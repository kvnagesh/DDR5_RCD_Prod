////////////////////////////////////////////////////////////////////////////////
// Module: error_thresh_mon.sv
// Description: Error threshold monitor module for system-level error management
//              Monitors error counts from all sources, compares to thresholds,
//              and issues system-level fail/warning flags
// Author: RTL Design
// Date: November 2025
////////////////////////////////////////////////////////////////////////////////

module error_thresh_mon #(
  parameter int NUM_ERROR_SOURCES = 8,  // Number of error monitoring channels
  parameter int COUNTER_WIDTH = 32,     // Width of error counters
  parameter int THRESHOLD_WIDTH = 16    // Threshold comparison width
)(
  input  logic                              clk,
  input  logic                              rst_n,
  input  logic                              enable,
  
  // Error input from multiple sources
  input  logic [NUM_ERROR_SOURCES-1:0]     error_valid,         // Error occurrence flags
  input  logic [NUM_ERROR_SOURCES-1:0]     error_severity,      // Severity: 0=Info, 1=Warning, 2=Error, 3=Fatal
  input  logic [COUNTER_WIDTH-1:0]         error_counts[NUM_ERROR_SOURCES],  // Per-source error counts
  
  // Threshold configuration (per source)
  input  logic [THRESHOLD_WIDTH-1:0]       warn_threshold[NUM_ERROR_SOURCES],
  input  logic [THRESHOLD_WIDTH-1:0]       fail_threshold[NUM_ERROR_SOURCES],
  input  logic                              threshold_load,      // Pulse to load thresholds
  
  // System-level status outputs
  output logic                              system_warning,      // System warning flag
  output logic                              system_fail,         // System fail flag (any channel exceeded fail threshold)
  output logic                              system_fatal,        // System fatal error flag
  
  // Per-source status
  output logic [NUM_ERROR_SOURCES-1:0]     source_warning,      // Warning per source
  output logic [NUM_ERROR_SOURCES-1:0]     source_fail,         // Fail per source
  output logic [NUM_ERROR_SOURCES-1:0]     source_fatal,        // Fatal per source
  
  // Aggregated statistics
  output logic [COUNTER_WIDTH-1:0]         total_errors,        // Total errors across all sources
  output logic [7:0]                       active_error_sources, // Number of sources with errors
  output logic [2:0]                       max_severity,        // Highest severity seen
  output logic [7:0]                       severity_histogram[0:3], // Count per severity level
  
  // Interrupt/Alert signals
  output logic                              error_interrupt,     // Pulse on new error
  output logic                              threshold_crossed,   // Pulse when threshold crossed
  output logic [NUM_ERROR_SOURCES-1:0]     interrupt_per_source
);

  // Internal registers and signals
  logic [COUNTER_WIDTH-1:0]                 local_counters[NUM_ERROR_SOURCES];
  logic [THRESHOLD_WIDTH-1:0]              local_warn_thresh[NUM_ERROR_SOURCES];
  logic [THRESHOLD_WIDTH-1:0]              local_fail_thresh[NUM_ERROR_SOURCES];
  logic [NUM_ERROR_SOURCES-1:0]            prev_error_valid;
  logic [NUM_ERROR_SOURCES-1:0]            source_warn_status;
  logic [NUM_ERROR_SOURCES-1:0]            source_fail_status;
  logic [NUM_ERROR_SOURCES-1:0]            source_fatal_status;
  logic [COUNTER_WIDTH-1:0]                 total_error_count;
  logic [7:0]                              source_counter;
  logic [2:0]                              highest_severity;
  logic [7:0]                              sev_histogram[0:3];
  logic [7:0]                              threshold_pulse_dly;
  logic [7:0]                              error_pulse_dly;
  logic                                    any_warn;
  logic                                    any_fail;
  logic                                    any_fatal;
  
  // Count active sources with errors
  function automatic logic [7:0] count_active_sources(
    logic [NUM_ERROR_SOURCES-1:0] flags
  );
    logic [7:0] count;
    count = 8'h0;
    for (int i = 0; i < NUM_ERROR_SOURCES; i++) begin
      if (flags[i]) count = count + 1;
    end
    return count;
  endfunction
  
  // Find maximum severity
  function automatic logic [2:0] find_max_severity(
    logic [NUM_ERROR_SOURCES-1:0] fatal,
    logic [NUM_ERROR_SOURCES-1:0] fail,
    logic [NUM_ERROR_SOURCES-1:0] warn
  );
    if (fatal != {NUM_ERROR_SOURCES{1'b0}}) return 3'h3; // Fatal
    if (fail != {NUM_ERROR_SOURCES{1'b0}})  return 3'h2; // Fail
    if (warn != {NUM_ERROR_SOURCES{1'b0}})  return 3'h1; // Warn
    return 3'h0; // No error
  endfunction
  
  // Threshold comparison for each source
  always_comb begin
    for (int i = 0; i < NUM_ERROR_SOURCES; i++) begin
      // Determine status based on error count vs thresholds
      if (error_counts[i] >= local_fail_thresh[i]) begin
        source_fatal_status[i] = error_severity[i];  // Mark fatal if severe
        source_fail_status[i] = 1'b1;
        source_warn_status[i] = 1'b1;
      end
      else if (error_counts[i] >= local_warn_thresh[i]) begin
        source_fatal_status[i] = 1'b0;
        source_fail_status[i] = 1'b0;
        source_warn_status[i] = 1'b1;
      end
      else begin
        source_fatal_status[i] = 1'b0;
        source_fail_status[i] = 1'b0;
        source_warn_status[i] = 1'b0;
      end
    end
  end
  
  // Update error counters and track history
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (int i = 0; i < NUM_ERROR_SOURCES; i++) begin
        local_counters[i] <= {COUNTER_WIDTH{1'b0}};
        local_warn_thresh[i] <= {{THRESHOLD_WIDTH-8{1'b0}}, 8'hFF};
        local_fail_thresh[i] <= {{THRESHOLD_WIDTH-8{1'b0}}, 8'h10};
      end
      total_error_count <= {COUNTER_WIDTH{1'b0}};
      prev_error_valid <= {NUM_ERROR_SOURCES{1'b0}};
      sev_histogram[0] <= 8'h0;
      sev_histogram[1] <= 8'h0;
      sev_histogram[2] <= 8'h0;
      sev_histogram[3] <= 8'h0;
    end
    else if (enable) begin
      // Load thresholds when requested
      if (threshold_load) begin
        for (int i = 0; i < NUM_ERROR_SOURCES; i++) begin
          local_warn_thresh[i] <= warn_threshold[i];
          local_fail_thresh[i] <= fail_threshold[i];
        end
      end
      
      // Update counters on new errors
      prev_error_valid <= error_valid;
      for (int i = 0; i < NUM_ERROR_SOURCES; i++) begin
        if (error_valid[i]) begin
          // Increment counter (prevent overflow)
          if (local_counters[i] != {COUNTER_WIDTH{1'b1}}) begin
            local_counters[i] <= local_counters[i] + 1;
          end
          
          // Increment total
          if (total_error_count != {COUNTER_WIDTH{1'b1}}) begin
            total_error_count <= total_error_count + 1;
          end
          
          // Update severity histogram
          case (error_severity[i])
            2'h0: sev_histogram[0] <= (sev_histogram[0] != 8'hFF) ? sev_histogram[0] + 1 : sev_histogram[0];
            2'h1: sev_histogram[1] <= (sev_histogram[1] != 8'hFF) ? sev_histogram[1] + 1 : sev_histogram[1];
            2'h2: sev_histogram[2] <= (sev_histogram[2] != 8'hFF) ? sev_histogram[2] + 1 : sev_histogram[2];
            2'h3: sev_histogram[3] <= (sev_histogram[3] != 8'hFF) ? sev_histogram[3] + 1 : sev_histogram[3];
          endcase
        end
      end
    end
  end
  
  // System-level status aggregation
  always_comb begin
    any_warn = (source_warn_status != {NUM_ERROR_SOURCES{1'b0}}) ? 1'b1 : 1'b0;
    any_fail = (source_fail_status != {NUM_ERROR_SOURCES{1'b0}}) ? 1'b1 : 1'b0;
    any_fatal = (source_fatal_status != {NUM_ERROR_SOURCES{1'b0}}) ? 1'b1 : 1'b0;
  end
  
  // Register system-level flags
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      system_warning <= 1'b0;
      system_fail <= 1'b0;
      system_fatal <= 1'b0;
    end
    else if (enable) begin
      system_warning <= any_warn;
      system_fail <= any_fail;
      system_fatal <= any_fatal;
    end
  end
  
  // Generate interrupt pulses (detect rising edge of errors)
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      error_pulse_dly <= 8'h00;
      threshold_pulse_dly <= 8'h00;
      interrupt_per_source <= {NUM_ERROR_SOURCES{1'b0}};
    end
    else if (enable) begin
      // Shift history for pulse generation
      error_pulse_dly <= {error_pulse_dly[6:0], (|error_valid)};
      threshold_pulse_dly <= {threshold_pulse_dly[6:0], (threshold_load)};
      
      // Per-source interrupt on rising edge
      for (int i = 0; i < NUM_ERROR_SOURCES; i++) begin
        interrupt_per_source[i] <= (error_valid[i] && ~prev_error_valid[i]) ? 1'b1 : 1'b0;
      end
    end
  end
  
  // Output assignments
  assign error_interrupt = error_pulse_dly[0] && ~error_pulse_dly[1]; // Rising edge detect
  assign threshold_crossed = threshold_pulse_dly[0] && ~threshold_pulse_dly[1];
  assign source_warning = source_warn_status;
  assign source_fail = source_fail_status;
  assign source_fatal = source_fatal_status;
  assign total_errors = total_error_count;
  assign active_error_sources = count_active_sources(source_fail_status | source_warn_status);
  assign max_severity = find_max_severity(source_fatal_status, source_fail_status, source_warn_status);
  assign severity_histogram[0] = sev_histogram[0];
  assign severity_histogram[1] = sev_histogram[1];
  assign severity_histogram[2] = sev_histogram[2];
  assign severity_histogram[3] = sev_histogram[3];

endmodule
