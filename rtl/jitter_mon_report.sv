//==============================================================================
// Module: jitter_mon_report.sv
// Description: Synthesizable hardware module for on-chip jitter measurement
//              and real-time reporting with handshake interface
// Author: Auto-generated for DDR5_RCD_Prod
// Date: 2025-11-04
//==============================================================================
//
// INTERFACE DESCRIPTION:
// -----------------------
// Clock and Reset:
//   - clk_ref      : Reference clock for timing measurements
//   - clk_target   : Target clock to monitor (DCK or other clock)
//   - rst_n        : Active-low asynchronous reset
//
// Configuration:
//   - cfg_enable   : Enable jitter monitoring
//   - cfg_window   : Measurement window size (2^cfg_window samples)
//   - cfg_threshold: Jitter threshold for error flagging (in ps)
//
// Status Outputs (Handshake Interface):
//   - report_valid : Indicates valid measurement data available
//   - report_ready : Downstream ready to accept report
//   - jitter_min   : Minimum measured jitter (cycle-to-cycle)
//   - jitter_max   : Maximum measured jitter
//   - jitter_avg   : Average jitter over measurement window
//   - error_count  : Number of measurements exceeding threshold
//   - sample_count : Total number of samples in current window
//
// MEASUREMENT TECHNIQUE:
// ----------------------
// 1. Time-to-Digital Conversion (TDC):
//    - Uses reference clock (clk_ref) as time base
//    - Captures target clock (clk_target) edges with synchronizer
//    - Measures interval between consecutive target clock edges
//
// 2. Cycle-to-Cycle Jitter Calculation:
//    - Measures period of each target clock cycle
//    - Calculates delta between consecutive periods
//    - Jitter = abs(Period[n] - Period[n-1])
//
// 3. Statistical Accumulation:
//    - Tracks min/max jitter values
//    - Accumulates sum for average calculation
//    - Counts threshold violations
//
// REPORTING FORMAT:
// -----------------
// All jitter measurements reported in picoseconds (ps)
// Report updates every 2^cfg_window samples via handshake protocol
// Measurements reset after successful handshake
//
//==============================================================================

module jitter_mon_report #(
  parameter int REF_CLK_FREQ_MHZ = 400,    // Reference clock frequency
  parameter int TGT_CLK_FREQ_MHZ = 2400,   // Target clock nominal frequency
  parameter int COUNTER_WIDTH    = 16,     // Width of timing counters
  parameter int JITTER_WIDTH     = 16,     // Width of jitter measurements
  parameter int WINDOW_WIDTH     = 8,      // Width of window size config
  parameter int SAMPLE_CNT_WIDTH = 16      // Width of sample counter
) (
  // Clock and Reset
  input  logic                       clk_ref,
  input  logic                       clk_target,
  input  logic                       rst_n,

  // Configuration Interface
  input  logic                       cfg_enable,
  input  logic [WINDOW_WIDTH-1:0]    cfg_window,
  input  logic [JITTER_WIDTH-1:0]    cfg_threshold,

  // Status Report Interface (Handshake)
  output logic                       report_valid,
  input  logic                       report_ready,
  output logic [JITTER_WIDTH-1:0]    jitter_min,
  output logic [JITTER_WIDTH-1:0]    jitter_max,
  output logic [JITTER_WIDTH-1:0]    jitter_avg,
  output logic [SAMPLE_CNT_WIDTH-1:0] error_count,
  output logic [SAMPLE_CNT_WIDTH-1:0] sample_count
);

  //============================================================================
  // Local Parameters
  //============================================================================
  localparam int PS_PER_REF_CLK = (1000000 / REF_CLK_FREQ_MHZ); // ps per ref cycle
  localparam int NOMINAL_PERIOD = (1000000 / TGT_CLK_FREQ_MHZ); // nominal target period in ps

  //============================================================================
  // Internal Signals
  //============================================================================

  // Target clock edge detection
  logic [2:0]                 target_sync;
  logic                       target_edge;
  logic                       target_prev;

  // Period measurement
  logic [COUNTER_WIDTH-1:0]   period_counter;
  logic [COUNTER_WIDTH-1:0]   period_captured;
  logic [COUNTER_WIDTH-1:0]   period_prev;
  logic                       period_valid;

  // Jitter calculation
  logic signed [COUNTER_WIDTH:0] period_delta;
  logic [JITTER_WIDTH-1:0]    jitter_current;
  logic                       jitter_valid;

  // Statistical accumulators
  logic [JITTER_WIDTH-1:0]    jitter_min_reg;
  logic [JITTER_WIDTH-1:0]    jitter_max_reg;
  logic [JITTER_WIDTH+SAMPLE_CNT_WIDTH-1:0] jitter_sum;
  logic [SAMPLE_CNT_WIDTH-1:0] error_count_reg;
  logic [SAMPLE_CNT_WIDTH-1:0] sample_count_reg;

  // Window control
  logic [SAMPLE_CNT_WIDTH-1:0] window_size;
  logic                       window_complete;

  // Report generation
  logic [JITTER_WIDTH-1:0]    jitter_avg_calc;
  logic                       report_pending;

  //============================================================================
  // Target Clock Edge Detection (CDC-safe synchronizer)
  //============================================================================
  always_ff @(posedge clk_ref or negedge rst_n) begin
    if (!rst_n) begin
      target_sync <= 3'b000;
      target_prev <= 1'b0;
    end else begin
      // Three-stage synchronizer for CDC
      target_sync <= {target_sync[1:0], clk_target};
      target_prev <= target_sync[2];
    end
  end

  // Detect rising edge of synchronized target clock
  assign target_edge = target_sync[2] & ~target_prev;

  //============================================================================
  // Period Measurement Counter
  //============================================================================
  always_ff @(posedge clk_ref or negedge rst_n) begin
    if (!rst_n) begin
      period_counter  <= '0;
      period_captured <= '0;
      period_valid    <= 1'b0;
    end else if (!cfg_enable) begin
      period_counter  <= '0;
      period_captured <= '0;
      period_valid    <= 1'b0;
    end else begin
      if (target_edge) begin
        // Capture current count on target edge
        period_captured <= period_counter;
        period_counter  <= '0;
        period_valid    <= 1'b1;
      end else begin
        // Increment counter (saturate at max)
        if (period_counter != {COUNTER_WIDTH{1'b1}}) begin
          period_counter <= period_counter + 1'b1;
        end
        period_valid <= 1'b0;
      end
    end
  end

  //============================================================================
  // Cycle-to-Cycle Jitter Calculation
  //============================================================================
  always_ff @(posedge clk_ref or negedge rst_n) begin
    if (!rst_n) begin
      period_prev  <= '0;
      period_delta <= '0;
      jitter_current <= '0;
      jitter_valid   <= 1'b0;
    end else if (!cfg_enable) begin
      period_prev  <= '0;
      period_delta <= '0;
      jitter_current <= '0;
      jitter_valid   <= 1'b0;
    end else if (period_valid) begin
      // Store previous period
      period_prev <= period_captured;
      
      // Calculate signed difference
      period_delta <= $signed({1'b0, period_captured}) - $signed({1'b0, period_prev});
      
      // Take absolute value and convert to picoseconds
      if (period_prev != '0) begin // Skip first sample
        jitter_current <= (period_delta[COUNTER_WIDTH] ? 
                          (~period_delta[COUNTER_WIDTH-1:0] + 1'b1) : 
                          period_delta[COUNTER_WIDTH-1:0]) * PS_PER_REF_CLK;
        jitter_valid <= 1'b1;
      end else begin
        jitter_valid <= 1'b0;
      end
    end else begin
      jitter_valid <= 1'b0;
    end
  end

  //============================================================================
  // Window Size Calculation
  //============================================================================
  always_comb begin
    window_size = 1 << cfg_window; // 2^cfg_window
  end

  assign window_complete = (sample_count_reg >= window_size) && cfg_enable;

  //============================================================================
  // Statistical Accumulation
  //============================================================================
  always_ff @(posedge clk_ref or negedge rst_n) begin
    if (!rst_n) begin
      jitter_min_reg   <= {JITTER_WIDTH{1'b1}}; // Initialize to max
      jitter_max_reg   <= '0;
      jitter_sum       <= '0;
      error_count_reg  <= '0;
      sample_count_reg <= '0;
    end else if (!cfg_enable) begin
      jitter_min_reg   <= {JITTER_WIDTH{1'b1}};
      jitter_max_reg   <= '0;
      jitter_sum       <= '0;
      error_count_reg  <= '0;
      sample_count_reg <= '0;
    end else if (report_valid && report_ready) begin
      // Reset after successful handshake
      jitter_min_reg   <= {JITTER_WIDTH{1'b1}};
      jitter_max_reg   <= '0;
      jitter_sum       <= '0;
      error_count_reg  <= '0;
      sample_count_reg <= '0;
    end else if (jitter_valid && !window_complete) begin
      // Update statistics
      if (jitter_current < jitter_min_reg) begin
        jitter_min_reg <= jitter_current;
      end
      
      if (jitter_current > jitter_max_reg) begin
        jitter_max_reg <= jitter_current;
      end
      
      jitter_sum <= jitter_sum + jitter_current;
      
      if (jitter_current > cfg_threshold) begin
        error_count_reg <= error_count_reg + 1'b1;
      end
      
      sample_count_reg <= sample_count_reg + 1'b1;
    end
  end

  //============================================================================
  // Average Calculation
  //============================================================================
  always_comb begin
    if (sample_count_reg > 0) begin
      jitter_avg_calc = jitter_sum / sample_count_reg;
    end else begin
      jitter_avg_calc = '0;
    end
  end

  //============================================================================
  // Report Generation with Handshake
  //============================================================================
  always_ff @(posedge clk_ref or negedge rst_n) begin
    if (!rst_n) begin
      report_valid   <= 1'b0;
      report_pending <= 1'b0;
      jitter_min     <= '0;
      jitter_max     <= '0;
      jitter_avg     <= '0;
      error_count    <= '0;
      sample_count   <= '0;
    end else if (!cfg_enable) begin
      report_valid   <= 1'b0;
      report_pending <= 1'b0;
    end else begin
      // Generate report when window completes
      if (window_complete && !report_pending) begin
        report_valid   <= 1'b1;
        report_pending <= 1'b1;
        jitter_min     <= jitter_min_reg;
        jitter_max     <= jitter_max_reg;
        jitter_avg     <= jitter_avg_calc;
        error_count    <= error_count_reg;
        sample_count   <= sample_count_reg;
      end
      
      // Clear valid after handshake
      if (report_valid && report_ready) begin
        report_valid   <= 1'b0;
        report_pending <= 1'b0;
      end
    end
  end

  //============================================================================
  // Assertions for Verification
  //============================================================================
  `ifdef SIMULATION
    // Check that reference clock is faster than target clock
    initial begin
      assert (REF_CLK_FREQ_MHZ >= TGT_CLK_FREQ_MHZ * 4)
        else $warning("Reference clock should be at least 4x target clock for accurate measurement");
    end

    // Check for counter overflow
    property p_no_counter_overflow;
      @(posedge clk_ref) disable iff (!rst_n)
      (period_counter == {COUNTER_WIDTH{1'b1}}) |-> ##[1:10] target_edge;
    endproperty
    assert property (p_no_counter_overflow)
      else $error("Period counter overflow - increase COUNTER_WIDTH or REF_CLK_FREQ");

    // Check handshake protocol
    property p_valid_stable;
      @(posedge clk_ref) disable iff (!rst_n)
      (report_valid && !report_ready) |=> report_valid;
    endproperty
    assert property (p_valid_stable)
      else $error("report_valid must remain stable until report_ready");
  `endif

endmodule

//==============================================================================
// END OF FILE: jitter_mon_report.sv
//==============================================================================
