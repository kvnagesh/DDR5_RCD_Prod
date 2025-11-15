// =====================================================================
// Parity Check Module for RCD Bus Signals
// =====================================================================
// Description: Implements even/odd parity checking for all bus signals
//              with error detection and reporting capabilities.
//              Supports multiple bus widths and simultaneous checking.
//
// Author: Signal Integrity Module
// Date: 2025-11-04
// =====================================================================

module parity_check #(
  parameter int DWIDTH = 64,           
  parameter int NUM_BUSES = 4,         
  parameter string PARITY_TYPE = "EVEN" // "EVEN" or "ODD"
) (
  input  logic                clk,
  input  logic                rst_n,
  input  logic                en,
  
  // Data Buses with Parity Bits
  input  logic [DWIDTH:0]     bus_in [NUM_BUSES],  
  
  // Parity Check Results
  output logic                parity_err [NUM_BUSES],     
  output logic [NUM_BUSES-1:0] parity_err_vector,         
  output logic                any_parity_err,              
  
  // Error Reporting
  output logic [7:0]          error_bus_id,                
  output logic [15:0]         parity_err_count,            
  output logic                parity_err_valid,            
  
  // Configuration
  input  logic                cfg_parity_type,             
  input  logic                cfg_err_report_en            // Enable error reporting
);

  // ===================================================================
  // Parity Calculation and Checking Logic
  // ===================================================================
  logic [NUM_BUSES-1:0] parity_calc;
  logic [NUM_BUSES-1:0] parity_received;
  logic [NUM_BUSES-1:0] parity_check_result;
  
  // Generate parity check for each bus
  genvar i, j;
  generate
    for (i = 0; i < NUM_BUSES; i = i + 1) begin : gen_parity_check
      // Extract parity bit (MSB)
      assign parity_received[i] = bus_in[i][DWIDTH];
      
      // Calculate XOR of all data bits
      logic calc_parity;
      always_comb begin
        calc_parity = 1'b0;
        for (j = 0; j < DWIDTH; j = j + 1) begin
          calc_parity = calc_parity ^ bus_in[i][j];
        end
      end
      
      assign parity_calc[i] = calc_parity;
      
      // Determine parity error based on EVEN/ODD configuration
      always_comb begin
        if (cfg_parity_type == 1'b0) begin
          // EVEN parity: calc_parity ^ received_parity should be 0
          parity_check_result[i] = parity_calc[i] ^ parity_received[i];
        end else begin
          // ODD parity: calc_parity ^ received_parity should be 1
          parity_check_result[i] = ~(parity_calc[i] ^ parity_received[i]);
        end
      end
      
      assign parity_err[i] = parity_check_result[i];
    end
  endgenerate
  
  // ===================================================================
  // Combined Error Signals
  // ===================================================================
  always_comb begin
    parity_err_vector = parity_check_result;
    any_parity_err = |parity_check_result;
  end
  
  // ===================================================================
  // First Error Priority Encoder
  // ===================================================================
  always_comb begin
    error_bus_id = 8'h00;
    for (int k = 0; k < NUM_BUSES; k = k + 1) begin
      if (parity_check_result[k]) begin
        error_bus_id = k;
        break;
      end
    end
  end
  
  // ===================================================================
  // Error Counter and Reporting
  // ===================================================================
  logic [15:0] error_counter;
  logic parity_error_detected;
  
  assign parity_error_detected = any_parity_err && cfg_err_report_en;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      error_counter <= 16'h0000;
      parity_err_valid <= 1'b0;
    end else if (en) begin
      if (parity_error_detected) begin
        error_counter <= error_counter + 1;
        parity_err_valid <= 1'b1;
      end else begin
        parity_err_valid <= 1'b0;
      end
    end
  end
  
  assign parity_err_count = error_counter;

endmodule

// =====================================================================
// Multi-Bus Parity Generator
// =====================================================================
module parity_gen #(
  parameter int DWIDTH = 64,
  parameter string PARITY_TYPE = "EVEN"
) (
  input  logic [DWIDTH-1:0]  data_in,
  output logic               parity_out
);

  logic calc_parity;
  
  always_comb begin
    calc_parity = ^data_in; // Calculate parity
    
    if (PARITY_TYPE == "EVEN") begin
      parity_out = calc_parity;  // Even parity
    end else begin
      parity_out = ~calc_parity; // Odd parity
    end
  end

endmodule

// =====================================================================
// Parity Monitor - Continuous Monitoring with Statistics
// =====================================================================
module parity_monitor #(
  parameter int DWIDTH = 64,
  parameter int NUM_MONITORS = 8
) (
  input  logic                     clk,
  input  logic                     rst_n,
  input  logic [DWIDTH:0]          bus_data [NUM_MONITORS],
  input  logic                     cfg_parity_type,
  input  logic                     monitor_en,
  
  output logic [NUM_MONITORS-1:0]  error_flags,
  output logic [31:0]              total_errors,
  output logic [7:0]               error_rate,     
  output logic                     monitor_active
);

  logic [NUM_MONITORS-1:0] error_detected;
  logic [31:0] error_count;
  logic [7:0] cycle_count;
  logic [7:0] cycle_errors;
  
  generate
    genvar m;
    for (m = 0; m < NUM_MONITORS; m = m + 1) begin : gen_monitor
      logic parity_calc, parity_recv;
      
      always_comb begin
        parity_recv = bus_data[m][DWIDTH];
        parity_calc = ^bus_data[m][DWIDTH-1:0];
        
        if (cfg_parity_type == 1'b0) begin
          error_detected[m] = parity_calc ^ parity_recv;
        end else begin
          error_detected[m] = ~(parity_calc ^ parity_recv);
        end
      end
    end
  endgenerate
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      error_count <= 32'h00000000;
      cycle_count <= 8'h00;
      cycle_errors <= 8'h00;
      monitor_active <= 1'b0;
    end else if (monitor_en) begin
      monitor_active <= 1'b1;
      
      // Count total errors
      error_count <= error_count + (|error_detected ? 1 : 0);
      
      // Track error rate (per 256 cycles)
      cycle_count <= cycle_count + 1;
      if (|error_detected) begin
        cycle_errors <= cycle_errors + 1;
      end
      
      if (cycle_count == 8'hFF) begin
        cycle_count <= 8'h00;
        cycle_errors <= 8'h00;
      end
    end else begin
      monitor_active <= 1'b0;
    end
  end
  
  assign error_flags = error_detected;
  assign total_errors = error_count;
  assign error_rate = cycle_errors;

endmodule

// =====================================================================
// END OF MODULE
// =====================================================================
