////////////////////////////////////////////////////////////////////////////////
// Module: ecc_err_type_ctrl.sv
// Description: Logic for distinguishing and reporting correctable vs 
//              uncorrectable errors, with metadata and error severity output
// Author: RTL Design
// Date: November 2025
////////////////////////////////////////////////////////////////////////////////

module ecc_err_type_ctrl #(
  parameter int DATA_WIDTH = 128,       // Data width for error detection
  parameter int ECC_WIDTH = 16,         // ECC syndrome width (Hamming)
  parameter int HISTORY_DEPTH = 32      // Error history log depth
)(
  input  logic                        clk,
  input  logic                        rst_n,
  
  // Data and control inputs
  input  logic [DATA_WIDTH-1:0]        data_in,
  input  logic [ECC_WIDTH-1:0]         ecc_syndrome,
  input  logic                        ecc_valid,
  input  logic                        enable,
  
  // Error detection outputs
  output logic                        error_detected,
  output logic                        is_correctable,
  output logic                        is_uncorrectable,
  
  // Error metadata
  output logic [7:0]                  error_bit_pos,      // Position of error bit(s)
  output logic [3:0]                  error_count,        // Number of error bits
  output logic [2:0]                  error_severity,     // 0=None, 1=Info, 2=Warning, 3=Severe, 4=Fatal
  output logic [31:0]                 error_info,         // Packed error information
  
  // Corrected data output
  output logic [DATA_WIDTH-1:0]        data_corrected,
  output logic                        correction_done,
  
  // History and statistics
  output logic [7:0]                  correctable_errors,
  output logic [7:0]                  uncorrectable_errors,
  output logic [15:0]                 total_error_events
);

  // Internal registers
  logic [DATA_WIDTH-1:0]              data_reg;
  logic [ECC_WIDTH-1:0]               syndrome_reg;
  logic [7:0]                         error_history [0:HISTORY_DEPTH-1];
  logic [7:0]                         corr_err_count;
  logic [7:0]                         uncorr_err_count;
  logic [15:0]                        total_events;
  logic [6:0]                         history_ptr;
  logic [3:0]                         error_bit_count;
  logic                               is_single_bit;
  logic                               is_multi_bit;
  logic [7:0]                         bit_position;
  
  // Parity generation function
  function automatic logic calc_parity(logic [DATA_WIDTH-1:0] data);
    logic parity;
    parity = 1'b0;
    for (int i = 0; i < DATA_WIDTH; i++) begin
      parity ^= data[i];
    end
    return parity;
  endfunction
  
  // Count set bits function
  function automatic logic [3:0] count_bits(logic [ECC_WIDTH-1:0] syndrome);
    logic [3:0] count;
    count = 4'h0;
    for (int i = 0; i < ECC_WIDTH; i++) begin
      if (syndrome[i]) count = count + 1;
    end
    return count;
  endfunction
  
  // Find first set bit position
  function automatic logic [7:0] find_error_pos(logic [ECC_WIDTH-1:0] syndrome);
    logic [7:0] pos;
    pos = 8'h00;
    for (int i = 0; i < ECC_WIDTH; i++) begin
      if (syndrome[i]) begin
        pos = i;
        break;
      end
    end
    return pos;
  endfunction
  
  // ECC error detection and classification
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_reg <= {DATA_WIDTH{1'b0}};
      syndrome_reg <= {ECC_WIDTH{1'b0}};
      error_detected <= 1'b0;
      is_correctable <= 1'b0;
      is_uncorrectable <= 1'b0;
      error_bit_count <= 4'h0;
      is_single_bit <= 1'b0;
      is_multi_bit <= 1'b0;
      bit_position <= 8'h00;
    end
    else if (enable && ecc_valid) begin
      data_reg <= data_in;
      syndrome_reg <= ecc_syndrome;
      
      // Count error bits
      error_bit_count <= count_bits(ecc_syndrome);
      
      // Detect error type
      if (ecc_syndrome == {ECC_WIDTH{1'b0}}) begin
        // No error
        error_detected <= 1'b0;
        is_correctable <= 1'b0;
        is_uncorrectable <= 1'b0;
        is_single_bit <= 1'b0;
        is_multi_bit <= 1'b0;
      end
      else if (count_bits(ecc_syndrome) == 4'h1) begin
        // Single-bit error (correctable)
        error_detected <= 1'b1;
        is_correctable <= 1'b1;
        is_uncorrectable <= 1'b0;
        is_single_bit <= 1'b1;
        is_multi_bit <= 1'b0;
        bit_position <= find_error_pos(ecc_syndrome);
      end
      else begin
        // Multi-bit error (uncorrectable)
        error_detected <= 1'b1;
        is_correctable <= 1'b0;
        is_uncorrectable <= 1'b1;
        is_single_bit <= 1'b0;
        is_multi_bit <= 1'b1;
        bit_position <= 8'hFF; // Mark as multi-bit
      end
    end
    else begin
      error_detected <= 1'b0;
      is_correctable <= 1'b0;
      is_uncorrectable <= 1'b0;
    end
  end
  
  // Error correction logic
  always_comb begin
    data_corrected = data_reg;
    correction_done = 1'b0;
    
    if (error_detected && is_single_bit && is_correctable) begin
      // Single-bit error correction using Hamming code
      if (bit_position < DATA_WIDTH) begin
        data_corrected[bit_position] = ~data_reg[bit_position];
      end
      correction_done = 1'b1;
    end
    else if (error_detected && is_multi_bit) begin
      // Cannot correct multi-bit error
      correction_done = 1'b0;
    end
  end
  
  // Error severity assignment
  always_comb begin
    case ({error_detected, is_correctable, is_uncorrectable})
      3'b000: error_severity = 3'h0; // No error
      3'b110: begin                   // Correctable error
        if (error_bit_count == 4'h1) 
          error_severity = 3'h1;      // Info/Warning
        else
          error_severity = 3'h2;      // Warning
      end
      3'b101: error_severity = 3'h4;  // Uncorrectable - Fatal
      default: error_severity = 3'h0;
    endcase
  end
  
  // Error information packing
  assign error_info = {
    error_detected,      // [31]
    is_correctable,      // [30]
    is_uncorrectable,    // [29]
    error_severity[2:0], // [28:26]
    error_bit_count,     // [25:22]
    bit_position[7:0]    // [21:14]
  };
  
  // Update counters
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      corr_err_count <= 8'h00;
      uncorr_err_count <= 8'h00;
      total_events <= 16'h0000;
      history_ptr <= 7'h00;
    end
    else if (enable && error_detected) begin
      // Update counters
      if (is_correctable) begin
        corr_err_count <= (corr_err_count == 8'hFF) ? corr_err_count : corr_err_count + 1;
      end
      else if (is_uncorrectable) begin
        uncorr_err_count <= (uncorr_err_count == 8'hFF) ? uncorr_err_count : uncorr_err_count + 1;
      end
      
      // Increment total events
      total_events <= (total_events == 16'hFFFF) ? total_events : total_events + 1;
      
      // Store in history (circular buffer)
      error_history[history_ptr] <= {
        is_uncorrectable,
        is_correctable,
        error_severity,
        error_bit_count[3:0]
      };
      history_ptr <= (history_ptr == HISTORY_DEPTH - 1) ? 7'h00 : history_ptr + 1;
    end
  end
  
  // Output assignments
  assign correctable_errors = corr_err_count;
  assign uncorrectable_errors = uncorr_err_count;
  assign total_error_events = total_events;
  assign error_bit_pos = bit_position;
  assign error_count = error_bit_count;

endmodule
