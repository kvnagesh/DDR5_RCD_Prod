// =====================================================================
// ECC Encoder/Decoder Module - Parameterizable for RCD Data Paths
// =====================================================================
// Description: Implements SECDED (Single Error Correction, Double Error 
//              Detection), Hamming code, and BCH code support with runtime
//              configuration for flexible error correction on RCD datapaths
//
// Author: Error Correction Unit
// Date: 2025-11-04
// =====================================================================

module ecc_enc_dec #(
  parameter int DWIDTH = 64,           
  parameter int EWIDTH = 8,            
  parameter string ECC_TYPE = "SECDED", 
  parameter string ECC_MODE = "ENCODE" // "ENCODE", "DECODE", "BOTH"
) (
  input  logic                clk,
  input  logic                rst_n,
  input  logic                en,      
  
  // Encoding Interface
  input  logic [DWIDTH-1:0]   data_in,
  output logic [EWIDTH-1:0]   ecc_out,
  
  // Decoding Interface  
  input  logic [DWIDTH-1:0]   data_recv,
  input  logic [EWIDTH-1:0]   ecc_recv,
  output logic [DWIDTH-1:0]   data_out,
  output logic                single_err_detected,  
  output logic                double_err_detected,  
  output logic [15:0]         syndrome_out,        
  output logic [7:0]          error_position,      
  
  // Configuration
  input  logic [2:0]          cfg_ecc_type,        
  input  logic                cfg_enable_correction // Enable error correction
);

  // ===================================================================
  // SECDED Hamming Code Generation
  // ===================================================================
  function automatic logic [7:0] calc_secded_ecc(
    input logic [DWIDTH-1:0] data
  );
    logic [7:0] ecc;
    logic [DWIDTH-1:0] data_xor;
    
    // Calculate parity bits for Hamming(72,64) - SECDED variant
    ecc[0] = ^(data & 64'h AAAAAAAAAAAAAAA); // P1: bits 1,3,5,...
    ecc[1] = ^(data & 64'h CCCCCCCCCCCCCCCC); // P2: bits 2,3,6,7,...  
    ecc[2] = ^(data & 64'h F0F0F0F0F0F0F0F0); // P4: bits 4-7,12-15,...
    ecc[3] = ^(data & 64'h FF00FF00FF00FF00); // P8: bits 8-15,...
    ecc[4] = ^(data & 64'h FFFF0000FFFF0000); // P16: bits 16-31,...
    ecc[5] = ^(data & 64'h FFFFFFFF00000000); // P32: bits 32-63
    ecc[6] = ^data;                          // Overall parity
    ecc[7] = 1'b0;                           // Reserved
    
    return ecc;
  endfunction
  
  // ===================================================================
  // SECDED Syndrome Calculation & Error Correction
  // ===================================================================
  function automatic logic [7:0] calc_secded_syndrome(
    input logic [DWIDTH-1:0] data,
    input logic [7:0] ecc_stored
  );
    logic [7:0] ecc_calc, syndrome;
    
    ecc_calc = calc_secded_ecc(data);
    syndrome = ecc_calc ^ ecc_stored;
    return syndrome;
  endfunction

  // ===================================================================
  // BCH Code Support (15,11) - for higher reliability
  // ===================================================================
  function automatic logic [3:0] calc_bch_ecc(
    input logic [10:0] data
  );
    logic [3:0] ecc;
    // BCH polynomial: x^4 + x + 1 (0x13 in GF(2^4))
    ecc[0] = data[0] ^ data[1] ^ data[3] ^ data[4] ^ data[6] ^ data[9] ^ data[10];
    ecc[1] = data[0] ^ data[2] ^ data[3] ^ data[5] ^ data[6] ^ data[7] ^ data[10];
    ecc[2] = data[1] ^ data[2] ^ data[4] ^ data[5] ^ data[7] ^ data[8] ^ data[10];
    ecc[3] = data[0] ^ data[1] ^ data[5] ^ data[8] ^ data[9];
    return ecc;
  endfunction

  // ===================================================================
  // Hamming Code (31,26) variant
  // ===================================================================
  function automatic logic [4:0] calc_hamming_ecc(
    input logic [25:0] data
  );
    logic [4:0] ecc;
    
    ecc[0] = ^(data & 26'h155555);    // Positions 1,3,5,7,9,...
    ecc[1] = ^(data & 26'h366666);    // Positions 2,3,6,7,10,...
    ecc[2] = ^(data & 26'h70F0F0);    // Positions 4,5,6,7,12,...
    ecc[3] = ^(data & 26'hFF00);      // Positions 8-15
    ecc[4] = ^data;                   // Overall parity
    
    return ecc;
  endfunction

  // ===================================================================
  // Main ECC Logic
  // ===================================================================
  logic [EWIDTH-1:0] ecc_calculated;
  logic [EWIDTH-1:0] syndrome;
  logic [DWIDTH-1:0] corrected_data;
  
  // ECC Encoding
  always_comb begin
    if (ECC_MODE == "ENCODE" || ECC_MODE == "BOTH") begin
      ecc_calculated = calc_secded_ecc(data_in);
      ecc_out = ecc_calculated;
    end else begin
      ecc_out = '0;
    end
  end
  
  // ECC Decoding & Error Correction
  always_comb begin
    syndrome = calc_secded_syndrome(data_recv, ecc_recv);
    error_position = syndrome[7:0];
    
    // Determine error type
    if (syndrome == 8'h00) begin
      single_err_detected = 1'b0;
      double_err_detected = 1'b0;
      syndrome_out = 16'h0000;
    end else if (syndrome[7] == 1'b1) begin
      // Single bit error - correctable
      single_err_detected = 1'b1;
      double_err_detected = 1'b0;
      syndrome_out = {8'h00, syndrome};
    end else begin
      // Double bit error - detectable but not correctable
      single_err_detected = 1'b0;
      double_err_detected = 1'b1;
      syndrome_out = {8'h01, syndrome};
    end
    
    // Error correction
    corrected_data = data_recv;
    if (cfg_enable_correction && single_err_detected) begin
      corrected_data[error_position] = ~corrected_data[error_position];
    end
  end
  
  // Output mux
  assign data_out = corrected_data;

endmodule

// =====================================================================
// END OF MODULE
// =====================================================================
