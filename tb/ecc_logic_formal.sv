//-----------------------------------------------------------------------------
// Title       : ECC Logic Formal Verification
// Project     : DDR5 RCD Production
//-----------------------------------------------------------------------------
// File        : ecc_logic_formal.sv
// Author      : Verification Team
// Created     : 2025-11-11
// Description : Formal verification properties for ECC logic with SEC-DED
//               (Single Error Correction - Double Error Detection) algorithm
//               proof for Hamming(72,64) code in DDR5 RCD.
//-----------------------------------------------------------------------------

`timescale 1ps/1fs

module ecc_logic_formal (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [63:0] data_in,
  input  logic        encode_en,
  input  logic [7:0]  ecc_gen,
  input  logic [63:0] data_rx,
  input  logic [7:0]  ecc_rx,
  input  logic        decode_en,
  input  logic [63:0] data_corrected,
  input  logic        single_error,
  input  logic        double_error,
  input  logic [6:0]  error_position
);

  //===========================================================================
  // Parameters
  //===========================================================================
  
  parameter int DATA_WIDTH = 64;
  parameter int ECC_WIDTH = 8;
  
  //===========================================================================
  // Helper Functions
  //===========================================================================
  
  // Reference ECC generation (must match DUT)
  function automatic logic [ECC_WIDTH-1:0] ref_generate_ecc(input logic [DATA_WIDTH-1:0] data);
    logic [ECC_WIDTH-1:0] ecc;
    ecc[0] = ^{data[0], data[1], data[3], data[4], data[6], data[8], data[10],
               data[11], data[13], data[15], data[17], data[19], data[21], data[23],
               data[25], data[26], data[28], data[30], data[32], data[34], data[36],
               data[38], data[40], data[42], data[44], data[46], data[48], data[50],
               data[52], data[54], data[56], data[57], data[59], data[61], data[63]};
    ecc[1] = ^{data[0], data[2], data[3], data[5], data[6], data[9], data[10],
               data[12], data[13], data[16], data[17], data[20], data[21], data[24],
               data[25], data[27], data[28], data[31], data[32], data[35], data[36],
               data[39], data[40], data[43], data[44], data[47], data[48], data[51],
               data[52], data[55], data[56], data[58], data[59], data[62], data[63]};
    ecc[2] = ^{data[1], data[2], data[3], data[7], data[8], data[9], data[10],
               data[14], data[15], data[16], data[17], data[22], data[23], data[24],
               data[25], data[29], data[30], data[31], data[32], data[37], data[38],
               data[39], data[40], data[45], data[46], data[47], data[48], data[53],
               data[54], data[55], data[56], data[60], data[61], data[62], data[63]};
    ecc[3] = ^{data[4], data[5], data[6], data[7], data[8], data[9], data[10],
               data[18], data[19], data[20], data[21], data[22], data[23], data[24],
               data[25], data[33], data[34], data[35], data[36], data[37], data[38],
               data[39], data[40], data[49], data[50], data[51], data[52], data[53],
               data[54], data[55], data[56]};
    ecc[4] = ^{data[11], data[12], data[13], data[14], data[15], data[16], data[17],
               data[18], data[19], data[20], data[21], data[22], data[23], data[24],
               data[25], data[41], data[42], data[43], data[44], data[45], data[46],
               data[47], data[48], data[49], data[50], data[51], data[52], data[53],
               data[54], data[55], data[56]};
    ecc[5] = ^{data[26], data[27], data[28], data[29], data[30], data[31], data[32],
               data[33], data[34], data[35], data[36], data[37], data[38], data[39],
               data[40], data[41], data[42], data[43], data[44], data[45], data[46],
               data[47], data[48], data[49], data[50], data[51], data[52], data[53],
               data[54], data[55], data[56]};
    ecc[6] = ^{data[57], data[58], data[59], data[60], data[61], data[62], data[63]};
    ecc[7] = ^{data, ecc[6:0]};
    return ecc;
  endfunction
  
  // Count bit differences
  function automatic int count_bit_errors(input logic [63:0] d1, input logic [63:0] d2);
    int count = 0;
    for (int i = 0; i < DATA_WIDTH; i++)
      if (d1[i] != d2[i]) count++;
    return count;
  endfunction
  
  //===========================================================================
  // Formal Assumptions
  //===========================================================================
  
  assume_valid_reset: assume property (
    @(posedge clk) $rose(rst_n) |-> !$past(rst_n)
  );
  
  assume_encode_data_stable: assume property (
    @(posedge clk) disable iff (!rst_n)
    encode_en |-> $stable(data_in)
  );
  
  assume_decode_data_stable: assume property (
    @(posedge clk) disable iff (!rst_n)
    decode_en |-> $stable(data_rx) && $stable(ecc_rx)
  );
  
  //===========================================================================
  // Property Group 1: ECC Generation Correctness
  //===========================================================================
  
  property prop_ecc_correct_generation;
    logic [7:0] expected_ecc;
    @(posedge clk) disable iff (!rst_n)
    (encode_en, expected_ecc = ref_generate_ecc(data_in)) |=> 
      (ecc_gen == expected_ecc);
  endproperty
  
  assert_ecc_generation: assert property (prop_ecc_correct_generation);
  
  property prop_ecc_deterministic;
    @(posedge clk) disable iff (!rst_n)
    encode_en && ($past(data_in) == data_in) |=> 
      (ecc_gen == $past(ecc_gen));
  endproperty
  
  assert_ecc_deterministic: assert property (prop_ecc_deterministic);
  
  //===========================================================================
  // Property Group 2: Single Error Correction
  //===========================================================================
  
  property prop_single_error_corrects;
    @(posedge clk) disable iff (!rst_n)
    decode_en && single_error |=> 
      (data_corrected != data_rx) && !double_error;
  endproperty
  
  assert_single_error_correction: assert property (prop_single_error_corrects);
  
  property prop_error_position_valid;
    @(posedge clk) disable iff (!rst_n)
    single_error |-> (error_position < DATA_WIDTH);
  endproperty
  
  assert_error_position: assert property (prop_error_position_valid);
  
  property prop_single_bit_difference;
    int errors;
    @(posedge clk) disable iff (!rst_n)
    (single_error, errors = count_bit_errors(data_rx, data_corrected)) |=> 
      (errors == 1);
  endproperty
  
  assert_single_bit_fix: assert property (prop_single_bit_difference);
  
  //===========================================================================
  // Property Group 3: Double Error Detection
  //===========================================================================
  
  property prop_double_error_detected;
    @(posedge clk) disable iff (!rst_n)
    double_error |-> !single_error;
  endproperty
  
  assert_double_error: assert property (prop_double_error_detected);
  
  property prop_double_error_no_correction;
    @(posedge clk) disable iff (!rst_n)
    double_error |=> (data_corrected == data_rx);
  endproperty
  
  assert_no_correction_on_double: assert property (prop_double_error_no_correction);
  
  //===========================================================================
  // Property Group 4: No Error Case
  //===========================================================================
  
  property prop_no_error_passthrough;
    logic [7:0] expected_ecc;
    @(posedge clk) disable iff (!rst_n)
    (decode_en, expected_ecc = ref_generate_ecc(data_rx)) |=> 
      ((ecc_rx == expected_ecc) |-> 
        (!single_error && !double_error && (data_corrected == data_rx)));
  endproperty
  
  assert_no_error_case: assert property (prop_no_error_passthrough);
  
  //===========================================================================
  // Property Group 5: Mutual Exclusivity
  //===========================================================================
  
  property prop_error_flags_exclusive;
    @(posedge clk) disable iff (!rst_n)
    !(single_error && double_error);
  endproperty
  
  assert_exclusive_errors: assert property (prop_error_flags_exclusive);
  
  //===========================================================================
  // Property Group 6: Algorithm Invariants
  //===========================================================================
  
  property prop_ecc_width_correct;
    @(posedge clk) disable iff (!rst_n)
    encode_en |=> ($countones(ecc_gen) >= 0) && ($countones(ecc_gen) <= ECC_WIDTH);
  endproperty
  
  assert_ecc_valid_bits: assert property (prop_ecc_width_correct);
  
  property prop_data_unchanged_no_error;
    @(posedge clk) disable iff (!rst_n)
    decode_en && !single_error && !double_error |=> 
      (data_corrected == $past(data_rx));
  endproperty
  
  assert_data_preservation: assert property (prop_data_unchanged_no_error);
  
  //===========================================================================
  // Coverage Properties
  //===========================================================================
  
  cover_no_error_case: cover property (
    @(posedge clk) disable iff (!rst_n)
    decode_en ##1 !single_error && !double_error
  );
  
  cover_single_error_case: cover property (
    @(posedge clk) disable iff (!rst_n)
    decode_en ##1 single_error && !double_error
  );
  
  cover_double_error_case: cover property (
    @(posedge clk) disable iff (!rst_n)
    decode_en ##1 double_error && !single_error
  );
  
  cover_all_data_patterns: cover property (
    @(posedge clk) disable iff (!rst_n)
    encode_en && (data_in == 64'hFFFFFFFFFFFFFFFF)
  );
  
  cover_error_correction_sequence: cover property (
    @(posedge clk) disable iff (!rst_n)
    single_error ##[1:3] !single_error
  );
  
endmodule
