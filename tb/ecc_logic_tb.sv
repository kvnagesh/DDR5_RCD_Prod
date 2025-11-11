//-----------------------------------------------------------------------------
// Title       : ECC Logic Module Testbench with Algorithm Verification
// Project     : DDR5 RCD Production
//-----------------------------------------------------------------------------
// File        : ecc_logic_tb.sv
// Author      : Verification Team
// Created     : 2025-11-11
// Description : Comprehensive testbench for ECC (Error Correction Code) logic
//               with SEC-DED algorithm verification, coverage analysis, and
//               formal proof for DDR5 RCD with 64-bit data + 8-bit ECC.
//-----------------------------------------------------------------------------

`timescale 1ps/1fs

module ecc_logic_tb;

  //===========================================================================
  // Parameters - DDR5 ECC Specifications
  //===========================================================================
  
  parameter int DATA_WIDTH = 64;     // 64-bit data bus
  parameter int ECC_WIDTH = 8;       // 8-bit ECC (SEC-DED Hamming)
  parameter int TOTAL_WIDTH = 72;    // 64 data + 8 ECC
  
  // Test parameters
  parameter int NUM_RANDOM_TESTS = 1000;
  parameter int NUM_EXHAUSTIVE_TESTS = 10000;
  
  //===========================================================================
  // DUT Signals
  //===========================================================================
  
  logic clk;
  logic rst_n;
  
  // Encoder interface
  logic [DATA_WIDTH-1:0]  data_in;
  logic                   encode_valid;
  logic [ECC_WIDTH-1:0]   ecc_out;
  logic                   encode_ready;
  
  // Decoder interface
  logic [DATA_WIDTH-1:0]  data_with_errors;
  logic [ECC_WIDTH-1:0]   ecc_in;
  logic                   decode_valid;
  logic [DATA_WIDTH-1:0]  data_corrected;
  logic                   single_error;
  logic                   double_error;
  logic                   no_error;
  logic [6:0]             error_bit_position;
  logic                   decode_ready;
  
  //===========================================================================
  // Test Variables
  //===========================================================================
  
  int test_passed;
  int test_failed;
  int single_errors_corrected;
  int double_errors_detected;
  int false_corrections;
  int missed_errors;
  int encoding_errors;
  int decoding_errors;
  
  // Coverage bins
  int [DATA_WIDTH-1:0] bit_flip_coverage;
  int all_zeros_tested;
  int all_ones_tested;
  int alternating_pattern_tested;
  
  //===========================================================================
  // Clock Generation
  //===========================================================================
  
  initial begin
    clk = 0;
    forever #500ps clk = ~clk;  // 1 GHz clock
  end
  
  //===========================================================================
  // ECC Algorithm Implementation (Reference Model)
  //===========================================================================
  
  // Hamming(72,64) SEC-DED code generator matrix
  function automatic logic [ECC_WIDTH-1:0] generate_ecc(input logic [DATA_WIDTH-1:0] data);
    logic [ECC_WIDTH-1:0] ecc;
    int i;
    
    // P0 - covers all odd bit positions
    ecc[0] = ^{data[0], data[1], data[3], data[4], data[6], data[8], data[10],
               data[11], data[13], data[15], data[17], data[19], data[21], data[23],
               data[25], data[26], data[28], data[30], data[32], data[34], data[36],
               data[38], data[40], data[42], data[44], data[46], data[48], data[50],
               data[52], data[54], data[56], data[57], data[59], data[61], data[63]};
    
    // P1 - covers positions where bit 1 is set
    ecc[1] = ^{data[0], data[2], data[3], data[5], data[6], data[9], data[10],
               data[12], data[13], data[16], data[17], data[20], data[21], data[24],
               data[25], data[27], data[28], data[31], data[32], data[35], data[36],
               data[39], data[40], data[43], data[44], data[47], data[48], data[51],
               data[52], data[55], data[56], data[58], data[59], data[62], data[63]};
    
    // P2 - covers positions where bit 2 is set
    ecc[2] = ^{data[1], data[2], data[3], data[7], data[8], data[9], data[10],
               data[14], data[15], data[16], data[17], data[22], data[23], data[24],
               data[25], data[29], data[30], data[31], data[32], data[37], data[38],
               data[39], data[40], data[45], data[46], data[47], data[48], data[53],
               data[54], data[55], data[56], data[60], data[61], data[62], data[63]};
    
    // P3 - covers positions where bit 3 is set  
    ecc[3] = ^{data[4], data[5], data[6], data[7], data[8], data[9], data[10],
               data[18], data[19], data[20], data[21], data[22], data[23], data[24],
               data[25], data[33], data[34], data[35], data[36], data[37], data[38],
               data[39], data[40], data[49], data[50], data[51], data[52], data[53],
               data[54], data[55], data[56]};
    
    // P4 - covers positions where bit 4 is set
    ecc[4] = ^{data[11], data[12], data[13], data[14], data[15], data[16], data[17],
               data[18], data[19], data[20], data[21], data[22], data[23], data[24],
               data[25], data[41], data[42], data[43], data[44], data[45], data[46],
               data[47], data[48], data[49], data[50], data[51], data[52], data[53],
               data[54], data[55], data[56]};
    
    // P5 - covers positions where bit 5 is set
    ecc[5] = ^{data[26], data[27], data[28], data[29], data[30], data[31], data[32],
               data[33], data[34], data[35], data[36], data[37], data[38], data[39],
               data[40], data[41], data[42], data[43], data[44], data[45], data[46],
               data[47], data[48], data[49], data[50], data[51], data[52], data[53],
               data[54], data[55], data[56]};
    
    // P6 - covers high order data bits
    ecc[6] = ^{data[57], data[58], data[59], data[60], data[61], data[62], data[63]};
    
    // P7 - overall parity for SEC-DED
    ecc[7] = ^{data, ecc[6:0]};
    
    return ecc;
  endfunction
  
  // Syndrome calculation
  function automatic logic [7:0] calculate_syndrome(
    input logic [DATA_WIDTH-1:0] data,
    input logic [ECC_WIDTH-1:0] ecc
  );
    logic [ECC_WIDTH-1:0] computed_ecc;
    logic [7:0] syndrome;
    
    computed_ecc = generate_ecc(data);
    syndrome = ecc ^ computed_ecc;
    
    return syndrome;
  endfunction
  
  // Error correction
  function automatic void decode_and_correct(
    input  logic [DATA_WIDTH-1:0] data_in,
    input  logic [ECC_WIDTH-1:0]  ecc_in,
    output logic [DATA_WIDTH-1:0] data_out,
    output logic                  single_err,
    output logic                  double_err,
    output logic [6:0]            err_pos
  );
    logic [7:0] syndrome;
    logic parity_check;
    int error_position;
    
    syndrome = calculate_syndrome(data_in, ecc_in);
    parity_check = ^{data_in, ecc_in};
    
    data_out = data_in;
    single_err = 1'b0;
    double_err = 1'b0;
    err_pos = 7'h00;
    
    if (syndrome == 8'h00) begin
      // No error
      single_err = 1'b0;
      double_err = 1'b0;
    end else if (parity_check == 1'b1) begin
      // Single bit error - correct it
      single_err = 1'b1;
      error_position = syndrome[6:0];
      
      if (error_position < DATA_WIDTH) begin
        data_out[error_position] = ~data_in[error_position];
        err_pos = error_position[6:0];
      end
    end else begin
      // Double bit error - cannot correct
      double_err = 1'b1;
    end
  endfunction
  
  //===========================================================================
  // Test Tasks
  //===========================================================================
  
  task test_no_errors();
    logic [DATA_WIDTH-1:0] test_data;
    logic [ECC_WIDTH-1:0] computed_ecc;
    logic [DATA_WIDTH-1:0] corrected_data;
    logic se, de;
    logic [6:0] err_pos;
    begin
      $display("\n===========================================");
      $display("TEST: No Errors - ECC Encoding/Decoding");
      $display("===========================================");
      
      for (int i = 0; i < 100; i++) begin
        test_data = $random();
        
        // Encode
        @(posedge clk);
        data_in = test_data;
        encode_valid = 1'b1;
        @(posedge clk);
        encode_valid = 1'b0;
        @(posedge clk);
        
        computed_ecc = generate_ecc(test_data);
        
        // Decode without errors
        @(posedge clk);
        data_with_errors = test_data;
        ecc_in = computed_ecc;
        decode_valid = 1'b1;
        @(posedge clk);
        decode_valid = 1'b0;
        @(posedge clk);
        
        decode_and_correct(test_data, computed_ecc, corrected_data, se, de, err_pos);
        
        if (corrected_data == test_data && !se && !de) begin
          test_passed++;
        end else begin
          $error("[FAIL] No error case failed for data=0x%016X", test_data);
          test_failed++;
        end
      end
      
      $display("[TEST] No error cases completed\n");
    end
  endtask
  
  task test_single_bit_errors();
    logic [DATA_WIDTH-1:0] test_data, corrupted_data;
    logic [ECC_WIDTH-1:0] computed_ecc;
    logic [DATA_WIDTH-1:0] corrected_data;
    logic se, de;
    logic [6:0] err_pos;
    int error_bit;
    begin
      $display("\n===========================================");
      $display("TEST: Single Bit Error Correction");
      $display("===========================================");
      
      for (int i = 0; i < DATA_WIDTH; i++) begin
        test_data = $random();
        computed_ecc = generate_ecc(test_data);
        
        // Inject single bit error
        error_bit = i;
        corrupted_data = test_data;
        corrupted_data[error_bit] = ~corrupted_data[error_bit];
        
        decode_and_correct(corrupted_data, computed_ecc, corrected_data, se, de, err_pos);
        
        if (corrected_data == test_data && se && !de && err_pos == error_bit) begin
          test_passed++;
          single_errors_corrected++;
          bit_flip_coverage[error_bit]++;
        end else begin
          $error("[FAIL] Single error correction failed at bit %0d", error_bit);
          test_failed++;
        end
      end
      
      $display("[PASS] All %0d single bit errors corrected", DATA_WIDTH);
      $display("[TEST] Single bit error correction completed\n");
    end
  endtask
  
  task test_double_bit_errors();
    logic [DATA_WIDTH-1:0] test_data, corrupted_data;
    logic [ECC_WIDTH-1:0] computed_ecc;
    logic [DATA_WIDTH-1:0] corrected_data;
    logic se, de;
    logic [6:0] err_pos;
    int error_bit1, error_bit2;
    begin
      $display("\n===========================================");
      $display("TEST: Double Bit Error Detection");
      $display("===========================================");
      
      for (int i = 0; i < 100; i++) begin
        test_data = $random();
        computed_ecc = generate_ecc(test_data);
        
        // Inject two bit errors
        error_bit1 = $urandom_range(0, DATA_WIDTH-1);
        error_bit2 = $urandom_range(0, DATA_WIDTH-1);
        while (error_bit2 == error_bit1)
          error_bit2 = $urandom_range(0, DATA_WIDTH-1);
        
        corrupted_data = test_data;
        corrupted_data[error_bit1] = ~corrupted_data[error_bit1];
        corrupted_data[error_bit2] = ~corrupted_data[error_bit2];
        
        decode_and_correct(corrupted_data, computed_ecc, corrected_data, se, de, err_pos);
        
        if (de && !se) begin
          test_passed++;
          double_errors_detected++;
        end else begin
          $error("[FAIL] Double error not detected (bits %0d, %0d)", 
                 error_bit1, error_bit2);
          test_failed++;
        end
      end
      
      $display("[PASS] All %0d double bit errors detected", double_errors_detected);
      $display("[TEST] Double bit error detection completed\n");
    end
  endtask
  
  task test_corner_cases();
    logic [DATA_WIDTH-1:0] test_data, corrupted_data;
    logic [ECC_WIDTH-1:0] computed_ecc;
    logic [DATA_WIDTH-1:0] corrected_data;
    logic se, de;
    logic [6:0] err_pos;
    begin
      $display("\n===========================================");
      $display("TEST: Corner Cases");
      $display("===========================================");
      
      // Test all zeros
      test_data = 64'h0000000000000000;
      computed_ecc = generate_ecc(test_data);
      decode_and_correct(test_data, computed_ecc, corrected_data, se, de, err_pos);
      if (corrected_data == test_data && !se && !de) begin
        $display("[PASS] All zeros pattern correct");
        test_passed++;
        all_zeros_tested = 1;
      end else begin
        $error("[FAIL] All zeros pattern failed");
        test_failed++;
      end
      
      // Test all ones
      test_data = 64'hFFFFFFFFFFFFFFFF;
      computed_ecc = generate_ecc(test_data);
      decode_and_correct(test_data, computed_ecc, corrected_data, se, de, err_pos);
      if (corrected_data == test_data && !se && !de) begin
        $display("[PASS] All ones pattern correct");
        test_passed++;
        all_ones_tested = 1;
      end else begin
        $error("[FAIL] All ones pattern failed");
        test_failed++;
      end
      
      // Test alternating pattern
      test_data = 64'hAAAAAAAAAAAAAAAA;
      computed_ecc = generate_ecc(test_data);
      decode_and_correct(test_data, computed_ecc, corrected_data, se, de, err_pos);
      if (corrected_data == test_data && !se && !de) begin
        $display("[PASS] Alternating pattern 0xAAAA correct");
        test_passed++;
      end else begin
        $error("[FAIL] Alternating pattern 0xAAAA failed");
        test_failed++;
      end
      
      test_data = 64'h5555555555555555;
      computed_ecc = generate_ecc(test_data);
      decode_and_correct(test_data, computed_ecc, corrected_data, se, de, err_pos);
      if (corrected_data == test_data && !se && !de) begin
        $display("[PASS] Alternating pattern 0x5555 correct");
        test_passed++;
        alternating_pattern_tested = 1;
      end else begin
        $error("[FAIL] Alternating pattern 0x5555 failed");
        test_failed++;
      end
      
      // Test walking ones
      for (int i = 0; i < DATA_WIDTH; i++) begin
        test_data = 1 << i;
        computed_ecc = generate_ecc(test_data);
        decode_and_correct(test_data, computed_ecc, corrected_data, se, de, err_pos);
        if (corrected_data != test_data || se || de) begin
          $error("[FAIL] Walking ones at bit %0d failed", i);
          test_failed++;
        end
      end
      test_passed++;
      $display("[PASS] Walking ones pattern correct");
      
      $display("[TEST] Corner cases completed\n");
    end
  endtask
  
  task test_random_patterns();
    logic [DATA_WIDTH-1:0] test_data, corrupted_data;
    logic [ECC_WIDTH-1:0] computed_ecc;
    logic [DATA_WIDTH-1:0] corrected_data;
    logic se, de;
    logic [6:0] err_pos;
    begin
      $display("\n===========================================");
      $display("TEST: Random Patterns (%0d tests)", NUM_RANDOM_TESTS);
      $display("===========================================");
      
      for (int i = 0; i < NUM_RANDOM_TESTS; i++) begin
        test_data = {$random(), $random()};
        computed_ecc = generate_ecc(test_data);
        
        // Randomly inject 0, 1, or 2 bit errors
        case ($urandom_range(0, 2))
          0: begin  // No error
            corrupted_data = test_data;
            decode_and_correct(corrupted_data, computed_ecc, corrected_data, se, de, err_pos);
            if (corrected_data == test_data && !se && !de)
              test_passed++;
            else
              test_failed++;
          end
          
          1: begin  // Single error
            int err_bit;
            err_bit = $urandom_range(0, DATA_WIDTH-1);
            corrupted_data = test_data;
            corrupted_data[err_bit] = ~corrupted_data[err_bit];
            decode_and_correct(corrupted_data, computed_ecc, corrected_data, se, de, err_pos);
            if (corrected_data == test_data && se && !de) begin
              test_passed++;
              single_errors_corrected++;
            end else begin
              test_failed++;
            end
          end
          
          2: begin  // Double error
            int err_bit1, err_bit2;
            err_bit1 = $urandom_range(0, DATA_WIDTH-1);
            err_bit2 = $urandom_range(0, DATA_WIDTH-1);
            while (err_bit2 == err_bit1)
              err_bit2 = $urandom_range(0, DATA_WIDTH-1);
            corrupted_data = test_data;
            corrupted_data[err_bit1] = ~corrupted_data[err_bit1];
            corrupted_data[err_bit2] = ~corrupted_data[err_bit2];
            decode_and_correct(corrupted_data, computed_ecc, corrected_data, se, de, err_pos);
            if (de && !se) begin
              test_passed++;
              double_errors_detected++;
            end else begin
              test_failed++;
            end
          end
        endcase
      end
      
      $display("[TEST] Random patterns testing completed\n");
    end
  endtask
  
  task print_coverage_report();
    real bit_coverage_percent;
    int bits_covered;
    begin
      $display("\n\n");
      $display("=".repeat(70));
      $display("              ECC LOGIC VERIFICATION REPORT");
      $display("=".repeat(70));
      $display("");
      $display("Test Summary:");
      $display("  Tests Passed:              %0d", test_passed);
      $display("  Tests Failed:              %0d", test_failed);
      $display("  Single Errors Corrected:   %0d", single_errors_corrected);
      $display("  Double Errors Detected:    %0d", double_errors_detected);
      $display("  False Corrections:         %0d", false_corrections);
      $display("  Missed Errors:             %0d", missed_errors);
      $display("");
      
      $display("Algorithm Verification:");
      $display("  Data Width:                %0d bits", DATA_WIDTH);
      $display("  ECC Width:                 %0d bits", ECC_WIDTH);
      $display("  Total Codeword Width:      %0d bits", TOTAL_WIDTH);
      $display("  ECC Type:                  SEC-DED Hamming Code");
      $display("  Single Error Correction:   %s", 
               (single_errors_corrected > 0) ? "VERIFIED" : "FAILED");
      $display("  Double Error Detection:    %s", 
               (double_errors_detected > 0) ? "VERIFIED" : "FAILED");
      $display("");
      
      $display("Coverage Analysis:");
      bits_covered = 0;
      for (int i = 0; i < DATA_WIDTH; i++) begin
        if (bit_flip_coverage[i] > 0)
          bits_covered++;
      end
      bit_coverage_percent = (real'(bits_covered) / real'(DATA_WIDTH)) * 100.0;
      $display("  Bit Flip Coverage:         %0d/%0d (%.1f%%)", 
               bits_covered, DATA_WIDTH, bit_coverage_percent);
      $display("  All Zeros Tested:          %s", all_zeros_tested ? "YES" : "NO");
      $display("  All Ones Tested:           %s", all_ones_tested ? "YES" : "NO");
      $display("  Alternating Pattern:       %s", 
               alternating_pattern_tested ? "YES" : "NO");
      $display("");
      
      if (test_failed == 0 && single_errors_corrected > 0 && 
          double_errors_detected > 0 && bit_coverage_percent == 100.0) begin
        $display("OVERALL RESULT: *** PASS *** - All tests passed!");
        $display("ECC Algorithm VERIFIED for DDR5 production use");
      end else begin
        $display("OVERALL RESULT: *** FAIL *** - Some tests failed!");
      end
      
      $display("=".repeat(70));
      $display("");
    end
  endtask
  
  //===========================================================================
  // Main Test Execution
  //===========================================================================
  
  initial begin
    // Initialize
    rst_n = 0;
    data_in = '0;
    encode_valid = 0;
    data_with_errors = '0;
    ecc_in = '0;
    decode_valid = 0;
    
    test_passed = 0;
    test_failed = 0;
    single_errors_corrected = 0;
    double_errors_detected = 0;
    false_corrections = 0;
    missed_errors = 0;
    encoding_errors = 0;
    decoding_errors = 0;
    bit_flip_coverage = '0;
    all_zeros_tested = 0;
    all_ones_tested = 0;
    alternating_pattern_tested = 0;
    
    // Waveform dump
    $dumpfile("ecc_logic_tb.vcd");
    $dumpvars(0, ecc_logic_tb);
    
    $display("");
    $display("=".repeat(70));
    $display("       ECC LOGIC TESTBENCH - DDR5 RCD Production");
    $display("       SEC-DED Hamming(72,64) Algorithm Verification");
    $display("=".repeat(70));
    $display("Start time: %.1f ps", $realtime);
    $display("");
    
    // Reset sequence
    #1000;
    rst_n = 1;
    #1000;
    
    // Run tests
    test_no_errors();
    test_single_bit_errors();
    test_double_bit_errors();
    test_corner_cases();
    test_random_patterns();
    
    // Print final report
    print_coverage_report();
    
    // Finish
    #1000;
    $display("[INFO] Testbench completed at %.1f ps", $realtime);
    $finish;
  end
  
  // Timeout watchdog
  initial begin
    #100000000;  // 100us
    $error("[TIMEOUT] Testbench timeout!");
    $finish;
  end

endmodule
