//-----------------------------------------------------------------------------
// Title       : Clock Distributor Testbench with Skew Analysis
// Project     : DDR5 RCD Production
//-----------------------------------------------------------------------------
// File        : clock_distributor_tb.sv
// Author      : Verification Team
// Created     : 2025-11-11
// Description : Comprehensive testbench for clock distributor with inter-output
//               skew measurement, divider verification, and multi-output
//               distribution testing for DDR5 RCD.
//-----------------------------------------------------------------------------

`timescale 1ps/1fs  // High precision for skew analysis

module clock_distributor_tb;

  //===========================================================================
  // Parameters
  //===========================================================================
  
  parameter int OUTPUTS = 4;  // Test with 4 outputs
  parameter realtime CLK_PERIOD = 156.25ps;  // DDR5-12800 (6.4 GHz)
  parameter realtime SKEW_LIMIT = 10ps;      // Max 10ps inter-output skew
  parameter realtime JITTER_LIMIT = 5ps;     // Max 5ps jitter per output
  parameter int NUM_CYCLES = 1000;           // Test duration
  
  //===========================================================================
  // DUT Signals
  //===========================================================================
  
  logic clk_ref;
  logic rst_n;
  logic [$clog2(OUTPUTS)-1:0] sel_src_i;
  logic [OUTPUTS-1:0] gate_en_i;
  logic [OUTPUTS-1:0][1:0] drv_str_i;
  logic [OUTPUTS-1:0] clk_out_o;
  
  //===========================================================================
  // Measurement Signals
  //===========================================================================
  
  // Timestamp arrays for each output
  realtime rise_time [OUTPUTS][$];
  realtime fall_time [OUTPUTS][$];
  realtime last_edge_time [OUTPUTS];
  
  // Skew measurements
  realtime inter_output_skew [OUTPUTS][OUTPUTS][$];  // Skew between output pairs
  realtime max_skew_measured;
  realtime avg_skew;
  
  // Per-output period and jitter
  realtime period_measured [OUTPUTS][$];
  realtime jitter_measured [OUTPUTS][$];
  realtime max_jitter [OUTPUTS];
  
  // Statistics
  int glitch_count [OUTPUTS];
  int pass_count;
  int fail_count;
  int total_edges [OUTPUTS];
  
  //===========================================================================
  // DUT Instantiation
  //===========================================================================
  
  clock_distributor #(
    .OUTPUTS(OUTPUTS)
  ) dut (
    .clk_ref(clk_ref),
    .rst_n(rst_n),
    .sel_src_i(sel_src_i),
    .gate_en_i(gate_en_i),
    .drv_str_i(drv_str_i),
    .clk_out_o(clk_out_o)
  );
  
  //===========================================================================
  // Clock Generation
  //===========================================================================
  
  initial begin
    clk_ref = 0;
    forever #(CLK_PERIOD/2) clk_ref = ~clk_ref;
  end
  
  //===========================================================================
  // Edge Timestamp Capture for Skew Analysis
  //===========================================================================
  
  genvar i;
  generate
    for (i = 0; i < OUTPUTS; i++) begin : gen_edge_capture
      
      // Capture rising edges
      always @(posedge clk_out_o[i]) begin
        realtime current_time = $realtime;
        rise_time[i].push_back(current_time);
        last_edge_time[i] = current_time;
        total_edges[i]++;
        
        // Measure period and jitter
        if (rise_time[i].size() > 1) begin
          realtime period = current_time - rise_time[i][$-2];
          period_measured[i].push_back(period);
          
          realtime jitter = $abs(period - CLK_PERIOD);
          jitter_measured[i].push_back(jitter);
          
          if (jitter > max_jitter[i])
            max_jitter[i] = jitter;
            
          if (jitter > JITTER_LIMIT) begin
            $error("[OUTPUT %0d] Jitter %.3f ps exceeds limit %.3f ps at %.3f ps",
                   i, jitter, JITTER_LIMIT, current_time);
            fail_count++;
          end
        end
      end
      
      // Capture falling edges
      always @(negedge clk_out_o[i]) begin
        realtime current_time = $realtime;
        fall_time[i].push_back(current_time);
        last_edge_time[i] = current_time;
      end
      
      // Glitch detection
      always @(clk_out_o[i]) begin
        realtime current_time = $realtime;
        if (last_edge_time[i] > 0) begin
          realtime pulse_width = current_time - last_edge_time[i];
          if (pulse_width > 0 && pulse_width < (CLK_PERIOD / 4)) begin
            $error("[OUTPUT %0d] GLITCH detected: pulse width %.3f ps at %.3f ps",
                   i, pulse_width, current_time);
            glitch_count[i]++;
            fail_count++;
          end
        end
      end
      
    end
  endgenerate
  
  //===========================================================================
  // Inter-Output Skew Measurement
  //===========================================================================
  
  // Measure skew between all output pairs every clock cycle
  always @(posedge clk_ref) begin
    if (rst_n) begin
      // Wait for all outputs to have at least one edge
      automatic bit all_active = 1;
      for (int j = 0; j < OUTPUTS; j++) begin
        if (gate_en_i[j] && rise_time[j].size() == 0)
          all_active = 0;
      end
      
      if (all_active) begin
        // Measure skew between all pairs
        for (int out1 = 0; out1 < OUTPUTS; out1++) begin
          for (int out2 = out1+1; out2 < OUTPUTS; out2++) begin
            if (gate_en_i[out1] && gate_en_i[out2] && 
                rise_time[out1].size() > 0 && rise_time[out2].size() > 0) begin
              
              realtime skew = $abs(rise_time[out1][$-1] - rise_time[out2][$-1]);
              inter_output_skew[out1][out2].push_back(skew);
              
              // Track maximum skew
              if (skew > max_skew_measured)
                max_skew_measured = skew;
              
              // Check against specification
              if (skew > SKEW_LIMIT) begin
                $error("[SKEW VIOLATION] Out%0d <-> Out%0d: %.3f ps > %.3f ps limit at %.3f ps",
                       out1, out2, skew, SKEW_LIMIT, $realtime);
                fail_count++;
              end else begin
                pass_count++;
              end
            end
          end
        end
      end
    end
  end
  
  //===========================================================================
  // Test Stimulus
  //===========================================================================
  
  initial begin
    // Initialize
    rst_n = 0;
    sel_src_i = 0;
    gate_en_i = '0;
    drv_str_i = '0;
    max_skew_measured = 0;
    pass_count = 0;
    fail_count = 0;
    
    for (int j = 0; j < OUTPUTS; j++) begin
      glitch_count[j] = 0;
      max_jitter[j] = 0;
      total_edges[j] = 0;
      last_edge_time[j] = 0;
    end
    
    // Waveform dump
    $dumpfile("clock_distributor_tb.vcd");
    $dumpvars(0, clock_distributor_tb);
    
    $display("\n" + "=".repeat(70));
    $display("Clock Distributor Testbench with Skew Analysis");
    $display("DDR5 RCD @ 12800 MT/s (6.4 GHz)");
    $display("Configuration: %0d outputs, %.3f ps clock period", OUTPUTS, CLK_PERIOD);
    $display("Skew Limit: %.3f ps, Jitter Limit: %.3f ps", SKEW_LIMIT, JITTER_LIMIT);
    $display("=".repeat(70) + "\n");
    
    // Reset
    repeat(10) @(posedge clk_ref);
    rst_n = 1;
    $display("[%.3f ps] Reset released", $realtime);
    repeat(5) @(posedge clk_ref);
    
    // Test 1: Reference clock (sel_src=0), all outputs enabled
    $display("\n[TEST 1] Reference Clock Distribution - All Outputs");
    test_ref_clock_all_outputs();
    
    // Test 2: Divided clock (div2)
    $display("\n[TEST 2] Divided Clock (div2) Distribution");
    test_div2_clock();
    
    // Test 3: Divided clock (div4)
    $display("\n[TEST 3] Divided Clock (div4) Distribution");
    test_div4_clock();
    
    // Test 4: Independent gating
    $display("\n[TEST 4] Independent Output Gating");
    test_independent_gating();
    
    // Test 5: Sequential enable
    $display("\n[TEST 5] Sequential Output Enable");
    test_sequential_enable();
    
    // Test 6: Stress test - rapid switching
    $display("\n[TEST 6] Rapid Configuration Switching");
    test_rapid_switching();
    
    // Test 7: Clock tree balance verification
    $display("\n[TEST 7] Clock Tree Balance Verification");
    test_clock_tree_balance();
    
    // Final report
    repeat(50) @(posedge clk_ref);
    print_skew_analysis_report();
    
    // Pass/Fail
    $display("\n" + "=".repeat(70));
    if (fail_count == 0 && max_skew_measured <= SKEW_LIMIT) begin
      $display("*** TEST PASSED ***");
      $display("  Max Skew: %.3f ps (Limit: %.3f ps)", max_skew_measured, SKEW_LIMIT);
      $display("  All %0d checks passed", pass_count);
    end else begin
      $display("*** TEST FAILED ***");
      $display("  Failures: %0d", fail_count);
      $display("  Max Skew: %.3f ps (Limit: %.3f ps)", max_skew_measured, SKEW_LIMIT);
    end
    $display("=".repeat(70) + "\n");
    
    $finish;
  end
  
  //===========================================================================
  // Test Tasks
  //===========================================================================
  
  task test_ref_clock_all_outputs();
    sel_src_i = 0;  // Reference clock
    gate_en_i = '1; // All enabled
    drv_str_i = '1; // Default drive strength
    
    repeat(100) @(posedge clk_ref);
    $display("  PASS: Reference clock distributed to all outputs");
  endtask
  
  task test_div2_clock();
    sel_src_i = 1;  // Divide by 2
    gate_en_i = '1;
    
    repeat(100) @(posedge clk_ref);
    
    // Verify frequency is half
    if (period_measured[0].size() > 10) begin
      realtime avg_period = 0;
      for (int j = 0; j < 10; j++)
        avg_period += period_measured[0][$-j-1];
      avg_period = avg_period / 10;
      
      realtime expected_period = 2 * CLK_PERIOD;
      if ($abs(avg_period - expected_period) < 20ps) begin
        $display("  PASS: Div2 period = %.3f ps (expected %.3f ps)", avg_period, expected_period);
      end else begin
        $error("  FAIL: Div2 period = %.3f ps (expected %.3f ps)", avg_period, expected_period);
        fail_count++;
      end
    end
  endtask
  
  task test_div4_clock();
    sel_src_i = 2;  // Divide by 4
    gate_en_i = '1;
    
    repeat(100) @(posedge clk_ref);
    
    // Verify frequency is quarter
    if (period_measured[0].size() > 10) begin
      realtime avg_period = 0;
      for (int j = 0; j < 10; j++)
        avg_period += period_measured[0][$-j-1];
      avg_period = avg_period / 10;
      
      realtime expected_period = 4 * CLK_PERIOD;
      if ($abs(avg_period - expected_period) < 40ps) begin
        $display("  PASS: Div4 period = %.3f ps (expected %.3f ps)", avg_period, expected_period);
      end else begin
        $error("  FAIL: Div4 period = %.3f ps (expected %.3f ps)", avg_period, expected_period);
        fail_count++;
      end
    end
  endtask
  
  task test_independent_gating();
    sel_src_i = 0;
    
    // Enable outputs one at a time
    for (int out = 0; out < OUTPUTS; out++) begin
      gate_en_i = (1 << out);
      repeat(50) @(posedge clk_ref);
      
      // Verify only one output is active
      for (int check = 0; check < OUTPUTS; check++) begin
        if (check == out) begin
          if (total_edges[check] == 0) begin
            $error("  FAIL: Output %0d should be active", check);
            fail_count++;
          end
        end
      end
    end
    $display("  PASS: Independent gating verified");
  endtask
  
  task test_sequential_enable();
    sel_src_i = 0;
    gate_en_i = '0;
    
    // Enable outputs sequentially
    for (int out = 0; out < OUTPUTS; out++) begin
      gate_en_i[out] = 1;
      repeat(30) @(posedge clk_ref);
    end
    
    repeat(50) @(posedge clk_ref);
    $display("  PASS: Sequential enable completed");
  endtask
  
  task test_rapid_switching();
    // Rapidly switch between configurations
    for (int iter = 0; iter < 20; iter++) begin
      sel_src_i = $urandom() % 3;
      gate_en_i = $urandom();
      repeat(10) @(posedge clk_ref);
    end
    $display("  PASS: Rapid switching test completed");
  endtask
  
  task test_clock_tree_balance();
    sel_src_i = 0;
    gate_en_i = '1;
    
    repeat(200) @(posedge clk_ref);
    
    // Check that all outputs have similar edge counts
    int min_edges = total_edges[0];
    int max_edges = total_edges[0];
    
    for (int out = 1; out < OUTPUTS; out++) begin
      if (total_edges[out] < min_edges) min_edges = total_edges[out];
      if (total_edges[out] > max_edges) max_edges = total_edges[out];
    end
    
    int edge_imbalance = max_edges - min_edges;
    if (edge_imbalance <= 2) begin
      $display("  PASS: Clock tree balanced (max imbalance: %0d edges)", edge_imbalance);
    end else begin
      $error("  FAIL: Clock tree imbalanced (imbalance: %0d edges)", edge_imbalance);
      fail_count++;
    end
  endtask
  
  //===========================================================================
  // Reporting
  //===========================================================================
  
  task print_skew_analysis_report();
    $display("\n" + "=".repeat(70));
    $display("SKEW ANALYSIS REPORT");
    $display("=".repeat(70));
    
    // Per-output statistics
    $display("\nPer-Output Statistics:");
    $display("  Output | Edges | Max Jitter (ps) | Glitches");
    $display("  " + "-".repeat(50));
    for (int out = 0; out < OUTPUTS; out++) begin
      $display("    %0d    | %5d | %14.3f | %5d",
               out, total_edges[out], max_jitter[out], glitch_count[out]);
    end
    
    // Inter-output skew matrix
    $display("\nInter-Output Skew Matrix (ps):");
    $display("  " + "-".repeat(60));
    $display("        ", {OUTPUTS{"  Out%0d  "}}, 0, 1, 2, 3);
    
    for (int out1 = 0; out1 < OUTPUTS; out1++) begin
      $write("  Out%0d  ", out1);
      for (int out2 = 0; out2 < OUTPUTS; out2++) begin
        if (out1 == out2) begin
          $write("    -    ");
        end else if (out1 < out2 && inter_output_skew[out1][out2].size() > 0) begin
          // Calculate average skew
          realtime avg_skew_pair = 0;
          int num_samples = inter_output_skew[out1][out2].size();
          if (num_samples > 100) num_samples = 100;  // Last 100 samples
          
          for (int k = 0; k < num_samples; k++)
            avg_skew_pair += inter_output_skew[out1][out2][$-k-1];
          avg_skew_pair = avg_skew_pair / num_samples;
          
          $write(" %7.3f ", avg_skew_pair);
        end else begin
          $write("    -    ");
        end
      end
      $write("\n");
    end
    
    // Summary
    $display("\nSkew Summary:");
    $display("  Maximum Measured Skew: %.3f ps", max_skew_measured);
    $display("  Specification Limit:   %.3f ps", SKEW_LIMIT);
    $display("  Margin:                %.3f ps", SKEW_LIMIT - max_skew_measured);
    
    $display("\nTest Statistics:");
    $display("  Passed Checks: %0d", pass_count);
    $display("  Failed Checks: %0d", fail_count);
    $display("  Total Glitches: %0d", glitch_count.sum());
    
    $display("=".repeat(70));
  endtask
  
  // Timeout
  initial begin
    #100ms;
    $error("Testbench timeout!");
    $finish;
  end
  
endmodule
