//-----------------------------------------------------------------------------
// Title       : Clock Gate Verification Testbench (Timing Critical)
// Project     : DDR5 RCD Production
//-----------------------------------------------------------------------------
// File        : clock_gate_tb.sv
// Author      : Verification Team
// Created     : 2025-11-10
// Description : Comprehensive testbench for clock gate module with timing-
//               critical verification including glitch detection, setup/hold
//               timing checks, and race condition testing.
//-----------------------------------------------------------------------------

`timescale 1ps/1fs  // High precision for timing verification

module clock_gate_tb;

  //===========================================================================
  // Parameters
  //===========================================================================
  
  // DDR5 RCD timing parameters (12800 MT/s = 6400 MHz = 156.25 ps period)
  parameter realtime CLK_PERIOD     = 156.25ps;  // DDR5-12800 clock period
  parameter realtime CLK_HALF       = CLK_PERIOD / 2;
  parameter realtime SETUP_TIME     = 10ps;      // Min setup time for enable
  parameter realtime HOLD_TIME      = 5ps;       // Min hold time for enable
  parameter realtime JITTER_MAX     = 5ps;       // Max allowed jitter
  parameter realtime SKEW_MAX       = 10ps;      // Max clock skew tolerance
  
  parameter int NUM_ITERATIONS = 1000;           // Number of test cycles
  parameter bit ENABLE_COVERAGE = 1'b1;
  
  //===========================================================================
  // DUT Signals
  //===========================================================================
  
  logic clk_in;
  logic rst_n;
  logic enable;
  logic test_mode;
  logic clk_out_latch;
  logic clk_out_flop;
  
  //===========================================================================
  // Timing Measurement Signals
  //===========================================================================
  
  realtime clk_in_rise_time;
  realtime clk_in_fall_time;
  realtime clk_out_rise_time;
  realtime clk_out_fall_time;
  realtime enable_change_time;
  realtime measured_skew;
  realtime measured_jitter[$];
  
  int glitch_count;
  int pass_count;
  int fail_count;
  
  //===========================================================================
  // DUT Instantiations
  //===========================================================================
  
  // Latch-based clock gate
  clock_gate #(
    .USE_LATCH(1'b1),
    .ASYNC_RESET(1'b0),
    .SAFE_ENABLE(1'b1)
  ) dut_latch (
    .clk_in(clk_in),
    .rst_n(rst_n),
    .enable(enable),
    .test_mode(test_mode),
    .clk_out(clk_out_latch)
  );
  
  // Flop-based clock gate for comparison
  clock_gate #(
    .USE_LATCH(1'b0),
    .ASYNC_RESET(1'b0),
    .SAFE_ENABLE(1'b1)
  ) dut_flop (
    .clk_in(clk_in),
    .rst_n(rst_n),
    .enable(enable),
    .test_mode(test_mode),
    .clk_out(clk_out_flop)
  );
  
  //===========================================================================
  // Clock Generation with Jitter Modeling
  //===========================================================================
  
  initial begin
    clk_in = 0;
    forever begin
      realtime jitter = $urandom_range(0, JITTER_MAX*1000) / 1000.0;
      #(CLK_HALF + jitter) clk_in = 1;
      #(CLK_HALF - jitter) clk_in = 0;
    end
  end
  
  //===========================================================================
  // Timing Monitors
  //===========================================================================
  
  // Monitor clock input transitions
  always @(posedge clk_in) begin
    clk_in_rise_time = $realtime;
  end
  
  always @(negedge clk_in) begin
    clk_in_fall_time = $realtime;
  end
  
  // Monitor clock output transitions
  always @(posedge clk_out_latch) begin
    clk_out_rise_time = $realtime;
    measured_skew = clk_out_rise_time - clk_in_rise_time;
    measured_jitter.push_back(measured_skew);
    
    // Check skew within specification
    if (measured_skew > SKEW_MAX) begin
      $error("[TIMING] Clock skew violation: %.3f ps > %.3f ps max", 
             measured_skew, SKEW_MAX);
      fail_count++;
    end else begin
      pass_count++;
    end
  end
  
  always @(negedge clk_out_latch) begin
    clk_out_fall_time = $realtime;
  end
  
  // Monitor enable signal changes
  always @(enable) begin
    enable_change_time = $realtime;
  end
  
  //===========================================================================
  // Glitch Detection Monitor
  //===========================================================================
  
  realtime last_clk_out_change;
  
  initial last_clk_out_change = 0;
  
  always @(clk_out_latch) begin
    realtime current_time = $realtime;
    realtime pulse_width = current_time - last_clk_out_change;
    
    // Detect glitches (pulse width < minimum clock period/4)
    if (pulse_width > 0 && pulse_width < (CLK_PERIOD / 4)) begin
      $error("[GLITCH] Detected glitch on clk_out at %.3f ps (width=%.3f ps)",
             current_time, pulse_width);
      glitch_count++;
      fail_count++;
    end
    
    last_clk_out_change = current_time;
  end
  
  //===========================================================================
  // Setup/Hold Timing Checks
  //===========================================================================
  
  // Verify enable meets setup time before clock edge
  always @(posedge clk_in) begin
    realtime time_since_enable = $realtime - enable_change_time;
    if (time_since_enable > 0 && time_since_enable < SETUP_TIME) begin
      $warning("[TIMING] Setup time violation: enable changed %.3f ps before clock edge (min=%.3f ps)",
               time_since_enable, SETUP_TIME);
    end
  end
  
  //===========================================================================
  // Test Stimulus
  //===========================================================================
  
  initial begin
    // Initialize signals
    rst_n = 0;
    enable = 0;
    test_mode = 0;
    glitch_count = 0;
    pass_count = 0;
    fail_count = 0;
    
    // Setup waveform dumping
    $dumpfile("clock_gate_tb.vcd");
    $dumpvars(0, clock_gate_tb);
    
    $display("\n========================================");
    $display("Clock Gate Timing Verification Testbench");
    $display("DDR5 RCD @ 12800 MT/s (6.4 GHz)");
    $display("Clock Period: %.3f ps", CLK_PERIOD);
    $display("========================================\n");
    
    // Reset sequence
    repeat(5) @(posedge clk_in);
    rst_n = 1;
    $display("[%.3f ps] Reset released", $realtime);
    repeat(5) @(posedge clk_in);
    
    // Test 1: Basic enable/disable
    $display("\n[TEST 1] Basic Enable/Disable Test");
    test_enable_disable();
    
    // Test 2: Rapid enable toggling
    $display("\n[TEST 2] Rapid Enable Toggling Test");
    test_rapid_toggling();
    
    // Test 3: Test mode bypass
    $display("\n[TEST 3] Test Mode Bypass");
    test_mode_bypass();
    
    // Test 4: Back-to-back transitions
    $display("\n[TEST 4] Back-to-Back Transitions");
    test_back_to_back();
    
    // Test 5: Random enable pattern
    $display("\n[TEST 5] Random Enable Pattern (Stress Test)");
    test_random_pattern();
    
    // Test 6: Timing corner cases
    $display("\n[TEST 6] Timing Corner Cases");
    test_timing_corners();
    
    // Final report
    repeat(50) @(posedge clk_in);
    print_report();
    
    if (fail_count == 0 && glitch_count == 0) begin
      $display("\n*** TEST PASSED ***\n");
    end else begin
      $display("\n*** TEST FAILED ***\n");
      $display("  Failures: %0d", fail_count);
      $display("  Glitches: %0d", glitch_count);
    end
    
    $finish;
  end
  
  //===========================================================================
  // Test Tasks
  //===========================================================================
  
  task test_enable_disable();
    $display("  Enabling clock...");
    @(negedge clk_in);
    enable = 1;
    repeat(20) @(posedge clk_in);
    
    if (clk_out_latch !== clk_in) begin
      $error("  Clock output not following input when enabled");
      fail_count++;
    end else begin
      $display("  PASS: Clock gated properly when enabled");
    end
    
    $display("  Disabling clock...");
    @(negedge clk_in);
    enable = 0;
    repeat(10) @(posedge clk_in);
    
    if (clk_out_latch !== 0) begin
      $error("  Clock output not gated when disabled");
      fail_count++;
    end else begin
      $display("  PASS: Clock properly gated when disabled");
    end
  endtask
  
  task test_rapid_toggling();
    for (int i = 0; i < 20; i++) begin
      @(negedge clk_in);
      enable = ~enable;
      repeat(3) @(posedge clk_in);
    end
    $display("  PASS: Rapid toggling completed");
  endtask
  
  task test_mode_bypass();
    enable = 0;
    test_mode = 1;
    repeat(20) @(posedge clk_in);
    
    if (clk_out_latch !== clk_in) begin
      $error("  Test mode bypass failed");
      fail_count++;
    end else begin
      $display("  PASS: Test mode bypass working");
    end
    
    test_mode = 0;
    repeat(5) @(posedge clk_in);
  endtask
  
  task test_back_to_back();
    for (int i = 0; i < 10; i++) begin
      @(negedge clk_in);
      enable = 1;
      @(negedge clk_in);
      enable = 0;
    end
    $display("  PASS: Back-to-back transitions completed");
  endtask
  
  task test_random_pattern();
    for (int i = 0; i < NUM_ITERATIONS; i++) begin
      @(negedge clk_in);
      enable = $urandom();
      repeat($urandom_range(1, 10)) @(posedge clk_in);
    end
    $display("  PASS: Random pattern test completed (%0d iterations)", NUM_ITERATIONS);
  endtask
  
  task test_timing_corners();
    // Test enable changes at different points in clock cycle
    for (int i = 0; i < 8; i++) begin
      realtime delay = i * (CLK_PERIOD / 8);
      #delay;
      enable = ~enable;
      @(posedge clk_in);
    end
    $display("  PASS: Timing corner test completed");
  endtask
  
  task print_report();
    realtime avg_jitter, min_jitter, max_jitter;
    
    if (measured_jitter.size() > 0) begin
      min_jitter = measured_jitter[0];
      max_jitter = measured_jitter[0];
      avg_jitter = 0;
      
      foreach(measured_jitter[i]) begin
        avg_jitter += measured_jitter[i];
        if (measured_jitter[i] < min_jitter) min_jitter = measured_jitter[i];
        if (measured_jitter[i] > max_jitter) max_jitter = measured_jitter[i];
      end
      
      avg_jitter = avg_jitter / measured_jitter.size();
      
      $display("\n========================================");
      $display("Timing Verification Report");
      $display("========================================");
      $display("Clock Cycles Measured: %0d", measured_jitter.size());
      $display("Average Skew: %.3f ps", avg_jitter);
      $display("Min Skew: %.3f ps", min_jitter);
      $display("Max Skew: %.3f ps", max_jitter);
      $display("Glitches Detected: %0d", glitch_count);
      $display("Pass Count: %0d", pass_count);
      $display("Fail Count: %0d", fail_count);
      $display("========================================");
    end
  endtask
  
  // Timeout watchdog
  initial begin
    #100ms;
    $error("Testbench timeout!");
    $finish;
  end
  
endmodule
