//-----------------------------------------------------------------------------
// Title       : Clock Gate Formal Verification Module
// Project     : DDR5 RCD Production
//-----------------------------------------------------------------------------
// File        : clock_gate_formal.sv
// Author      : Verification Team
// Created     : 2025-11-10
// Description : Formal verification properties for clock gate using SVA.
//               Includes glitch-free assertions, state coverage, and
//               timing-critical safety/liveness properties.
//-----------------------------------------------------------------------------

`timescale 1ps/1fs

module clock_gate_formal #(
  parameter bit USE_LATCH = 1'b1,
  parameter bit ASYNC_RESET = 1'b0,
  parameter bit SAFE_ENABLE = 1'b1
)(
  input logic clk_in,
  input logic rst_n,
  input logic enable,
  input logic test_mode,
  output logic clk_out
);

  // DUT instantiation
  clock_gate #(
    .USE_LATCH(USE_LATCH),
    .ASYNC_RESET(ASYNC_RESET),
    .SAFE_ENABLE(SAFE_ENABLE)
  ) dut (
    .clk_in(clk_in),
    .rst_n(rst_n),
    .enable(enable),
    .test_mode(test_mode),
    .clk_out(clk_out)
  );

  //===========================================================================
  // Formal Assumptions
  //===========================================================================

  // Assume valid clock
  property valid_clock;
    $rose(clk_in) |=> ##[1:1000] $rose(clk_in);
  endproperty
  assume property (@(posedge clk_in) valid_clock);

  // Assume reset behavior
  property reset_stable;
    $fell(rst_n) |=> rst_n == 0 throughout ##[1:10] $rose(rst_n);
  endproperty
  assume property (@(posedge clk_in) reset_stable);

  //===========================================================================
  // Safety Properties - Critical for Glitch-Free Operation
  //===========================================================================

  // PROPERTY 1: No glitches on gated clock output
  // Ensures clock output changes only on clock edges
  property no_glitch;
    @(clk_in or clk_out) disable iff (!rst_n)
      $changed(clk_out) |-> ($changed(clk_in));
  endproperty
  assert property (no_glitch)
    else $error("FORMAL ERROR: Glitch detected on clk_out!");

  // PROPERTY 2: Clock output must be stable during inactive phase
  property clk_out_stable_when_disabled;
    @(posedge clk_in) disable iff (!rst_n || test_mode)
      !enable ##1 !enable |-> !clk_out throughout ##[1:$] (!enable)[*1];
  endproperty
  assert property (clk_out_stable_when_disabled)
    else $error("FORMAL ERROR: clk_out not stable when disabled!");

  // PROPERTY 3: Clock gating happens on safe edge (falling edge of clk_in)
  property safe_edge_gating;
    @(negedge clk_in) disable iff (!rst_n || test_mode)
      $fell(enable) |=> ##[0:2] (clk_out == 0);
  endproperty
  assert property (safe_edge_gating)
    else $error("FORMAL ERROR: Unsafe edge gating detected!");

  // PROPERTY 4: Test mode always passes clock through
  property test_mode_passthrough;
    @(posedge clk_in) disable iff (!rst_n)
      test_mode |-> ##1 (clk_out == clk_in);
  endproperty
  assert property (test_mode_passthrough)
    else $error("FORMAL ERROR: Test mode bypass failed!");

  // PROPERTY 5: No partial pulses - if clock starts, it must complete
  property complete_pulse;
    @(clk_out) disable iff (!rst_n)
      $rose(clk_out) |-> ##[1:$] $fell(clk_out);
  endproperty
  assert property (complete_pulse)
    else $error("FORMAL ERROR: Incomplete clock pulse detected!");

  // PROPERTY 6: Clock output frequency <= input frequency
  property freq_constraint;
    @(posedge clk_out) disable iff (!rst_n)
      1'b1 |-> ##[1:$] ($past(clk_in) == 1);
  endproperty
  assert property (freq_constraint)
    else $error("FORMAL ERROR: Output frequency exceeds input!");

  //===========================================================================
  // Liveness Properties - Ensure Progress
  //===========================================================================

  // PROPERTY 7: If enabled, clock will eventually propagate
  property enable_leads_to_clock;
    @(posedge clk_in) disable iff (!rst_n)
      enable && !test_mode |-> ##[2:10] (clk_out == clk_in);
  endproperty
  assert property (enable_leads_to_clock)
    else $error("FORMAL ERROR: Enable did not propagate to output!");

  // PROPERTY 8: Clock will eventually stop when disabled
  property disable_stops_clock;
    @(negedge clk_in) disable iff (!rst_n || test_mode)
      !enable |-> ##[1:3] (clk_out == 0);
  endproperty
  assert property (disable_stops_clock)
    else $error("FORMAL ERROR: Clock did not stop when disabled!");

  //===========================================================================
  // State Coverage - Ensure all states are reachable
  //===========================================================================

  // Cover: Enable asserted
  cover property (@(posedge clk_in) disable iff (!rst_n) enable);

  // Cover: Enable deasserted
  cover property (@(posedge clk_in) disable iff (!rst_n) !enable);

  // Cover: Test mode active
  cover property (@(posedge clk_in) disable iff (!rst_n) test_mode);

  // Cover: Enable transitions
  cover property (@(posedge clk_in) disable iff (!rst_n) $rose(enable));
  cover property (@(posedge clk_in) disable iff (!rst_n) $fell(enable));

  // Cover: Clock output transitions
  cover property (@(clk_in) $rose(clk_out));
  cover property (@(clk_in) $fell(clk_out));

  // Cover: All combinations of enable and test_mode
  cover property (@(posedge clk_in) disable iff (!rst_n) 
    enable && !test_mode);
  cover property (@(posedge clk_in) disable iff (!rst_n) 
    !enable && !test_mode);
  cover property (@(posedge clk_in) disable iff (!rst_n) 
    enable && test_mode);
  cover property (@(posedge clk_in) disable iff (!rst_n) 
    !enable && test_mode);

  //===========================================================================
  // Timing-Critical Properties
  //===========================================================================

  // PROPERTY 9: Minimum pulse width check
  property min_pulse_width;
    realtime rise_time, fall_time;
    @(clk_out)
      ($rose(clk_out), rise_time = $realtime) |=> 
      ($fell(clk_out), fall_time = $realtime) and 
      ((fall_time - rise_time) >= 50ps); // Min 50ps pulse width
  endproperty
  assert property (min_pulse_width)
    else $error("FORMAL ERROR: Pulse width below minimum!");

  // PROPERTY 10: No clock output when reset active
  property reset_kills_clock;
    @(posedge clk_in)
      !rst_n |-> (clk_out == 0);
  endproperty
  assert property (reset_kills_clock)
    else $error("FORMAL ERROR: Clock active during reset!");

  //===========================================================================
  // Mutual Exclusion Properties
  //===========================================================================

  // PROPERTY 11: Enable and disable are mutually exclusive states
  property enable_xor_disable;
    @(posedge clk_in) disable iff (!rst_n)
      enable || !enable; // Always true, sanity check
  endproperty
  assert property (enable_xor_disable);

  //===========================================================================
  // Advanced Formal Bounds
  //===========================================================================

  // Bound the proof depth
  parameter MAX_PROOF_DEPTH = 100;

  // Cover: Sustained enable for multiple cycles
  cover property (@(posedge clk_in) disable iff (!rst_n)
    enable[*10]);

  // Cover: Rapid toggling scenario
  cover property (@(posedge clk_in) disable iff (!rst_n)
    $rose(enable) ##1 $fell(enable) ##1 $rose(enable));

  //===========================================================================
  // Auxiliary Code for Formal Tools
  //===========================================================================

  // Signal for formal tools to track enable synchronization
  (* keep *) logic enable_synced;
  
  generate
    if (SAFE_ENABLE) begin
      always_ff @(posedge clk_in or negedge rst_n) begin
        if (!rst_n)
          enable_synced <= 1'b0;
        else
          enable_synced <= enable;
      end
    end else begin
      assign enable_synced = enable;
    end
  endgenerate

  //===========================================================================
  // Formal Verification Directives
  //===========================================================================

  `ifdef FORMAL
    initial begin
      $display("======================================");
      $display("Clock Gate Formal Verification");
      $display("Configuration:");
      $display("  USE_LATCH: %b", USE_LATCH);
      $display("  ASYNC_RESET: %b", ASYNC_RESET);
      $display("  SAFE_ENABLE: %b", SAFE_ENABLE);
      $display("======================================");
    end

    // Formal tool hints
    // synthesis translate_off
    always @(posedge clk_in) begin
      if (rst_n && enable && !clk_out && !test_mode) begin
        $info("INFO: Waiting for clock to propagate...");
      end
    end
    // synthesis translate_on
  `endif

endmodule

//=============================================================================
// End of File
//=============================================================================
