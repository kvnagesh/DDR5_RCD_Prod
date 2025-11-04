//==============================================================================
// File: ddr5_rcd_assertions.sv
// Description: Assertion Library for DDR5 RCD Verification - SystemVerilog Assertions & UVM Hooks
// Author: Production Implementation
// Date: 2025-11-04
//==============================================================================
`ifndef DDR5_RCD_ASSERTIONS_SV
`define DDR5_RCD_ASSERTIONS_SV

//==============================================================================
// Module: ddr5_rcd_assertions
// Description: Protocol and Functional RTL SystemVerilog Assertions
//==============================================================================
module ddr5_rcd_assertions
 (
    input logic clk,
    input logic rst_n,
    // Protocol Signals
    input logic ca_valid,
    input logic [6:0] ca_cmd,
    input logic [16:0] ca_addr,
    input logic [1:0] ca_cs,
    input logic ca_cke,
    input logic ca_odt,
    input logic dq_valid,
    input logic [127:0] dq_data,
    input logic [15:0] dq_mask,
    input logic dq_strobe,
    input logic parity_err,
    input logic alert_n
 );

  //============================================================================
  // Example Protocol Assertions (add more for full protocol coverage)
  //============================================================================

  // CA valid must only be low during reset
  property ca_valid_reset_p;
    @(posedge clk)
      !rst_n |-> !ca_valid;
  endproperty
  CA_VALID_RESET: assert property (ca_valid_reset_p)
    else $error("CA valid asserted during reset at %0t", $time);

  // Command range assertion
  property ca_cmd_range_p;
    @(posedge clk)
       ca_valid |-> ((ca_cmd >= 0) && (ca_cmd <= 127));
  endproperty
  CA_CMD_RANGE: assert property (ca_cmd_range_p)
    else $error("CA command out of range @%0t", $time);

  // Address range assertion
  property ca_addr_range_p;
    @(posedge clk)
      ca_valid |-> (ca_addr inside {[0:131071]});
  endproperty
  CA_ADDR_RANGE: assert property (ca_addr_range_p)
    else $error("CA address out of range @%0t", $time);

  // CA chip select must be valid
  property ca_cs_valid_p;
    @(posedge clk)
      ca_valid |-> (ca_cs inside {[0:3]});
  endproperty
  CA_CS_VALID: assert property (ca_cs_valid_p)
    else $error("CA chip select invalid @%0t", $time);

  // DQ valid should toggle with CA valid
  property dq_valid_sync_p;
    @(posedge clk)
      ca_valid |=> dq_valid;
  endproperty
  DQ_VALID_SYNC: assert property (dq_valid_sync_p)
    else $error("DQ valid not synchronous with CA valid @%0t", $time);

  // Alert signal should not be low unless parity error
  property alert_n_on_parity_p;
    @(posedge clk)
      (parity_err) |-> !alert_n;
  endproperty
  ALERT_N_ON_PARITY: assert property (alert_n_on_parity_p)
    else $error("Alert not low on parity error @%0t", $time);

  //============================================================================
  // TODO Implementation: Clock Stability Checks (Line 87)
  // Description: SVA assertions and coverage to ensure clock signals remain
  //              stable, meet duty cycle requirements, and detect glitches
  //              or frequency errors.
  //============================================================================

  // Parameters for DDR5 clock specifications
  // DDR5 typical clock period for 6400 MT/s is ~312.5ps (3200 MHz)
  // Adjust these parameters based on your design's target frequency
  parameter realtime CLK_PERIOD_MIN = 300ps;  // Minimum clock period
  parameter realtime CLK_PERIOD_MAX = 325ps;  // Maximum clock period
  parameter realtime CLK_PERIOD_NOM = 312.5ps; // Nominal clock period
  parameter realtime DUTY_CYCLE_MIN = 45.0;   // Minimum duty cycle (%)
  parameter realtime DUTY_CYCLE_MAX = 55.0;   // Maximum duty cycle (%)
  parameter realtime GLITCH_WINDOW = 50ps;    // Minimum pulse width to avoid glitch

  // Internal variables for clock period and duty cycle measurement
  realtime last_posedge_time = 0;
  realtime last_negedge_time = 0;
  realtime current_period = 0;
  realtime high_time = 0;
  realtime low_time = 0;
  real duty_cycle = 0;

  // Clock period measurement
  always @(posedge clk) begin
    if (rst_n) begin
      current_period = $realtime - last_posedge_time;
      last_posedge_time = $realtime;
      high_time = last_negedge_time - last_posedge_time;
    end
  end

  always @(negedge clk) begin
    if (rst_n) begin
      last_negedge_time = $realtime;
      low_time = $realtime - last_negedge_time;
      // Calculate duty cycle percentage
      if (current_period > 0)
        duty_cycle = (high_time / current_period) * 100.0;
    end
  end

  //----------------------------------------------------------------------------
  // Assertion 1: Clock Period Stability Check
  // Ensures clock period remains within acceptable min/max bounds
  //----------------------------------------------------------------------------
  property clk_period_stability_p;
    realtime t1;
    @(posedge clk) disable iff (!rst_n)
      (1, t1 = $realtime) |=> 
        (($realtime - t1) >= CLK_PERIOD_MIN) && (($realtime - t1) <= CLK_PERIOD_MAX);
  endproperty
  
  CLK_PERIOD_STABILITY: assert property (clk_period_stability_p)
    else $error("Clock period out of range: %0t at time %0t", current_period, $time);

  //----------------------------------------------------------------------------
  // Assertion 2: Clock Duty Cycle Check
  // Verifies that clock high and low times maintain proper duty cycle
  //----------------------------------------------------------------------------
  property clk_duty_cycle_p;
    @(posedge clk) disable iff (!rst_n)
      ##1 (duty_cycle >= DUTY_CYCLE_MIN) && (duty_cycle <= DUTY_CYCLE_MAX);
  endproperty
  
  CLK_DUTY_CYCLE: assert property (clk_duty_cycle_p)
    else $error("Clock duty cycle violation: %0.2f%% at time %0t", duty_cycle, $time);

  //----------------------------------------------------------------------------
  // Assertion 3: Clock Glitch Detection (Positive Edge)
  // Detects narrow positive pulses that could be glitches
  //----------------------------------------------------------------------------
  property clk_no_pos_glitch_p;
    realtime t_rise;
    @(posedge clk) disable iff (!rst_n)
      (1, t_rise = $realtime) ##0 
        @(negedge clk) (($realtime - t_rise) >= GLITCH_WINDOW);
  endproperty
  
  CLK_NO_POS_GLITCH: assert property (clk_no_pos_glitch_p)
    else $error("Clock positive glitch detected: pulse width %0t at time %0t", 
                ($realtime - last_posedge_time), $time);

  //----------------------------------------------------------------------------
  // Assertion 4: Clock Glitch Detection (Negative Edge)
  // Detects narrow negative pulses that could be glitches
  //----------------------------------------------------------------------------
  property clk_no_neg_glitch_p;
    realtime t_fall;
    @(negedge clk) disable iff (!rst_n)
      (1, t_fall = $realtime) ##0 
        @(posedge clk) (($realtime - t_fall) >= GLITCH_WINDOW);
  endproperty
  
  CLK_NO_NEG_GLITCH: assert property (clk_no_neg_glitch_p)
    else $error("Clock negative glitch detected: pulse width %0t at time %0t", 
                ($realtime - last_negedge_time), $time);

  //----------------------------------------------------------------------------
  // Assertion 5: Clock Frequency Stability
  // Ensures clock period doesn't vary by more than ±2% between consecutive cycles
  //----------------------------------------------------------------------------
  realtime prev_period = 0;
  
  always @(posedge clk) begin
    if (rst_n && prev_period > 0) begin
      automatic real period_variation = 
        (current_period - prev_period) / prev_period * 100.0;
      if ((period_variation > 2.0) || (period_variation < -2.0))
        $error("Clock frequency instability: %0.2f%% variation at time %0t", 
               period_variation, $time);
    end
    prev_period = current_period;
  end

  //----------------------------------------------------------------------------
  // Assertion 6: Clock Must Toggle
  // Ensures clock doesn't remain stuck at same level
  //----------------------------------------------------------------------------
  property clk_must_toggle_p;
    @(posedge clk) disable iff (!rst_n)
      ##1 1;
  endproperty
  
  CLK_MUST_TOGGLE: assert property (clk_must_toggle_p)
    else $error("Clock stuck or not toggling at time %0t", $time);

  //============================================================================
  // Coverage Points for Clock Stability
  //============================================================================
  
  covergroup clk_stability_cg @(posedge clk);
    option.per_instance = 1;
    option.name = "clk_stability_coverage";

    // Coverage for clock period ranges
    cp_clk_period: coverpoint current_period iff (rst_n) {
      bins period_min     = {[CLK_PERIOD_MIN:CLK_PERIOD_NOM-10ps]};
      bins period_nominal = {[CLK_PERIOD_NOM-10ps:CLK_PERIOD_NOM+10ps]};
      bins period_max     = {[CLK_PERIOD_NOM+10ps:CLK_PERIOD_MAX]};
      bins period_out_of_range = {[0:CLK_PERIOD_MIN-1ps], [CLK_PERIOD_MAX+1ps:$]};
    }

    // Coverage for duty cycle ranges
    cp_duty_cycle: coverpoint duty_cycle iff (rst_n) {
      bins duty_low       = {[DUTY_CYCLE_MIN:48.0]};
      bins duty_nominal   = {[48.0:52.0]};
      bins duty_high      = {[52.0:DUTY_CYCLE_MAX]};
      bins duty_violation = {[0:DUTY_CYCLE_MIN-0.1], [DUTY_CYCLE_MAX+0.1:100.0]};
    }

    // Coverage for frequency stability
    cp_freq_stability: coverpoint ((current_period - prev_period) / prev_period * 100.0) iff (rst_n && prev_period > 0) {
      bins stable      = {[-0.5:0.5]};
      bins minor_var   = {[-2.0:-0.5], [0.5:2.0]};
      bins major_var   = {[-5.0:-2.0], [2.0:5.0]};
      bins unstable    = {[$:-5.0], [5.0:$]};
    }

    // Cross coverage: period vs duty cycle
    cx_period_duty: cross cp_clk_period, cp_duty_cycle;

  endgroup

  // Instantiate coverage group
  clk_stability_cg clk_stab_cov = new();

  //============================================================================
  // Additional Protocol/Timing Assertions: Add as needed
  //============================================================================

endmodule : ddr5_rcd_assertions

`endif // DDR5_RCD_ASSERTIONS_SV
