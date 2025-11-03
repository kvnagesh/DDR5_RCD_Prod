//-----------------------------------------------------------------------------
// Title      : Clock Gate Module
// Project    : DDR5 RCD Production
//-----------------------------------------------------------------------------
// File       : clock_gate.sv
// Author     : Design Team
// Created    : 2025-11-03
// Description: Integrated clock gating cell with enable control
//              Provides safe clock gating with glitch-free operation
//-----------------------------------------------------------------------------

module clock_gate #(
  parameter bit USE_LATCH = 1'b1,        // Use latch-based clock gating (recommended)
  parameter bit ASYNC_RESET = 1'b0       // Asynchronous reset support
) (
  // Clock and Reset
  input  logic clk_in,                   // Input clock
  input  logic rst_n,                    // Active-low reset
  
  // Enable Control
  input  logic enable,                   // Clock enable (active high)
  input  logic test_mode,                // Test mode bypass (disable gating)
  
  // Output Clock
  output logic clk_out                   // Gated output clock
);

  //-----------------------------------------------------------------------------
  // Internal Signals
  //-----------------------------------------------------------------------------
  logic enable_latched;
  logic clk_gate_en;
  
  //-----------------------------------------------------------------------------
  // Clock Gate Enable Logic
  //-----------------------------------------------------------------------------
  // In test mode, bypass clock gating to ensure full observability
  assign clk_gate_en = test_mode | enable;

  //-----------------------------------------------------------------------------
  // Latch-Based Clock Gating (Glitch-Free)
  //-----------------------------------------------------------------------------
  generate
    if (USE_LATCH) begin : gen_latch_based
      // Latch enable on negative edge of clock
      // This ensures enable is stable during positive edge
      always_latch begin
        if (!clk_in) begin
          enable_latched = clk_gate_en;
        end
      end
      
      // Gate the clock
      assign clk_out = clk_in & enable_latched;
      
    end else begin : gen_flop_based
      //-------------------------------------------------------------------------
      // Flip-Flop Based Clock Gating (Alternative)
      //-------------------------------------------------------------------------
      // This version uses a flip-flop instead of latch
      // Less area efficient but may be preferred in some flows
      
      always_ff @(negedge clk_in or negedge rst_n) begin
        if (!rst_n) begin
          enable_latched <= 1'b0;
        end else begin
          enable_latched <= clk_gate_en;
        end
      end
      
      assign clk_out = clk_in & enable_latched;
      
    end
  endgenerate

  //-----------------------------------------------------------------------------
  // Assertions (for simulation)
  //-----------------------------------------------------------------------------
  `ifdef SIM_ONLY
    // Check for X/Z on enable during normal operation
    property p_enable_valid;
      @(posedge clk_in) disable iff (!rst_n || test_mode)
        !$isunknown(enable);
    endproperty
    assert_enable_valid: assert property (p_enable_valid)
      else $error("Enable signal has unknown value (X/Z)");

    // Check that enable doesn't change during clock high (without latch)
    property p_enable_stable;
      @(posedge clk_in) disable iff (!rst_n || test_mode || USE_LATCH)
        $stable(enable);
    endproperty
    assert_enable_stable: assert property (p_enable_stable)
      else $warning("Enable changed during clock high period");

    // Verify test mode bypasses gating
    property p_test_mode_bypass;
      @(posedge clk_in) disable iff (!rst_n)
        test_mode |-> (clk_out == clk_in);
    endproperty
    assert_test_mode: assert property (p_test_mode_bypass)
      else $error("Test mode not properly bypassing clock gate");

  `endif

  //-----------------------------------------------------------------------------
  // Coverage (for verification)
  //-----------------------------------------------------------------------------
  `ifdef SIM_ONLY
    covergroup cg_clock_gate @(posedge clk_in);
      cp_enable: coverpoint enable {
        bins low  = {1'b0};
        bins high = {1'b1};
      }
      cp_test_mode: coverpoint test_mode {
        bins normal = {1'b0};
        bins test   = {1'b1};
      }
      cx_enable_test: cross cp_enable, cp_test_mode;
    endgroup

    cg_clock_gate cg_inst = new();
  `endif

endmodule

//-----------------------------------------------------------------------------
// Multi-bit Clock Gate Wrapper
// Provides multiple independent clock gates with shared control
//-----------------------------------------------------------------------------
module clock_gate_array #(
  parameter int NUM_GATES = 4,
  parameter bit USE_LATCH = 1'b1
) (
  input  logic                  clk_in,
  input  logic                  rst_n,
  input  logic [NUM_GATES-1:0]  enable,
  input  logic                  test_mode,
  output logic [NUM_GATES-1:0]  clk_out
);

  //-----------------------------------------------------------------------------
  // Generate Clock Gate Instances
  //-----------------------------------------------------------------------------
  generate
    for (genvar i = 0; i < NUM_GATES; i++) begin : gen_clock_gates
      clock_gate #(
        .USE_LATCH   (USE_LATCH),
        .ASYNC_RESET (1'b0)
      ) u_clock_gate (
        .clk_in    (clk_in),
        .rst_n     (rst_n),
        .enable    (enable[i]),
        .test_mode (test_mode),
        .clk_out   (clk_out[i])
      );
    end
  endgenerate

endmodule
