//-----------------------------------------------------------------------------
// Title      : Clock Gate Module
// Project    : DDR5 RCD Production
//-----------------------------------------------------------------------------
// File       : clock_gate.sv
// Author     : Design Team
// Created    : 2025-11-03
// Description: Tapeout-quality clock gating cells with both latch-based and
//              flip-flop-based implementations for power management.
//              Provides glitch-free clock gating for DDR5 RCD.
//-----------------------------------------------------------------------------

module clock_gate 
#(
  parameter bit USE_LATCH     = 1'b1,  // 1: Latch-based (ICG), 0: Flop-based
  parameter bit ASYNC_RESET   = 1'b0,  // Asynchronous reset support
  parameter bit SAFE_ENABLE   = 1'b1   // Safe enable (sync enable changes)
)
(
  //===========================================================================
  // Clock and Reset Interface
  //===========================================================================
  input  logic clk_in,              // Input clock
  input  logic rst_n,               // Active-low reset
  
  //===========================================================================
  // Control Interface
  //===========================================================================
  input  logic enable,              // Clock enable (active high)
  input  logic test_mode,           // Test mode bypass (disable gating for DFT)
  
  //===========================================================================
  // Output Interface
  //===========================================================================
  output logic clk_out              // Gated output clock
);

  //=============================================================================
  // Internal Signal Declarations
  //=============================================================================
  
  logic enable_sync;                // Synchronized enable
  logic enable_latched;             // Latched enable (for latch-based gating)
  logic enable_flopped;             // Flopped enable (for flop-based gating)
  logic clk_gate_en;                // Final gate enable signal
  logic test_mode_active;           // Test mode control
  
  //=============================================================================
  // Safe Enable Synchronization (Optional)
  // Synchronizes enable signal to prevent metastability
  //=============================================================================
  
  generate
    if (SAFE_ENABLE) begin : gen_safe_enable
      logic enable_sync_q1, enable_sync_q2;
      
      if (ASYNC_RESET) begin : gen_async_safe
        always_ff @(posedge clk_in or negedge rst_n) begin
          if (!rst_n) begin
            enable_sync_q1 <= 1'b0;
            enable_sync_q2 <= 1'b0;
          end else begin
            enable_sync_q1 <= enable;
            enable_sync_q2 <= enable_sync_q1;
          end
        end
      end else begin : gen_sync_safe
        always_ff @(posedge clk_in) begin
          if (!rst_n) begin
            enable_sync_q1 <= 1'b0;
            enable_sync_q2 <= 1'b0;
          end else begin
            enable_sync_q1 <= enable;
            enable_sync_q2 <= enable_sync_q1;
          end
        end
      end
      
      assign enable_sync = enable_sync_q2;
      
    end else begin : gen_direct_enable
      // Direct connection without synchronization
      assign enable_sync = enable;
    end
  endgenerate
  
  //=============================================================================
  // Test Mode Control
  // In test mode, bypass clock gating to ensure full observability
  //=============================================================================
  
  assign test_mode_active = test_mode;
  assign clk_gate_en = test_mode_active || enable_sync;
  
  //=============================================================================
  // IMPLEMENTATION 1: Latch-Based Clock Gating (ICG Style)
  // Industry standard - negative-level-sensitive latch
  // Enable is captured on falling edge of clock
  //=============================================================================
  
  generate
    if (USE_LATCH) begin : gen_latch_based_cg
      
      // Latch-based clock gate cell
      // The latch opens when clk_in is low, capturing enable_sync
      // This ensures glitch-free clock gating
      always_latch begin
        if (!clk_in) begin
          enable_latched = clk_gate_en;
        end
      end
      
      // Generate gated clock
      // Clock is ANDed with latched enable
      assign clk_out = clk_in && enable_latched;
      
      // Synthesis directive to preserve latch for clock gating
      // This prevents synthesis tools from optimizing away the latch
      /* synthesis syn_preserve = 1 */
      /* synthesis dont_touch = "true" */
      
    end
  endgenerate
  
  //=============================================================================
  // IMPLEMENTATION 2: Flip-Flop-Based Clock Gating
  // Alternative implementation using flip-flop for enable capture
  // More conservative, easier timing closure in some cases
  //=============================================================================
  
  generate
    if (!USE_LATCH) begin : gen_flop_based_cg
      
      // Capture enable on rising edge of inverted clock
      // This mimics the behavior of latch-based gating
      if (ASYNC_RESET) begin : gen_async_flop
        always_ff @(negedge clk_in or negedge rst_n) begin
          if (!rst_n) begin
            enable_flopped <= 1'b0;
          end else begin
            enable_flopped <= clk_gate_en;
          end
        end
      end else begin : gen_sync_flop
        always_ff @(negedge clk_in) begin
          if (!rst_n) begin
            enable_flopped <= 1'b0;
          end else begin
            enable_flopped <= clk_gate_en;
          end
        end
      end
      
      // Generate gated clock
      assign clk_out = clk_in && enable_flopped;
      
      // Synthesis directive to preserve flip-flop for clock gating
      /* synthesis syn_preserve = 1 */
      /* synthesis dont_touch = "true" */
      
    end
  endgenerate
  
  //=============================================================================
  // Synthesis Attributes and Constraints
  //=============================================================================
  
  // Mark this module as a clock gating cell for synthesis tools
  // This helps with proper handling during synthesis and STA
  /* synthesis syn_hier = "hard" */
  /* synthesis clock_gating_cell = "yes" */
  
  //=============================================================================
  // Formal Verification Properties (Synthesis Safe)
  //=============================================================================
  
  `ifdef FORMAL_VERIFICATION
    
    // Property: Clock output must be low when enable is low (unless test mode)
    property clock_gated_when_disabled;
      @(posedge clk_in) disable iff (!rst_n || test_mode_active)
      !enable_sync |-> ##[1:2] !clk_out;
    endproperty
    
    // Property: No glitches on clock output
    property no_clock_glitches;
      @(clk_out) disable iff (!rst_n)
      $stable(clk_out) [*2];
    endproperty
    
    // Property: Test mode always passes clock
    property test_mode_bypass;
      @(posedge clk_in) disable iff (!rst_n)
      test_mode |-> (clk_out == clk_in);
    endproperty
    
    assert property (clock_gated_when_disabled) else
      $error("Clock gating failed - clock active when disabled");
    
    assert property (test_mode_bypass) else
      $error("Test mode bypass failed");
    
  `endif
  
  //=============================================================================
  // Coverage Points for Verification (Synthesis Safe)
  //=============================================================================
  
  `ifdef COVERAGE
    
    covergroup cg_clock_gate @(posedge clk_in);
      
      cp_enable: coverpoint enable_sync {
        bins enable_low  = {1'b0};
        bins enable_high = {1'b1};
      }
      
      cp_test_mode: coverpoint test_mode_active {
        bins test_off = {1'b0};
        bins test_on  = {1'b1};
      }
      
      cp_enable_transitions: coverpoint enable_sync {
        bins low_to_high = (1'b0 => 1'b1);
        bins high_to_low = (1'b1 => 1'b0);
      }
      
      // Cross coverage
      cx_enable_test: cross cp_enable, cp_test_mode;
      
    endgroup
    
    cg_clock_gate cg_inst = new();
    
  `endif
  
endmodule : clock_gate

//=============================================================================
// End of File
//=============================================================================
