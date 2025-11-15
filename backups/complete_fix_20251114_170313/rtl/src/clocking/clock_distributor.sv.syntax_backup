// SPDX-License-Identifier: Apache-2.0
// File: src/clocking/clock_distributor.sv
// Description: Low-jitter programmable clock distribution for subchannels with gating and drive cfg
// - Selectable subchannel clock output, per-output gating, drive strength config hooks
// - Clean clock gating via integrated latch-based enable (uses clock_gate.sv)
// - Register-programmable muxing and dividers (simple integer div)

`timescale 1ns/1ps

module clock_distributor #(
  parameter int OUTPUTS = 2
) (
  input  logic                 clk_ref,
  input  logic                 rst_n,

  // Control (cfg domain assumed same as clk_ref for simplicity)
  input  logic [$clog2(OUTPUTS)-1:0]  sel_src_i,     
  input  logic [OUTPUTS-1:0]          gate_en_i,     
  input  logic [OUTPUTS-1:0][1:0]     drv_str_i,     

  // Outputs
  output logic [OUTPUTS-1:0]          clk_out_o
);

  // Simple integer dividers derived from clk_ref
  logic clk_div2, clk_div4;
  logic div2_q;
  logic [1:0] div4_cnt;

  always_ff @(posedge clk_ref or negedge rst_n) begin
    if (!rst_n) begin
      div2_q   <= 1'b0;
      div4_cnt <= 2'b00;
    end else begin
      div2_q   <= ~div2_q;
      div4_cnt <= div4_cnt + 2'd1;
    end
  end
  assign clk_div2 = div2_q;
  assign clk_div4 = div4_cnt[1];

  // Select source clock
  logic clk_sel;
  always_comb begin
    unique case (sel_src_i)
      0: clk_sel = clk_ref;
      1: clk_sel = clk_div2;
      2: clk_sel = clk_div4;
      default: clk_sel = clk_ref;
    endcase
  end

  // Gate per output using provided clock_gate cell (integrated latch enable)
  // clock_gate.sv expected interface: input clk_i, input en_i, output clk_o
  genvar i;
  generate
    for (i=0; i<OUTPUTS; i++) begin : g_clk_out
      clock_gate u_gate (
        .clk_i (clk_sel),
        .en_i  (gate_en_i[i]),
        .clk_o (clk_out_o[i])
      );
      // drv_str_i exposed for synthesis constraints to map pad drivers; unused in RTL
      // synthesis translate_off
      logic [1:0] _unused_drv;
      assign _unused_drv = drv_str_i[i];
      // synthesis translate_on
    end
  endgenerate

endmodule
