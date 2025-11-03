// SPDX-License-Identifier: Apache-2.0
// File: src/data_path/signal_router.sv
// Description: Programmable routing matrix for CA/ECC and debug taps
// - Ready/valid stream switching with isolation control
// - Per-path enable, isolation, and tap outputs
// - Synthesizable, glitch-safe muxing with registered selects

`timescale 1ns/1ps

module signal_router #(
  parameter int WIDTH_BITS = 40,
  parameter int PORTS      = 4  // number of inputs to select among
) (
  input  logic                   clk,
  input  logic                   rst_n,

  // Inputs
  input  logic [PORTS-1:0][WIDTH_BITS-1:0] in_data_i,
  input  logic [PORTS-1:0]                 in_valid_i,
  output logic [PORTS-1:0]                 in_ready_o,

  // Output
  output logic [WIDTH_BITS-1:0]            out_data_o,
  output logic                             out_valid_o,
  input  logic                             out_ready_i,

  // Control
  input  logic [$clog2(PORTS)-1:0]         sel_i,        // which input routes to output
  input  logic                              isolate_i,    // force output idle
  input  logic                              tap_enable_i, // mirror output to tap

  // Debug tap
  output logic [WIDTH_BITS-1:0]            tap_data_o,
  output logic                             tap_valid_o
);

  // Register selects to avoid glitches
  logic [$clog2(PORTS)-1:0] sel_q;
  logic isolate_q, tap_en_q;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      sel_q    <= '0;
      isolate_q<= 1'b0;
      tap_en_q <= 1'b0;
    end else begin
      sel_q    <= sel_i;
      isolate_q<= isolate_i;
      tap_en_q <= tap_enable_i;
    end
  end

  // Simple handshake routing: backpressure only to selected input
  always_comb begin
    in_ready_o  = '0;
  end

  // Selected signals
  logic [WIDTH_BITS-1:0] sel_data;
  logic sel_valid;

  assign sel_data  = in_data_i[sel_q];
  assign sel_valid = in_valid_i[sel_q] & ~isolate_q;

  // Ready to selected input only when not isolated
  assign in_ready_o[sel_q] = out_ready_i & ~isolate_q;

  // Outputs
  assign out_data_o  = sel_data;
  assign out_valid_o = sel_valid;

  // Tap
  assign tap_data_o  = tap_en_q ? sel_data  : '0;
  assign tap_valid_o = tap_en_q ? sel_valid : 1'b0;

endmodule
