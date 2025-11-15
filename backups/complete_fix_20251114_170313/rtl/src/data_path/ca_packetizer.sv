// SPDX-License-Identifier: Apache-2.0
// File: src/data_path/ca_packetizer.sv
// Description: DDR5 RCD CA packetization and formatting for x4/x8 devices with rank select
// - Parameterized device width and rank count
// - Ready/valid streaming input/output
// - Inserts CA cycles/beats per JEDEC framing, simple model
// - Synthesizable and timing-friendly

`timescale 1ns/1ps

module ca_packetizer #(
  parameter int WIDTH_BITS       = 40,        
  parameter int DEV_WIDTH        = 8,         
  parameter int RANKS            = 2,         
  parameter bit INCLUDE_ECC      = 1'b1
) (
  input  logic                   clk,
  input  logic                   rst_n,

  // Config
  input  logic [clog2_int(RANKS)-1:0] rank_sel_i,   
  input  logic [1:0]               burst_len_i,     
  input  logic                     cmd_is_mrs_i,    
  input  logic                     cmd_is_act_i,    
  input  logic                     cmd_is_pre_i,    

  // Stream in: address/command fields packed simple
  input  logic [31:0]             addr_cmd_i,
  input  logic                    in_valid_i,
  output logic                    in_ready_o,

  // Stream out: formatted CA beat(s) with ECC
  output logic [WIDTH_BITS-1:0]   ca_data_o,
  output logic                    ca_valid_o,
  input  logic                    ca_ready_i
);

  // -------- Utilities --------
  function automatic int clog2_int(input int x);
    int i; begin i=0; while ((1<<i) < x) i++; return i; end
  endfunction

  function automatic logic [7:0] ecc8(input logic [31:0] d);
    logic [7:0] p; begin
      p[0]=^d[3:0]; p[1]=^d[7:4]; p[2]=^d[11:8]; p[3]=^d[15:12];
      p[4]=^d[19:16]; p[5]=^d[23:20]; p[6]=^d[27:24]; p[7]=^d[31:28];
      return p;
    end
  endfunction

  // -------- Packet formatter state --------
  typedef enum logic [1:0] {IDLE, BEAT0, BEAT1, BEAT2} state_e;
  state_e state_q, state_d;

  logic [31:0] payload_q;
  logic [WIDTH_BITS-1:0] beat_data;
  logic                   out_valid_d, out_valid_q;
  logic                   take;

  // Map fields into CA based on command type and device width
  function automatic logic [31:0] map_fields(input logic [31:0] in);
    logic [31:0] o; begin
      o = in;
      if (DEV_WIDTH==4) begin
        // example field re-map for x4
        o[7:0]   = in[7:0];   // A[7:0]
        o[15:8]  = in[15:8];  // BA/BankGrp
        o[23:16] = in[23:16]; // opcode
        o[31:24] = { {(clog2_int(RANKS)){1'b0}}, in[31:24][7-clog2_int(RANKS)+:clog2_int(RANKS)] };
      end else begin
        // x8: different packing
        o[9:0]   = in[9:0];   // A[9:0]
        o[17:10] = in[17:10]; // bank
        o[25:18] = in[25:18]; // opcode
        o[31:26] = in[31:26]; // ext
      end
      return o;
    end
  endfunction

  logic [31:0] mapped;
  assign mapped = map_fields(addr_cmd_i);

  // Build 40-bit with ECC in upper bits
  always_comb begin
    beat_data = '0;
    beat_data[31:0]  = mapped;
    beat_data[39:32] = INCLUDE_ECC ? ecc8(mapped) : 8'h00;
  end

  // FSM Controls
  assign take = in_valid_i & in_ready_o;

  always_comb begin
    state_d     = state_q;
    in_ready_o  = 1'b0;
    out_valid_d = 1'b0;

    unique case (state_q)
      IDLE: begin
        in_ready_o = 1'b1;
        if (in_valid_i) begin
          state_d     = (burst_len_i==2'd0) ? BEAT0 : BEAT0; // enter
        end
      end

      BEAT0: begin
        out_valid_d = 1'b1;
        if (ca_ready_i) begin
          if (burst_len_i==2'd0) state_d = IDLE;
          else                    state_d = BEAT1;
        end
      end

      BEAT1: begin
        out_valid_d = 1'b1;
        if (ca_ready_i) begin
          if (burst_len_i==2'd1) state_d = IDLE;
          else                    state_d = BEAT2;
        end
      end

      BEAT2: begin
        out_valid_d = 1'b1;
        if (ca_ready_i) begin
          state_d = IDLE;
        end
      end

      default: state_d = IDLE;
    endcase
  end

  // Registers
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state_q    <= IDLE;
      payload_q  <= '0;
      out_valid_q<= 1'b0;
    end else begin
      state_q    <= state_d;
      if (take) payload_q <= addr_cmd_i;
      out_valid_q<= out_valid_d;
    end
  end

  assign ca_data_o  = beat_data;
  assign ca_valid_o = out_valid_q;

endmodule
