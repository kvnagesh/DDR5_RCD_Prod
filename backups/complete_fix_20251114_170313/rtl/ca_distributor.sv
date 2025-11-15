//-----------------------------------------------------------------------------
// Title      : CA (Command/Address) Distributor
// Project    : DDR5 RCD Production
//-----------------------------------------------------------------------------
// File       : ca_distributor.sv
// Author     : Design Team
// Updated    : 2025-11-04
// Description: Distributes host command/address signals to DRAM devices.
//   Implements parameterized packet decoding/routing with seamless integration.
//   All field widths parameterized as per latest/future DDR5 specs.
//   Full bus mapping, routing modes, and documentation updated for expandability.
//-----------------------------------------------------------------------------
module ca_distributor #(
  parameter int CA_WIDTH        = 24,   
  parameter int RANK_BITS       = 4,    
  parameter int ROW_BITS        = 9,    
  parameter int BANK_BITS       = 4,    
  parameter int COL_BITS        = 4,    
  parameter int CMD_BITS        = 3,    
  parameter int NUM_SUBCHANNELS = 2,    
  parameter int PIPELINE_DEPTH  = 2     // Timing closure pipeline stages
) (
  input  logic                              clk,
  input  logic                              rst_n,
  // Control/routing
  input  logic                              enable,
  input  logic [1:0]                        routing_mode,    
  input  logic [RANK_BITS-1:0]              rank_select,     
  input  logic                              pipeline_enable, 
  // Input CA from Host
  input  logic [CA_WIDTH-1:0]               ca_in,
  input  logic                              ca_valid_in,
  input  logic [RANK_BITS-1:0]              ca_rank_in,      
  output logic                              ca_ready_out,
  // Output CA to DRAM subchannels
  output logic [NUM_SUBCHANNELS-1:0][CA_WIDTH-1:0] ca_out,
  output logic [NUM_SUBCHANNELS-1:0]               ca_valid_out,
  input  logic [NUM_SUBCHANNELS-1:0]               ca_ready_in,
  // Decoded fields
  output logic [BANK_BITS-1:0]              bank,            
  output logic [RANK_BITS-1:0]              rank,            
  output logic [ROW_BITS-1:0]               row,             
  output logic [COL_BITS-1:0]               col,             
  output logic [CMD_BITS-1:0]               cmd_type,        
  output logic                              decode_valid,
  // Status/debug
  output logic [31:0]                       pkt_count,
  output logic [31:0]                       error_count,
  output logic                              overflow_flag
);
//=============================================================================
// Internal Signals (Pipeline, Routing, Status)
//=============================================================================
  logic [PIPELINE_DEPTH:0][CA_WIDTH-1:0]           ca_pipe;
  logic [PIPELINE_DEPTH:0]                         ca_valid_pipe;
  logic [PIPELINE_DEPTH:0][RANK_BITS-1:0]          ca_rank_pipe;
  logic [NUM_SUBCHANNELS-1:0]                      subchannel_enable;
  logic                                            routing_valid;
  logic                                            internal_ready;
  logic [NUM_SUBCHANNELS-1:0]                      output_ready;
  logic [31:0]                                     pkt_count_q, error_count_q;
  logic                                            overflow_flag_q;
//=============================================================================
// Input Capture & Pipeline
//=============================================================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      ca_pipe[0]       <= '0;
      ca_valid_pipe[0] <= 1'b0;
      ca_rank_pipe[0]  <= '0;
    end else begin
      if (enable && ca_valid_in && internal_ready) begin
        ca_pipe[0]       <= ca_in;
        ca_valid_pipe[0] <= 1'b1;
        ca_rank_pipe[0]  <= ca_rank_in;
      end else if (internal_ready) begin
        ca_valid_pipe[0] <= 1'b0;
      end
    end
  end
//=============================================================================
// Timing Closure Pipeline Stages
//=============================================================================
  generate
    for (genvar i = 1; i <= PIPELINE_DEPTH; i++) begin : gen_pipeline
      always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
          ca_pipe[i]       <= '0;
          ca_valid_pipe[i] <= 1'b0;
          ca_rank_pipe[i]  <= '0;
        end else begin
          if (pipeline_enable) begin
            ca_pipe[i]       <= ca_pipe[i-1];
            ca_valid_pipe[i] <= ca_valid_pipe[i-1];
            ca_rank_pipe[i]  <= ca_rank_pipe[i-1];
          end else begin
            ca_pipe[i]       <= (i==1) ? ca_pipe[0] : ca_pipe[i-1];
            ca_valid_pipe[i] <= (i==1) ? ca_valid_pipe[0] : ca_valid_pipe[i-1];
            ca_rank_pipe[i]  <= (i==1) ? ca_rank_pipe[0] : ca_rank_pipe[i-1];
          end
        end
      end
    end
  endgenerate
//=============================================================================
// Field Decoding: Fully Parameterized Mapping (Future-Proofed)
//=============================================================================
  always_comb begin
    bank      = ca_pipe[PIPELINE_DEPTH][CA_WIDTH-1 -: BANK_BITS];
    rank      = ca_pipe[PIPELINE_DEPTH][CA_WIDTH-1-BANK_BITS -: RANK_BITS];
    row       = ca_pipe[PIPELINE_DEPTH][CA_WIDTH-1-BANK_BITS-RANK_BITS -: ROW_BITS];
    col       = ca_pipe[PIPELINE_DEPTH][CA_WIDTH-1-BANK_BITS-RANK_BITS-ROW_BITS -: COL_BITS];
    cmd_type  = ca_pipe[PIPELINE_DEPTH][CMD_BITS-1:0]; // Lowest bits for command type
    decode_valid = ca_valid_pipe[PIPELINE_DEPTH];
  end
//=============================================================================
// Routing: Bus/Port Distribution Logic (Seamless Integration)
//=============================================================================
  always_comb begin
    subchannel_enable = '0;
    routing_valid     = ca_valid_pipe[PIPELINE_DEPTH] && enable;
    case (routing_mode)
      2'b00: subchannel_enable = {NUM_SUBCHANNELS{1'b1}};         // Broadcast
      2'b01: subchannel_enable[0] = 1'b1;                        // SC0 only
      2'b10: if (NUM_SUBCHANNELS > 1) subchannel_enable[1] = 1'b1; // SC1 only
      2'b11: begin                                              // Rank decode
        if (ca_rank_pipe[PIPELINE_DEPTH][0] == 1'b0)
          subchannel_enable[0] = 1'b1;
        else if (NUM_SUBCHANNELS > 1)
          subchannel_enable[1] = 1'b1;
      end
      default: subchannel_enable = '0;
    endcase
  end
//=============================================================================
// Output Stage: Bus Routing and Ready/Valid Handshake
//=============================================================================
  generate
    for (genvar sc = 0; sc < NUM_SUBCHANNELS; sc++) begin : gen_output
      always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
          ca_out[sc]       <= '0;
          ca_valid_out[sc] <= 1'b0;
        end else begin
          if (routing_valid && subchannel_enable[sc] && output_ready[sc]) begin
            ca_out[sc]       <= ca_pipe[PIPELINE_DEPTH];
            ca_valid_out[sc] <= 1'b1;
          end else if (output_ready[sc]) begin
            ca_valid_out[sc] <= 1'b0;
          end
        end
      end
      assign output_ready[sc] = ca_ready_in[sc] || !ca_valid_out[sc];
    end
  endgenerate
  always_comb begin
    internal_ready = 1'b1;
    for (int i = 0; i < NUM_SUBCHANNELS; i++) begin
      if (subchannel_enable[i])
        internal_ready = internal_ready && output_ready[i];
    end
  end
  assign ca_ready_out = internal_ready && enable;
//=============================================================================
// Counters/Debug (Expandability & Verification)
//=============================================================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      pkt_count_q      <= 32'h0;
      error_count_q    <= 32'h0;
      overflow_flag_q  <= 1'b0;
    end else begin
      if (ca_valid_in && ca_ready_out && enable)
        pkt_count_q   <= pkt_count_q + 32'h1;
      if (ca_valid_in && !ca_ready_out && enable) begin
        error_count_q   <= error_count_q + 32'h1;
        overflow_flag_q <= 1'b1;
      end
      if (ca_valid_in && ca_ready_out)
        overflow_flag_q <= 1'b0;
    end
  end
  assign pkt_count     = pkt_count_q;
  assign error_count   = error_count_q;
  assign overflow_flag = overflow_flag_q;
//=============================================================================
// End of File: ca_distributor.sv (Parameterization & Comments Updated)
//=============================================================================
endmodule // ca_distributor
