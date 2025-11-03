//-----------------------------------------------------------------------------
// Title      : CA (Command/Address) Distributor
// Project    : DDR5 RCD Production
//-----------------------------------------------------------------------------
// File       : ca_distributor.sv
// Author     : Design Team
// Created    : 2025-11-03
// Description: Distributes command/address signals from host to DRAM devices
//              Implements CA routing with 2 subchannel support, rank decoding,
//              pipelined output, and full synchronization.
//              Tapeout-quality synthesizable RTL.
//-----------------------------------------------------------------------------

module ca_distributor 
#(
  parameter int CA_WIDTH       = 14,    // CA bus width (DDR5 standard)
  parameter int NUM_SUBCHANNELS = 2,    // DDR5 supports 2 subchannels
  parameter int PIPELINE_DEPTH  = 2,    // Pipeline stages for timing closure
  parameter int RANK_BITS       = 2     // Number of rank select bits
)
(
  //===========================================================================
  // Clock and Reset Interface
  //===========================================================================
  input  logic                              clk,
  input  logic                              rst_n,
  
  //===========================================================================
  // Configuration and Control Interface
  //===========================================================================
  input  logic                              enable,
  input  logic [1:0]                        routing_mode,     // 00: broadcast, 01: SC0, 10: SC1, 11: rank-decode
  input  logic [RANK_BITS-1:0]              rank_select,      // Target rank selection
  input  logic                              pipeline_enable,  // Enable pipeline stages
  
  //===========================================================================
  // Input CA Interface (from Host Controller)
  //===========================================================================
  input  logic [CA_WIDTH-1:0]               ca_in,
  input  logic                              ca_valid_in,
  input  logic [RANK_BITS-1:0]              ca_rank_in,       // Rank info embedded in CA packet
  output logic                              ca_ready_out,
  
  //===========================================================================
  // Output CA Interfaces (to DRAM Subchannels)
  //===========================================================================
  output logic [NUM_SUBCHANNELS-1:0][CA_WIDTH-1:0] ca_out,
  output logic [NUM_SUBCHANNELS-1:0]               ca_valid_out,
  input  logic [NUM_SUBCHANNELS-1:0]               ca_ready_in,
  
  //===========================================================================
  // Status and Debug Interface
  //===========================================================================
  output logic [31:0]                       pkt_count,
  output logic [31:0]                       error_count,
  output logic                              overflow_flag
);

  //=============================================================================
  // Internal Signal Declarations
  //=============================================================================
  
  // Pipeline stage registers
  logic [PIPELINE_DEPTH:0][CA_WIDTH-1:0]           ca_pipe;
  logic [PIPELINE_DEPTH:0]                         ca_valid_pipe;
  logic [PIPELINE_DEPTH:0][RANK_BITS-1:0]          ca_rank_pipe;
  
  // Routing control signals
  logic [NUM_SUBCHANNELS-1:0]                      subchannel_enable;
  logic                                            routing_valid;
  
  // Ready/Valid handshake signals
  logic                                            internal_ready;
  logic [NUM_SUBCHANNELS-1:0]                      output_ready;
  
  // Status counters
  logic [31:0]                                     pkt_count_q;
  logic [31:0]                                     error_count_q;
  logic                                            overflow_flag_q;
  
  //=============================================================================
  // Input Stage: Capture and Initial Processing
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
  // Pipeline Stages: Timing Closure for High-Speed Operation
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
            // Bypass mode - propagate directly
            ca_pipe[i]       <= (i == 1) ? ca_pipe[0] : ca_pipe[i-1];
            ca_valid_pipe[i] <= (i == 1) ? ca_valid_pipe[0] : ca_valid_pipe[i-1];
            ca_rank_pipe[i]  <= (i == 1) ? ca_rank_pipe[0] : ca_rank_pipe[i-1];
          end
        end
      end
    end
  endgenerate
  
  //=============================================================================
  // Routing Logic: Subchannel Selection and Distribution
  //=============================================================================
  
  always_comb begin
    // Default: no subchannel enabled
    subchannel_enable = '0;
    routing_valid = ca_valid_pipe[PIPELINE_DEPTH] && enable;
    
    case (routing_mode)
      2'b00: begin
        // Broadcast mode - send to all subchannels
        subchannel_enable = {NUM_SUBCHANNELS{1'b1}};
      end
      
      2'b01: begin
        // Subchannel 0 only
        subchannel_enable[0] = 1'b1;
      end
      
      2'b10: begin
        // Subchannel 1 only
        if (NUM_SUBCHANNELS > 1)
          subchannel_enable[1] = 1'b1;
      end
      
      2'b11: begin
        // Rank decode mode - use rank info to select subchannel
        // DDR5: Even ranks -> SC0, Odd ranks -> SC1
        if (ca_rank_pipe[PIPELINE_DEPTH][0] == 1'b0)
          subchannel_enable[0] = 1'b1;
        else if (NUM_SUBCHANNELS > 1)
          subchannel_enable[1] = 1'b1;
      end
      
      default: begin
        subchannel_enable = '0;
      end
    endcase
  end
  
  //=============================================================================
  // Output Stage: Synchronized Distribution to Subchannels
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
      
      // Ready signal per subchannel
      assign output_ready[sc] = ca_ready_in[sc] || !ca_valid_out[sc];
    end
  endgenerate
  
  //=============================================================================
  // Ready/Valid Handshake Control
  //=============================================================================
  
  // Internal ready: can accept new data when all enabled outputs are ready
  always_comb begin
    internal_ready = 1'b1;
    for (int i = 0; i < NUM_SUBCHANNELS; i++) begin
      if (subchannel_enable[i]) begin
        internal_ready = internal_ready && output_ready[i];
      end
    end
  end
  
  assign ca_ready_out = internal_ready && enable;
  
  //=============================================================================
  // Packet Counter: Track Processed Transactions
  //=============================================================================
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      pkt_count_q <= 32'h0;
    end else begin
      if (ca_valid_in && ca_ready_out && enable) begin
        pkt_count_q <= pkt_count_q + 32'h1;
      end
    end
  end
  
  assign pkt_count = pkt_count_q;
  
  //=============================================================================
  // Error Detection: Overflow and Protocol Violations
  //=============================================================================
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      error_count_q  <= 32'h0;
      overflow_flag_q <= 1'b0;
    end else begin
      // Detect overflow condition: valid input but not ready
      if (ca_valid_in && !ca_ready_out && enable) begin
        error_count_q  <= error_count_q + 32'h1;
        overflow_flag_q <= 1'b1;
      end
      
      // Clear overflow flag on successful transaction
      if (ca_valid_in && ca_ready_out) begin
        overflow_flag_q <= 1'b0;
      end
    end
  end
  
  assign error_count  = error_count_q;
  assign overflow_flag = overflow_flag_q;
  
  //=============================================================================
  // Assertions for Verification (Synthesis Safe)
  //=============================================================================
  
  `ifdef FORMAL_VERIFICATION
    // Check parameter constraints
    initial begin
      assert (CA_WIDTH > 0) else $error("CA_WIDTH must be positive");
      assert (NUM_SUBCHANNELS > 0) else $error("NUM_SUBCHANNELS must be positive");
      assert (PIPELINE_DEPTH >= 0) else $error("PIPELINE_DEPTH must be non-negative");
    end
    
    // Protocol checks
    property valid_requires_ready;
      @(posedge clk) disable iff (!rst_n)
      ca_valid_in && !ca_ready_out |=> ca_valid_in;
    endproperty
    
    assert property (valid_requires_ready) else 
      $error("Valid signal dropped without ready");
  `endif
  
endmodule : ca_distributor

//=============================================================================
// End of File
//=============================================================================
