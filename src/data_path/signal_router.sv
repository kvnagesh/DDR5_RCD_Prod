//==================================================================================
// Module: signal_router
// Description: Parameterized Signal routing matrix for DDR5 RCD
//   Flexibly routes DQ/CA/DQS/clock signals, handles buffering/FIFO, arbitration,
//   multiple DRAM ranks, ganged/independent subchannels, logs decisions.
//==================================================================================
module signal_router #(
  parameter int DQ_WIDTH       = 8,
  parameter int DQS_WIDTH      = 1,
  parameter int CA_WIDTH       = 7,
  parameter int CK_WIDTH       = 1,
  parameter int NUM_RANKS      = 2,
  parameter int NUM_CHANNELS   = 2,
  parameter bit ENABLE_LOGGING = 1,
  parameter int FIFO_DEPTH     = 8
)(
  input  logic                   clk,
  input  logic                   rst_n,
  input  logic                   cfg_gang_mode,      // 1: ganged, 0: independent
  input  logic [NUM_RANKS-1:0]   cfg_rank_en,
  input  logic [NUM_CHANNELS-1:0]cfg_channel_en,
  input  logic [DQ_WIDTH-1:0]    host_dq_in,
  input  logic [CA_WIDTH-1:0]    host_ca_in,
  input  logic                   host_dqs_in,
  input  logic                   host_ck_in,
  input  logic                   host_pkt_valid,

  output logic [DQ_WIDTH-1:0]    dram_dq_out   [NUM_RANKS][NUM_CHANNELS],
  output logic [CA_WIDTH-1:0]    dram_ca_out   [NUM_RANKS][NUM_CHANNELS],
  output logic                   dram_dqs_out  [NUM_RANKS][NUM_CHANNELS],
  output logic                   dram_ck_out   [NUM_RANKS][NUM_CHANNELS],
  output logic                   route_ack,
  output logic                   error_status
);

logic [NUM_RANKS-1:0][NUM_CHANNELS-1:0][DQ_WIDTH-1:0] dq_buf;
logic [NUM_RANKS-1:0][NUM_CHANNELS-1:0] dq_buf_valid;
logic [NUM_RANKS-1:0][NUM_CHANNELS-1:0][FIFO_DEPTH-1:0][DQ_WIDTH-1:0] dq_fifo;
logic [NUM_RANKS-1:0][NUM_CHANNELS-1:0][FIFO_DEPTH-1:0] dq_fifo_valid;

//---------------------- Parameterized Routing Task -----------------------------
task automatic route_signal(
  input  logic [DQ_WIDTH-1:0]      dq,
  input  logic [CA_WIDTH-1:0]      ca,
  input  logic                     dqs,
  input  logic                     ck,
  input  int                       rank,
  input  int                       channel
);
  begin
    if (cfg_rank_en[rank] && cfg_channel_en[channel]) begin
      // Buffering and FIFO logic
      dq_buf[rank][channel]        = dq;
      dq_buf_valid[rank][channel]  = 1'b1;
      dq_fifo[rank][channel][0]    = dq;
      dq_fifo_valid[rank][channel][0] = 1'b1;
      // Route
      dram_dq_out[rank][channel]   = dq;
      dram_ca_out[rank][channel]   = ca;
      dram_dqs_out[rank][channel]  = dqs;
      dram_ck_out[rank][channel]   = ck;
      route_ack = 1'b1;
      if (ENABLE_LOGGING)
        $display("Routing: rank=%0d ch=%0d dq=0x%0h ca=0x%0h dqs=%0b ck=%0b", rank, channel, dq, ca, dqs, ck);
    end else begin
      error_status = 1'b1;
      if (ENABLE_LOGGING)
        $display("Route ERROR: rank=%0d ch=%0d (disabled)", rank, channel);
    end
  end
endtask

//----------------- Arbitration Task: Simple round-robin ------------------------
task automatic arbitrate(
  output int sel_rank,
  output int sel_channel
);
  static int last_rank;
  static int last_channel;
  begin
    sel_rank    = (last_rank + 1) % NUM_RANKS;
    sel_channel = (last_channel + 1) % NUM_CHANNELS;
    last_rank   = sel_rank;
    last_channel= sel_channel;
    if (ENABLE_LOGGING)
      $display("Arbitrate: next rank=%0d ch=%0d", sel_rank, sel_channel);
  end
endtask

//----------------- Reset and Error Handling ------------------------------------
task automatic handle_reset();
  int i, j, k;
  begin
    for (i = 0; i < NUM_RANKS; i++)
      for (j = 0; j < NUM_CHANNELS; j++)
      begin
        dq_buf[i][j] = '0;
        dq_buf_valid[i][j] = 0;
        for (k = 0; k < FIFO_DEPTH; k++) begin
          dq_fifo[i][j][k] = '0;
          dq_fifo_valid[i][j][k] = 0;
        end
      end
    route_ack    = 0;
    error_status = 0;
    if (ENABLE_LOGGING)
      $display("[Reset] All buffers/FIFOs cleared.");
  end
endtask

task automatic handle_error(input string msg);
  begin
    error_status = 1'b1;
    if (ENABLE_LOGGING)
      $display("[ERROR] %s", msg);
  end
endtask

//----------------- Testbench/Stimulus Integration (Stub) -----------------------
// To be instantiated/called from a testbench (see testbench example)
//-------------------------------------------------------------------------------

// Assertions (sample)
`ifdef FORMAL
  // Route must only happen when channel and rank enabled
  assert property(@(posedge clk) disable iff(!rst_n)
    (host_pkt_valid & cfg_rank_en !== 0 & cfg_channel_en !== 0) |-> route_ack);
  // Error if invalid select
  assert property(@(posedge clk) disable iff(!rst_n)
    (host_pkt_valid & (cfg_rank_en == 0 | cfg_channel_en == 0)) |-> error_status);
`endif

endmodule
// end of signal_router
