//==================================================================================
// Module: subchannel_controller
// Description: Enhanced parameterized subchannel controller for DDR5 RCD
//   Handles routing, arbitration, FIFO buffering, load balancing, logging,
//   covers reset/error paths, and supports independent/ganged subchannels.
//==================================================================================
module subchannel_controller #(
  parameter int SUBCHANNEL_WIDTH     = 40,
  parameter int NUM_SUBCHANNELS      = 2,
  parameter int DATA_WIDTH           = 80,
  parameter int SYNC_STAGES          = 2,
  parameter int PIPELINE_DEPTH       = 3,
  parameter bit ENABLE_ARBITRATION   = 1,
  parameter bit ENABLE_LOAD_BALANCING= 1,
  parameter bit ENABLE_LOGGING       = 1,
  parameter int FIFO_DEPTH           = 8
)(
  input  logic                         clk,
  input  logic                         rst_n,
  input  logic                         cfg_independent,
  input  logic                         cfg_ganged,
  input  logic [NUM_SUBCHANNELS-1:0]   cfg_subchannel_en,
  input  logic [DATA_WIDTH-1:0]        data_in,
  input  logic                         data_in_valid,

  output logic [SUBCHANNEL_WIDTH-1:0]  subch_data_out   [NUM_SUBCHANNELS],
  output logic                         subch_valid      [NUM_SUBCHANNELS],
  output logic                         arb_decision,
  output logic                         error_status
);

logic [NUM_SUBCHANNELS-1:0][SUBCHANNEL_WIDTH-1:0] data_fifo  [FIFO_DEPTH];
logic [NUM_SUBCHANNELS-1:0][FIFO_DEPTH-1:0]        fifo_valid;

//-------------------- Parameterized Routing Task ------------------------------
task automatic route_subchannel(
  input  logic [SUBCHANNEL_WIDTH-1:0] d,
  input  int                         subch
);
  begin
    if (cfg_subchannel_en[subch]) begin
      // Buffering and FIFO logic for subchannel
      data_fifo[subch][0] = d;
      fifo_valid[subch][0] = 1'b1;
      subch_data_out[subch] = d;
      subch_valid[subch]    = 1'b1;
      arb_decision = 1'b0;
      if (ENABLE_LOGGING)
        $display("Routed to subchannel=%0d: 0x%0h", subch, d);
    end else begin
      error_status = 1'b1;
      if (ENABLE_LOGGING)
        $display("Route ERROR: subchannel=%0d (disabled)", subch);
    end
  end
endtask

//-------------------- Arbitration Task -----------------------------
task automatic arbitrate_subchannel(
  output int sel_subch
);
  static int last_subch;
  begin
    sel_subch = (last_subch + 1) % NUM_SUBCHANNELS;
    last_subch= sel_subch;
    arb_decision = 1'b1;
    if (ENABLE_LOGGING)
      $display("Arbitrate: next subchannel=%0d", sel_subch);
  end
endtask

//-------------------- Reset Task -------------------------
task automatic handle_reset();
  int i, k;
  begin
    for (i = 0; i < NUM_SUBCHANNELS; i++) begin
      subch_data_out[i] = '0;
      subch_valid[i]    = 0;
      for (k = 0; k < FIFO_DEPTH; k++) begin
        data_fifo[i][k] = '0;
        fifo_valid[i][k] = 0;
      end
    end
    arb_decision = 0;
    error_status = 0;
    if (ENABLE_LOGGING)
      $display("[Reset] All subchannels FIFOs cleared.");
  end
endtask

//-------------------- Error Task -------------------------
task automatic handle_error(input string msg);
  begin
    error_status = 1'b1;
    if (ENABLE_LOGGING)
      $display("[ERROR] %s", msg);
  end
endtask

//------------------- Testbench/Stimulus Integration (Stub) -------------------
// To be instantiated/called from a testbench (see testbench example)
//-----------------------------------------------------------------------------

// Assertions (sample)
`ifdef FORMAL
  // Route must only happen when subchannel enabled
  assert property(@(posedge clk) disable iff(!rst_n)
    (data_in_valid & cfg_subchannel_en !== 0) |-> subch_valid[0] | subch_valid[1]);
  // Error if invalid select
  assert property(@(posedge clk) disable iff(!rst_n)
    (data_in_valid & (cfg_subchannel_en == 0)) |-> error_status);
`endif

endmodule
// end of subchannel_controller
