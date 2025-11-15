//==================================================================================
// Testbench: signal_router_tb
// Description: Simple stimulus for signal_router and subchannel_controller
//==================================================================================
module signal_router_tb();
  import "DPI-C" context task sv_assert(input bit cond, input string msg);
  parameter DQ_WIDTH      = 8;
  parameter CA_WIDTH      = 7;
  parameter DQS_WIDTH     = 1;
  parameter CK_WIDTH      = 1;
  parameter NUM_RANKS     = 2;
  parameter NUM_CHANNELS  = 2;
  parameter FIFO_DEPTH    = 8;

  logic clk;
  logic rst_n;
  logic [DQ_WIDTH-1:0] host_dq;
  logic [CA_WIDTH-1:0] host_ca;
  logic host_dqs, host_ck;
  logic host_pkt_valid;
  logic [NUM_RANKS-1:0] cfg_rank_en;
  logic [NUM_CHANNELS-1:0] cfg_channel_en;
  logic cfg_gang_mode;
  logic route_ack, error_status;
  
  // DUT Instance
  signal_router #(
      .DQ_WIDTH(DQ_WIDTH), .CA_WIDTH(CA_WIDTH), .DQS_WIDTH(DQS_WIDTH), .CK_WIDTH(CK_WIDTH),
      .NUM_RANKS(NUM_RANKS), .NUM_CHANNELS(NUM_CHANNELS), .FIFO_DEPTH(FIFO_DEPTH))
      dut (.*);

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  initial begin
    rst_n = 0;
    #20;
    rst_n = 1;
  end

  initial begin
    // Stimulus -- Enable all ranks/channels
    cfg_rank_en = 2'b11; cfg_channel_en = 2'b11; cfg_gang_mode = 0;
    @(posedge rst_n);
    repeat (3) begin
      host_dq = $random;
      host_ca = $random;
      host_dqs = $random;
      host_ck = $random;
      host_pkt_valid = 1;
      @(posedge clk);
    end
    // Error test -- disable all
    cfg_rank_en = 2'b00; cfg_channel_en = 2'b00;
    host_pkt_valid = 1;
    host_dq = 8'hA5;
    @(posedge clk);
    sv_assert(error_status, "Expected routing error on disabled ranks/channels");
    // Reset test
    rst_n = 0;
    @(posedge clk);
    rst_n = 1;
    @(posedge clk);
    $display("TB done");
    $finish;
  end
endmodule
//==================================================================================
// Testbench: subchannel_controller_tb (Stub)
//==================================================================================
module subchannel_controller_tb();
  parameter SUBCHANNEL_WIDTH = 40;
  parameter NUM_SUBCHANNELS = 2;
  parameter DATA_WIDTH = 80;
  parameter FIFO_DEPTH = 8;

  logic clk;
  logic rst_n;
  logic [NUM_SUBCHANNELS-1:0] cfg_subchannel_en;
  logic data_in_valid;
  logic [DATA_WIDTH-1:0] data_in;

  logic [SUBCHANNEL_WIDTH-1:0] subch_data_out[NUM_SUBCHANNELS];
  logic subch_valid[NUM_SUBCHANNELS];
  logic error_status;

  subchannel_controller #(
      .SUBCHANNEL_WIDTH(SUBCHANNEL_WIDTH),
      .NUM_SUBCHANNELS(NUM_SUBCHANNELS), .DATA_WIDTH(DATA_WIDTH), .FIFO_DEPTH(FIFO_DEPTH))
      dut (.*);

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  initial begin
    rst_n = 0;
    #10;
    rst_n = 1;
  end

  initial begin
    cfg_subchannel_en = 2'b11;
    data_in = 80'hFFEEDDCCBBAA99887766;
    data_in_valid = 1;
    @(posedge clk);
    // Error test
    cfg_subchannel_en = 2'b00;
    data_in = 80'hAABBCC;
    data_in_valid = 1;
    @(posedge clk);
    $display("TB done");
    $finish;
  end
endmodule
//==================================================================================
