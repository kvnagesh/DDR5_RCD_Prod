//==================================================================================
// Module: synchronizers
// Description: Wide synchronizer library for DDR5 RCD CDC
//              Provides parameterized shift-register, handshake, reset synchronizers
// Author: Production Implementation
// Date: 2025-11-04
//==================================================================================

module synchronizers #(
  parameter int DATA_WIDTH = 1,   
  parameter int SYNC_STAGES = 2   // Number of synchronization stages (>=2 recommended)
) (
  input  logic                  clk_dst,   
  input  logic                  rst_n,     
  input  logic [DATA_WIDTH-1:0] data_in,   
  output logic [DATA_WIDTH-1:0] data_out   // Synchronized output
);

  // ========================================================================
  // Shift-register CDC synchronizer - minimize metastability
  // ========================================================================
  logic [SYNC_STAGES-1:0][DATA_WIDTH-1:0] sync_ff;

  always_ff @(posedge clk_dst or negedge rst_n) begin
    if (!rst_n) begin
      sync_ff <= '0;
    end else begin
      sync_ff[0] <= data_in;
      for (int i=1; i<SYNC_STAGES; i++) begin
        sync_ff[i] <= sync_ff[i-1];
      end
    end
  end

  assign data_out = sync_ff[SYNC_STAGES-1];

  // ========================================================================
  // Handshake synchronizer (CDC with request/ack protocol)
  // ========================================================================
  // Example:
  //   handshake_sync #(SYNC_STAGES) hs (.clk_dst(clk_dst), .rst_n(rst_n), .req_in(req_in), .ack_out(ack_out));

endmodule

// ========================================================================
// 2-stage synchronizer for single-bit CDC
// ========================================================================
module sync_2ff #(parameter int DATA_WIDTH=1) (
  input  logic                  clk_dst,
  input  logic                  rst_n,
  input  logic [DATA_WIDTH-1:0] data_in,
  output logic [DATA_WIDTH-1:0] data_out
);
  logic [DATA_WIDTH-1:0] ff1, ff2;
  always_ff @(posedge clk_dst or negedge rst_n) begin
    if (!rst_n) begin
      ff1 <= '0;
      ff2 <= '0;
    end else begin
      ff1 <= data_in;
      ff2 <= ff1;
    end
  end
  assign data_out = ff2;
endmodule

// ========================================================================
// 3-stage synchronizer for robust metastability tolerance
// ========================================================================
module sync_3ff #(parameter int DATA_WIDTH=1) (
  input  logic                  clk_dst,
  input  logic                  rst_n,
  input  logic [DATA_WIDTH-1:0] data_in,
  output logic [DATA_WIDTH-1:0] data_out
);
  logic [DATA_WIDTH-1:0] ff1, ff2, ff3;
  always_ff @(posedge clk_dst or negedge rst_n) begin
    if (!rst_n) begin
      ff1 <= '0;
      ff2 <= '0;
      ff3 <= '0;
    end else begin
      ff1 <= data_in;
      ff2 <= ff1;
      ff3 <= ff2;
    end
  end
  assign data_out = ff3;
endmodule

// ========================================================================
// Handshake CDC synchronizer: request/ack domain crossing
// ========================================================================
module sync_handshake (
  input  logic clk_dst,
  input  logic rst_n,
  input  logic req_in,
  output logic req_sync,
  output logic ack_out
);
  logic req_ff1, req_ff2;
  always_ff @(posedge clk_dst or negedge rst_n) begin
    if (!rst_n) begin
      req_ff1 <= 1'b0;
      req_ff2 <= 1'b0;
      ack_out <= 1'b0;
    end else begin
      req_ff1 <= req_in;
      req_ff2 <= req_ff1;
      ack_out <= req_ff2;
    end
  end
  assign req_sync = req_ff2;
endmodule

// ========================================================================
// Reset synchronizer: Synchronous reset signal crossing
// ========================================================================
module sync_reset (
  input  logic clk_dst,
  input  logic async_reset_n,
  output logic sync_reset_n
);
  logic r0, r1;
  always_ff @(posedge clk_dst or negedge async_reset_n) begin
    if (!async_reset_n) begin
      r0 <= 1'b0;
      r1 <= 1'b0;
    end else begin
      r0 <= 1'b1;
      r1 <= r0;
    end
  end
  assign sync_reset_n = r1;
endmodule

// ========================================================================
// Assertion: All synchronizer outputs shall stabilize after SYNC_STAGES cycles
// ========================================================================
// Example property for main synchronizer:
// assert_stable_sync: assert property (
//   @(posedge clk_dst) disable iff (!rst_n)
//   $stable(data_out) throughout [SYNC_STAGES:SYNC_STAGES+2]
// );
