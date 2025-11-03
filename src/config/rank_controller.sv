//==============================================================================
// File: rank_controller.sv
// Description: Multi-rank selection, address decode, chip select (CS), ODT control
//              Ready/valid configuration interface and timing-friendly FSM
// Author: Auto-generated for DDR5 RCD Project
// Date: November 2025
//==============================================================================

module rank_controller #(
  parameter int NUM_RANKS      = 2,
  parameter int ADDR_WIDTH     = 18,
  parameter int BANK_GROUPS    = 4,
  parameter int BANKS_PER_GRP  = 4
) (
  // Clock and reset
  input  logic                   clk,
  input  logic                   rst_n,

  // Configuration interface
  input  logic                   cfg_valid,
  output logic                   cfg_ready,
  input  logic [$clog2(NUM_RANKS)-1:0] cfg_rank_map [NUM_RANKS], // physical map
  input  logic [NUM_RANKS-1:0]   cfg_rank_enable,

  // Command/address interface
  input  logic                   cmd_valid,
  output logic                   cmd_ready,
  input  logic [ADDR_WIDTH-1:0]  cmd_addr,
  input  logic [BANK_GROUPS-1:0] cmd_bg,
  input  logic [$clog2(BANKS_PER_GRP)-1:0] cmd_ba,
  input  logic [$clog2(NUM_RANKS)-1:0]     cmd_rank,   // requested rank

  // RCD outputs per rank
  output logic [NUM_RANKS-1:0]   rcd_cs_n,
  output logic [NUM_RANKS-1:0]   rcd_odt,

  // Status
  output logic                   rank_sel_error,
  output logic                   rank_sel_done,
  output logic [NUM_RANKS-1:0]   active_rank_onehot
);

  //============================================================================
  // Local parameters and types
  //============================================================================
  typedef enum logic [2:0] {
    S_IDLE    = 3'b000,
    S_CFG     = 3'b001,
    S_DECODE  = 3'b010,
    S_DRIVE   = 3'b011,
    S_DONE    = 3'b100,
    S_ERROR   = 3'b101
  } state_t;

  state_t state_d, state_q;

  // Registers for configuration
  logic [$clog2(NUM_RANKS)-1:0] rank_map_q   [NUM_RANKS];
  logic [NUM_RANKS-1:0]         rank_en_q;

  // Command latching
  logic [ADDR_WIDTH-1:0]        addr_q;
  logic [BANK_GROUPS-1:0]       bg_q;
  logic [$clog2(BANKS_PER_GRP)-1:0] ba_q;
  logic [$clog2(NUM_RANKS)-1:0] rank_q;

  // One-hot rank select
  logic [NUM_RANKS-1:0]         rank_onehot;

  // Simple ODT policy: enable ODT for selected rank, off for others
  // Can be extended for multi-rank read/write turnarounds

  //============================================================================
  // Rank one-hot decoder
  //============================================================================
  always_comb begin
    rank_onehot = '0;
    if (rank_q < NUM_RANKS)
      rank_onehot[rank_map_q[rank_q]] = 1'b1; // apply physical map
  end

  //============================================================================
  // FSM - sequential
  //============================================================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state_q <= S_IDLE;
    end else begin
      state_q <= state_d;
    end
  end

  //============================================================================
  // FSM - combinational
  //============================================================================
  always_comb begin
    state_d = state_q;
    case (state_q)
      S_IDLE: begin
        if (cfg_valid && cfg_ready)       state_d = S_CFG;
        else if (cmd_valid && cmd_ready)  state_d = S_DECODE;
      end
      S_CFG: begin
        state_d = S_DONE;
      end
      S_DECODE: begin
        // Rank must be enabled and in range
        if ((rank_q >= NUM_RANKS) || !rank_en_q[rank_map_q[rank_q]])
          state_d = S_ERROR;
        else
          state_d = S_DRIVE;
      end
      S_DRIVE: begin
        state_d = S_DONE;
      end
      S_DONE: begin
        state_d = S_IDLE;
      end
      S_ERROR: begin
        // wait for cmd_valid to drop
        if (!cmd_valid)
          state_d = S_IDLE;
      end
      default: state_d = S_IDLE;
    endcase
  end

  //============================================================================
  // Input handshakes and latching
  //============================================================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      addr_q <= '0;
      bg_q   <= '0;
      ba_q   <= '0;
      rank_q <= '0;
    end else begin
      if (cmd_valid && cmd_ready) begin
        addr_q <= cmd_addr;
        bg_q   <= cmd_bg;
        ba_q   <= cmd_ba;
        rank_q <= cmd_rank;
      end
    end
  end

  // Configuration capture
  integer i;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (i=0; i<NUM_RANKS; i++) begin
        rank_map_q[i] <= i[$clog2(NUM_RANKS)-1:0];
      end
      rank_en_q <= {NUM_RANKS{1'b1}};
    end else begin
      if (cfg_valid && cfg_ready) begin
        for (i=0; i<NUM_RANKS; i++) begin
          rank_map_q[i] <= cfg_rank_map[i];
        end
        rank_en_q <= cfg_rank_enable;
      end
    end
  end

  //============================================================================
  // Outputs and handshakes
  //============================================================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      cfg_ready       <= 1'b1;
      cmd_ready       <= 1'b1;
      rcd_cs_n        <= {NUM_RANKS{1'b1}};
      rcd_odt         <= '0;
      rank_sel_error  <= 1'b0;
      rank_sel_done   <= 1'b0;
      active_rank_onehot <= '0;
    end else begin
      // Defaults
      cfg_ready       <= (state_q == S_IDLE);
      cmd_ready       <= (state_q == S_IDLE);
      rank_sel_done   <= 1'b0;

      case (state_q)
        S_CFG: begin
          rank_sel_done <= 1'b1;
        end
        S_DECODE: begin
          // nothing, decision in next state
        end
        S_DRIVE: begin
          // Drive CS and ODT based on selected rank
          rcd_cs_n <= ~rank_onehot; // active low CS
          rcd_odt  <= rank_onehot;  // simple ODT policy
          active_rank_onehot <= rank_onehot;
        end
        S_DONE: begin
          rank_sel_done <= 1'b1;
          rank_sel_error <= 1'b0;
        end
        S_ERROR: begin
          rcd_cs_n       <= {NUM_RANKS{1'b1}};
          rcd_odt        <= '0;
          active_rank_onehot <= '0;
          rank_sel_error <= 1'b1;
        end
        default: begin
          // hold
        end
      endcase
    end
  end

  // Optional: simple assertions for sanity
  `ifdef FORMAL
    // Only one rank can be active at a time
    assert property (@(posedge clk) disable iff (!rst_n) $onehot0(active_rank_onehot));
  `endif

endmodule

//==============================================================================
// End of rank_controller.sv
//==============================================================================
