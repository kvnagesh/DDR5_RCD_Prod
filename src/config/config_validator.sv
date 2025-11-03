//==============================================================================
// File: config_validator.sv
// Description: Configuration validator for DDR5 RCD config settings.
//              Checks width/rank/register combinations and flags errors.
// Author: Auto-generated for DDR5 RCD Project
// Date: November 2025
//==============================================================================

module config_validator #(
  parameter int MAX_RANKS = 4,
  parameter int MAX_CHANNELS = 2
) (
  input  logic                     clk,
  input  logic                     rst_n,

  // Inputs to validate
  input  logic                     val_valid,
  output logic                     val_ready,

  // Width settings
  input  logic                     width_is_x8,       // 1=x8, 0=x4
  input  logic [1:0]               channel_mask,      // up to 2 channels

  // Rank settings
  input  logic [$clog2(MAX_RANKS)-1:0] num_ranks,
  input  logic [MAX_RANKS-1:0]         rank_enable,

  // Mode register bank summary (optional): pass key fields for sanity
  input  logic [15:0] mr0,  // example fields like BL, CL etc if needed
  input  logic [15:0] mr1,

  // Result
  output logic                     resp_valid,
  input  logic                     resp_ready,
  output logic                     cfg_ok,
  output logic [15:0]              error_code
);

  // Error code map
  localparam logic [15:0] ERR_NONE           = 16'h0000;
  localparam logic [15:0] ERR_ZERO_CHANNELS  = 16'h0001;
  localparam logic [15:0] ERR_BAD_WIDTH_MASK = 16'h0002;
  localparam logic [15:0] ERR_RANK_RANGE     = 16'h0003;
  localparam logic [15:0] ERR_NO_RANK_EN     = 16'h0004;
  localparam logic [15:0] ERR_MR_ILLEGAL     = 16'h0005;

  typedef enum logic [1:0] { V_IDLE, V_CHECK, V_RESP } vstate_t;
  vstate_t vs_d, vs_q;

  // Handshakes
  assign val_ready = (vs_q == V_IDLE);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) vs_q <= V_IDLE; else vs_q <= vs_d;
  end

  // Latch inputs
  logic                     width_is_x8_q;
  logic [1:0]               channel_mask_q;
  logic [$clog2(MAX_RANKS)-1:0] num_ranks_q;
  logic [MAX_RANKS-1:0]     rank_enable_q;
  logic [15:0]              mr0_q, mr1_q;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      width_is_x8_q  <= 1'b0;
      channel_mask_q <= '0;
      num_ranks_q    <= '0;
      rank_enable_q  <= '0;
      mr0_q          <= '0;
      mr1_q          <= '0;
    end else if (val_valid && val_ready) begin
      width_is_x8_q  <= width_is_x8;
      channel_mask_q <= channel_mask;
      num_ranks_q    <= num_ranks;
      rank_enable_q  <= rank_enable;
      mr0_q          <= mr0;
      mr1_q          <= mr1;
    end
  end

  // Checks
  logic [15:0] err_d, err_q;
  logic        ok_d, ok_q;

  always_comb begin
    vs_d  = vs_q;
    err_d = err_q;
    ok_d  = ok_q;

    case (vs_q)
      V_IDLE: begin
        if (val_valid && val_ready) begin
          vs_d  = V_CHECK;
          err_d = ERR_NONE;
        end
      end
      V_CHECK: begin
        err_d = ERR_NONE;

        // Rule 1: channel mask cannot be zero
        if (channel_mask_q == 2'b00) begin
          err_d = ERR_ZERO_CHANNELS;
        end

        // Rule 2: width x8 implies both channels may be supported but mask must be within MAX_CHANNELS
        if (&channel_mask_q === 1'bx) begin
          err_d = ERR_BAD_WIDTH_MASK; // basic X-prop catch for synthesis safe
        end

        // Rule 3: num_ranks must be 1..MAX_RANKS
        if ((num_ranks_q == '0) || (num_ranks_q > MAX_RANKS[$clog2(MAX_RANKS)-1:0])) begin
          err_d = ERR_RANK_RANGE;
        end

        // Rule 4: at least one rank enabled
        if (rank_enable_q == '0) begin
          err_d = ERR_NO_RANK_EN;
        end

        // Rule 5: example MR legality check (placeholder): disallow mr0[3:0]==0 when x8
        if (width_is_x8_q && (mr0_q[3:0] == 4'h0)) begin
          err_d = ERR_MR_ILLEGAL;
        end

        vs_d = V_RESP;
      end
      V_RESP: begin
        if (resp_ready) vs_d = V_IDLE;
      end
      default: vs_d = V_IDLE;
    endcase

    ok_d = (err_d == ERR_NONE);
  end

  // Outputs
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      resp_valid <= 1'b0;
      cfg_ok     <= 1'b0;
      error_code <= ERR_NONE;
    end else begin
      case (vs_q)
        V_CHECK: begin
          resp_valid <= 1'b1;
          cfg_ok     <= (err_d == ERR_NONE);
          error_code <= err_d;
        end
        V_RESP: begin
          if (resp_ready) resp_valid <= 1'b0;
        end
        default: begin
          resp_valid <= 1'b0;
        end
      endcase
    end
  end

  // Assertions
  `ifdef FORMAL
    // No X on control
    assert property (@(posedge clk) disable iff (!rst_n) !$isunknown({val_valid, val_ready}));
  `endif

endmodule

//==============================================================================
// End of config_validator.sv
//==============================================================================
