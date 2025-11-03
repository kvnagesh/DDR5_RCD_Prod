//==============================================================================
// File: mode_registers.sv
// Description: Shadowed, readable/writable mode registers for DDR5 RCD settings
//              Simple APB-like handshake interface for config access
// Author: Auto-generated for DDR5 RCD Project
// Date: November 2025
//==============================================================================

module mode_registers #(
  parameter int NUM_REGS = 32,
  parameter int REG_WIDTH = 16
) (
  input  logic                 clk,
  input  logic                 rst_n,

  // Simple register access (ready/valid)
  input  logic                 req_valid,
  output logic                 req_ready,
  input  logic                 req_write,        // 1=write, 0=read
  input  logic [$clog2(NUM_REGS)-1:0] req_addr,
  input  logic [REG_WIDTH-1:0] req_wdata,
  input  logic [REG_WIDTH/8-1:0] req_wstrb,

  output logic                 resp_valid,
  input  logic                 resp_ready,
  output logic [REG_WIDTH-1:0] resp_rdata,
  output logic                 resp_error,

  // Shadow commit interface
  input  logic                 commit_valid,
  output logic                 commit_ready,

  // CSR Exposure (optional)
  output logic [REG_WIDTH-1:0] regs_shadow   [NUM_REGS],
  output logic [REG_WIDTH-1:0] regs_committed[NUM_REGS]
);

  typedef enum logic [1:0] { ST_IDLE, ST_ACCESS, ST_RESP } st_t;
  st_t st_d, st_q;

  // Shadow and committed arrays
  logic [REG_WIDTH-1:0] shadow   [NUM_REGS];
  logic [REG_WIDTH-1:0] committed[NUM_REGS];

  // Latches for access
  logic                 wren_q;
  logic [$clog2(NUM_REGS)-1:0] addr_q;
  logic [REG_WIDTH-1:0] wdata_q;
  logic [REG_WIDTH/8-1:0] wstrb_q;

  // Ready/valid
  assign req_ready    = (st_q == ST_IDLE);
  assign commit_ready = (st_q == ST_IDLE);

  // State machine
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) st_q <= ST_IDLE; else st_q <= st_d;
  end

  always_comb begin
    st_d = st_q;
    case (st_q)
      ST_IDLE: begin
        if (req_valid && req_ready) st_d = ST_ACCESS;
        else if (commit_valid && commit_ready) st_d = ST_RESP; // treat commit as quick op
      end
      ST_ACCESS: begin
        st_d = ST_RESP;
      end
      ST_RESP: begin
        if (resp_ready) st_d = ST_IDLE;
      end
      default: st_d = ST_IDLE;
    endcase
  end

  // Capture request
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      wren_q  <= 1'b0;
      addr_q  <= '0;
      wdata_q <= '0;
      wstrb_q <= '0;
    end else if (req_valid && req_ready) begin
      wren_q  <= req_write;
      addr_q  <= req_addr;
      wdata_q <= req_wdata;
      wstrb_q <= req_wstrb;
    end
  end

  // Register write (shadow only)
  genvar gi;
  generate
    for (gi=0; gi<NUM_REGS; gi++) begin : g_shadow
      always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
          shadow[gi] <= '0;
          committed[gi] <= '0;
        end else begin
          if (st_q == ST_ACCESS && wren_q && addr_q == gi[$clog2(NUM_REGS)-1:0]) begin
            // byte write enables
            for (int b=0; b<REG_WIDTH/8; b++) begin
              if (wstrb_q[b])
                shadow[gi][8*b +: 8] <= wdata_q[8*b +: 8];
            end
          end
          if (commit_valid && commit_ready) begin
            committed[gi] <= shadow[gi];
          end
        end
      end
      assign regs_shadow[gi]    = shadow[gi];
      assign regs_committed[gi] = committed[gi];
    end
  endgenerate

  // Read path
  logic [REG_WIDTH-1:0] read_mux;
  always_comb begin
    read_mux = '0;
    if (addr_q < NUM_REGS)
      read_mux = shadow[addr_q]; // reads reflect shadow contents
  end

  // Response
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      resp_valid <= 1'b0;
      resp_rdata <= '0;
      resp_error <= 1'b0;
    end else begin
      case (st_q)
        ST_ACCESS: begin
          resp_valid <= 1'b1;
          resp_error <= (addr_q >= NUM_REGS);
          if (!wren_q) resp_rdata <= read_mux; // read
        end
        ST_RESP: begin
          if (resp_ready) resp_valid <= 1'b0;
        end
        default: begin
          resp_valid <= 1'b0;
          resp_error <= 1'b0;
        end
      endcase
    end
  end

  // Simple sanity assertions
  `ifdef FORMAL
    assert property (@(posedge clk) disable iff (!rst_n) !(req_valid && commit_valid));
  `endif

endmodule

//==============================================================================
// End of mode_registers.sv
//==============================================================================
