// ============================================================================
// File: register_map.sv
// Description: DDR5 RCD register map w/ parameterized, future-proof field mapping
//              for wider address/command fields as per updated DDR5 spec.
//              All bus mapping/port integration logic is expandable & documented.
// ============================================================================
module register_map #(
  parameter ADDR_WIDTH      = 8,    
  parameter CMD_WIDTH       = 24,   
  parameter DATA_WIDTH      = 16,   
  parameter TIMEOUT_CYCLES  = 32    // Timeout cycles, scalable
)(
  // Clock and Reset
  input  logic                      clk_i,
  input  logic                      rst_ni,

  // Register Access Interface (Master)
  input  logic [ADDR_WIDTH-1:0]     reg_addr,
  input  logic                      reg_rd_req,
  input  logic                      reg_wr_req,
  input  logic [DATA_WIDTH-1:0]     reg_wr_data,
  output logic [DATA_WIDTH-1:0]     reg_rd_data,
  output logic                      ack_o,
  output logic                      err_o,

  // Command/Address Bus Interface (parameterized for future/fuller bus mapping)
  output logic [CMD_WIDTH-1:0]      cmd_bus_o,   
  output logic [ADDR_WIDTH-1:0]     addr_bus_o,
  
  // External Output Signals (mapped from register fields)
  output logic                      ctrl_enable,
  output logic [7:0]                status_flags,   
  output logic [DATA_WIDTH-1:0]     mode_config,
  output logic                      interrupt_mask,

  // Write-back Signals
  output logic                      wb_valid,
  output logic [ADDR_WIDTH-1:0]     wb_addr,
  output logic [DATA_WIDTH-1:0]     wb_data
);
  // ========================================================================
  // Register File for All Addressable Registers, Fully Parameterized
  // ========================================================================
  logic [DATA_WIDTH-1:0] register_file [(1 << ADDR_WIDTH)-1:0];

  //----------------------------------------------------
  // Extend/Documented Address Map
  localparam REG_CTRL      = {ADDR_WIDTH{1'b0}};  // Control register @0
  localparam REG_STATUS    = {{(ADDR_WIDTH-1){1'b0}}, 1'b1}; // Status register @1
  localparam REG_MODE      = {{(ADDR_WIDTH-1){1'b0}}, 1'b0, 1'b1}; // Mode conf
  localparam REG_CMD       = {{(ADDR_WIDTH-2){1'b0}}, 2'b10}; // Dedicated CMD
  localparam REG_INT_MASK  = {{(ADDR_WIDTH-3){1'b0}}, 3'b011}; // Int Mask
  localparam REG_TEST      = {ADDR_WIDTH{1'b1}};  // Last valid address

  //-----------------------
  // Valid Address Decoding
  assign addr_bus_o = reg_addr;
  wire valid_addr = (reg_addr <= REG_TEST);
  //-----------------------
  // State/Hazard/Timeout (Keep logic similar, parameterized for width)
  logic [ADDR_WIDTH-1:0]   addr_curr, addr_next;
  logic                    rd_req_curr, rd_req_next;
  logic                    wr_req_curr, wr_req_next;
  logic                    simultaneous_access;
  logic                    addr_mismatch;
  logic [DATA_WIDTH-1:0]   rd_data_next, rd_data_curr;
  logic [$clog2(TIMEOUT_CYCLES)-1:0] timeout_counter;
  logic                    timeout_active;
  logic                    hazard_detected;
  //-----------------------
  assign simultaneous_access = reg_rd_req & reg_wr_req;
  assign addr_mismatch       = (reg_addr != addr_curr) & (rd_req_curr | wr_req_curr);
  assign hazard_detected     = simultaneous_access | addr_mismatch;
  //-----------------------
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      addr_curr       <= '0;
      rd_req_curr     <= 1'b0;
      wr_req_curr     <= 1'b0;
      rd_data_curr    <= '0;
      timeout_counter <= '0;
      timeout_active  <= 1'b0;
    end else begin
      addr_curr       <= addr_next;
      rd_req_curr     <= rd_req_next;
      wr_req_curr     <= wr_req_next;
      rd_data_curr    <= rd_data_next;
      if (reg_rd_req | reg_wr_req) begin
        if (timeout_counter == TIMEOUT_CYCLES - 1) begin
          timeout_active  <= 1'b1;
          timeout_counter <= '0;
        end else begin
          timeout_counter <= timeout_counter + 1'b1;
        end
      end else begin
        timeout_active  <= 1'b0;
        timeout_counter <= '0;
      end
    end
  end
  //-----------------------
  // Combinational logic for Read Data
  always_comb begin
    rd_data_next = register_file[reg_addr];
    case (reg_addr)
      REG_STATUS:   rd_data_next = {status_flags, 4'h0};
      REG_CMD:      rd_data_next = cmd_bus_o[DATA_WIDTH-1:0];
      default:      rd_data_next = register_file[reg_addr];
    endcase
  end
  assign reg_rd_data = rd_data_next;
  //-----------------------
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni)
      for (int i=0;i<(1<<ADDR_WIDTH);i++) register_file[i] <= '0;
    else if (reg_wr_req & ~hazard_detected & valid_addr)
      register_file[reg_addr] <= reg_wr_data;
  end
  //-----------------------
  // Ack/Error
  always_comb begin
    ack_o = 1'b0;
    if      ((reg_rd_req | reg_wr_req) & ~valid_addr)         ack_o = 1'b0;
    else if (simultaneous_access & (reg_addr == addr_curr))   ack_o = 1'b0;
    else if (addr_mismatch)                                   ack_o = 1'b0;
    else if (timeout_active)                                  ack_o = 1'b0;
    else if (reg_wr_req & (reg_addr == REG_STATUS))           ack_o = 1'b0;
    else if ((reg_rd_req | reg_wr_req) & valid_addr & ~hazard_detected) ack_o = 1'b1;
  end

  always_comb begin
    err_o = 1'b0;
    if      (~valid_addr)                err_o = 1'b1;
    else if (simultaneous_access)        err_o = 1'b1;
    else if (timeout_active)             err_o = 1'b1;
    else if (reg_wr_req & (reg_addr == REG_STATUS)) err_o = 1'b1;
  end
  //-----------------------
  always_comb begin
    addr_next   = addr_curr;
    rd_req_next = rd_req_curr;
    wr_req_next = wr_req_curr;
    if (reg_rd_req | reg_wr_req) begin
      addr_next   = reg_addr;
      rd_req_next = reg_rd_req;
      wr_req_next = reg_wr_req;
    end else if (ack_o) begin
      rd_req_next = 1'b0;
      wr_req_next = 1'b0;
      addr_next   = '0;
    end
  end
  //-----------------------
  // Expanded Bit/Bus Mapping for Full-Width Support
  always_comb begin
    ctrl_enable    = register_file[REG_CTRL][0];
    interrupt_mask = register_file[REG_INT_MASK][0];
    mode_config    = register_file[REG_MODE][DATA_WIDTH-1:0];
    // status_flags: [7] future use | [6] reserved | [5] reserved | [4] reserved |
    //  [3]: Timeout | [2]: Error | [1]: Write ACK | [0]: Read ACK
    status_flags[3] = timeout_active;
    status_flags[2] = err_o;
    status_flags[1] = ack_o & wr_req_curr;
    status_flags[0] = ack_o & rd_req_curr;
    status_flags[7:4] = 4'b0; // expandable for future flags
    cmd_bus_o       = register_file[REG_CMD][CMD_WIDTH-1:0]; // full command field mapping
  end
  //-----------------------
  always_comb begin
    wb_valid = 1'b0;
    wb_addr  = '0;
    wb_data  = '0;
    if (ack_o & reg_wr_req) begin
      wb_valid = 1'b1;
      wb_addr  = reg_addr;
      wb_data  = reg_wr_data;
    end
  end
endmodule
// ============================================================================
// End of future-proof, fully parameterized register_map.sv
// ============================================================================
