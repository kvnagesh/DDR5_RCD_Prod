// ============================================================================
// File: register_map.sv
// Description: Register map module implementing DDR5 RCD register access with
//              robust read functionality, bit/bus mapping, and comprehensive
//              acknowledge (ack_o) handling for edge cases and hazards.
// ============================================================================

module register_map #(
  parameter ADDR_WIDTH = 5,      // Register address width (32 registers max)
  parameter DATA_WIDTH = 8,      // Register data width (8-bit)
  parameter TIMEOUT_CYCLES = 16  // Timeout cycles for stalled transactions
) (
  // Clock and Reset
  input  logic                    clk_i,          // System clock
  input  logic                    rst_ni,         // Active-low asynchronous reset
  
  // Register Access Interface (Master)
  input  logic [ADDR_WIDTH-1:0]   reg_addr,       // Register address input
  input  logic                    reg_rd_req,     // Register read request
  input  logic                    reg_wr_req,     // Register write request
  input  logic [DATA_WIDTH-1:0]   reg_wr_data,    // Register write data
  output logic [DATA_WIDTH-1:0]   reg_rd_data,    // Register read data output
  output logic                    ack_o,          // Acknowledge output
  output logic                    err_o,          // Error flag for invalid access
  
  // External Output Signals (mapped from register bits)
  output logic                    ctrl_enable,    // Control enable signal
  output logic [3:0]              status_flags,   // Status flags [3:0]
  output logic [7:0]              mode_config,    // Mode configuration [7:0]
  output logic                    interrupt_mask, // Interrupt mask bit
  
  // Write-back Signals
  output logic                    wb_valid,       // Write-back valid flag
  output logic [ADDR_WIDTH-1:0]   wb_addr,        // Write-back address
  output logic [DATA_WIDTH-1:0]   wb_data         // Write-back data
);

  // ========================================================================
  // Register File Definition
  // ========================================================================
  logic [DATA_WIDTH-1:0] register_file [(1 << ADDR_WIDTH)-1:0];
  
  // Register Address Map
  localparam REG_CTRL      = 5'h00;  // Control register
  localparam REG_STATUS    = 5'h01;  // Status register (read-only)
  localparam REG_MODE      = 5'h02;  // Mode configuration register
  localparam REG_INT_MASK  = 5'h03;  // Interrupt mask register
  localparam REG_TEST      = 5'h1F;  // Test register (last addressable)
  
  // ========================================================================
  // Internal Signals
  // ========================================================================
  logic [DATA_WIDTH-1:0] rd_data_next, rd_data_curr;
  logic [ADDR_WIDTH-1:0] addr_curr, addr_next;
  logic                  rd_req_curr, rd_req_next;
  logic                  wr_req_curr, wr_req_next;
  logic                  valid_addr;
  logic                  simultaneous_access; // Simultaneous read + write
  logic                  addr_mismatch;       // Addr mismatch between read/write
  logic [$clog2(TIMEOUT_CYCLES)-1:0] timeout_counter;
  logic                  timeout_active;
  logic                  ack_stall;
  logic                  hazard_detected;
  
  // ========================================================================
  // Address Validation
  // ========================================================================
  assign valid_addr = (reg_addr <= REG_TEST);
  
  // ========================================================================
  // Hazard and Collision Detection
  // ========================================================================
  assign simultaneous_access = reg_rd_req & reg_wr_req;
  assign addr_mismatch = (reg_addr != addr_curr) & (rd_req_curr | wr_req_curr);
  assign hazard_detected = simultaneous_access | addr_mismatch;
  
  // ========================================================================
  // Sequential Logic - State Management
  // ========================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      addr_curr      <= '0;
      rd_req_curr    <= 1'b0;
      wr_req_curr    <= 1'b0;
      rd_data_curr   <= '0;
      timeout_counter <= '0;
      timeout_active  <= 1'b0;
    end else begin
      addr_curr      <= addr_next;
      rd_req_curr    <= rd_req_next;
      wr_req_curr    <= wr_req_next;
      rd_data_curr   <= rd_data_next;
      
      // Timeout counter logic
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
  
  // ========================================================================
  // Combinational Logic - Read Data Path
  // ========================================================================
  always_comb begin
    rd_data_next = register_file[reg_addr];
    
    // Handle special read cases (read-only registers, etc.)
    case (reg_addr)
      REG_STATUS: begin
        // Status register - composed of internal signals
        rd_data_next = {status_flags, 4'h0};
      end
      default: begin
        rd_data_next = register_file[reg_addr];
      end
    endcase
  end
  
  assign reg_rd_data = rd_data_next;
  
  // ========================================================================
  // Write Path and Register Updates
  // ========================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      // Initialize all registers
      for (int i = 0; i < (1 << ADDR_WIDTH); i++) begin
        register_file[i] <= '0;
      end
    end else if (reg_wr_req & ~hazard_detected & valid_addr) begin
      // Write only if valid address, no hazards, and write request active
      register_file[reg_addr] <= reg_wr_data;
    end
  end
  
  // ========================================================================
  // Robust Acknowledge (ack_o) Generation with Edge Case Handling
  // ========================================================================
  always_comb begin
    ack_o = 1'b0;
    ack_stall = 1'b0;
    
    // Edge Case 1: Invalid address - NACK immediately
    if ((reg_rd_req | reg_wr_req) & ~valid_addr) begin
      ack_o = 1'b0;
    end
    // Edge Case 2: Simultaneous read and write to same address - STALL
    else if (simultaneous_access & (reg_addr == addr_curr)) begin
      ack_o = 1'b0;
      ack_stall = 1'b1;
    end
    // Edge Case 3: Address mismatch (new request while previous pending) - STALL
    else if (addr_mismatch) begin
      ack_o = 1'b0;
      ack_stall = 1'b1;
    end
    // Edge Case 4: Timeout detected - NACK after timeout
    else if (timeout_active) begin
      ack_o = 1'b0;
    end
    // Edge Case 5: Write to read-only register - NACK
    else if (reg_wr_req & (reg_addr == REG_STATUS)) begin
      ack_o = 1'b0;
    end
    // Normal case: Valid read or write request
    else if ((reg_rd_req | reg_wr_req) & valid_addr & ~hazard_detected) begin
      ack_o = 1'b1;
    end
  end
  
  // ========================================================================
  // Error Flag Generation
  // ========================================================================
  always_comb begin
    err_o = 1'b0;
    
    if (reg_rd_req | reg_wr_req) begin
      // Error conditions
      if (~valid_addr) begin
        err_o = 1'b1;  // Invalid address
      end
      else if (simultaneous_access) begin
        err_o = 1'b1;  // Simultaneous read and write attempt
      end
      else if (timeout_active) begin
        err_o = 1'b1;  // Transaction timeout
      end
      else if (reg_wr_req & (reg_addr == REG_STATUS)) begin
        err_o = 1'b1;  // Write to read-only register
      end
    end
  end
  
  // ========================================================================
  // Next-State Logic for Address and Request Tracking
  // ========================================================================
  always_comb begin
    addr_next   = addr_curr;
    rd_req_next = rd_req_curr;
    wr_req_next = wr_req_curr;
    
    if (reg_rd_req | reg_wr_req) begin
      // Latch the current request
      addr_next   = reg_addr;
      rd_req_next = reg_rd_req;
      wr_req_next = reg_wr_req;
    end else if (ack_o) begin
      // Clear request after acknowledgement
      rd_req_next = 1'b0;
      wr_req_next = 1'b0;
      addr_next   = '0;
    end
  end
  
  // ========================================================================
  // Bit/Bus Mapping - Map Register Contents to External Outputs
  // ========================================================================
  always_comb begin
    // Extract CTRL register bits to external signals
    ctrl_enable   = register_file[REG_CTRL][0];       // Bit [0]
    interrupt_mask = register_file[REG_INT_MASK][0];  // Bit [0]
    
    // Extract MODE register bits to mode_config output
    mode_config   = register_file[REG_MODE][7:0];     // All bits
    
    // Status flags are synthesized from internal state
    // Bit [3]: Timeout error
    // Bit [2]: Access error
    // Bit [1]: Write acknowledge
    // Bit [0]: Read acknowledge
    status_flags[3] = timeout_active;
    status_flags[2] = err_o;
    status_flags[1] = ack_o & wr_req_curr;
    status_flags[0] = ack_o & rd_req_curr;
  end
  
  // ========================================================================
  // Write-Back Interface for Register Updates
  // ========================================================================
  always_comb begin
    wb_valid = 1'b0;
    wb_addr  = '0;
    wb_data  = '0;
    
    if (ack_o & reg_wr_req) begin
      // Signal valid write-back when write is acknowledged
      wb_valid = 1'b1;
      wb_addr  = reg_addr;
      wb_data  = reg_wr_data;
    end
  end
  
endmodule
// ============================================================================
// End of register_map.sv
// ============================================================================
