// =====================================================================
// Error Logging Register Module with Hardware Interface
// =====================================================================
// Description: Hardware logging module with register-mapped error and
//              status counters for debug and firmware access. Provides
//              comprehensive error tracking with configurable logging.
//
// Register Map:
//   0x00 - Error Status Register (ERR_STATUS)
//   0x04 - ECC Error Count (ECC_ERR_CNT)
//   0x08 - CRC Error Count (CRC_ERR_CNT)
//   0x0C - Parity Error Count (PAR_ERR_CNT)
//   0x10 - Single Bit Error Count (SBE_CNT)
//   0x14 - Double Bit Error Count (DBE_CNT)
//   0x18 - Last Error Address (LAST_ERR_ADDR)
//   0x1C - Error Control Register (ERR_CTRL)
//   0x20 - Error Interrupt Enable (ERR_INT_EN)
//   0x24 - Error Interrupt Status (ERR_INT_STA)
//
// Author: Error Logging System
// Date: 2025-11-04
// =====================================================================

module error_log_reg #(
  parameter int ADDR_WIDTH = 5,        // Register address width
  parameter int DATA_WIDTH = 32,       // Register data width
  parameter int ERR_FIFO_DEPTH = 16    // Error log FIFO depth
) (
  // Clock and Reset
  input  logic                clk,
  input  logic                rst_n,
  input  logic                en,
  
  // Error Inputs (from detection modules)
  input  logic                ecc_err_in,     // ECC error flag
  input  logic [15:0]         ecc_err_cnt_in, // ECC error count
  input  logic                ecc_sbe_in,     // Single-bit error
  input  logic                ecc_dbe_in,     // Double-bit error
  
  input  logic                crc_err_in,     // CRC error flag
  input  logic [15:0]         crc_err_cnt_in, // CRC error count
  
  input  logic                par_err_in,     // Parity error flag
  input  logic [15:0]         par_err_cnt_in, // Parity error count
  
  input  logic [31:0]         err_addr_in,    // Error address
  input  logic [7:0]          err_position_in,// Error position
  
  // Firmware Register Interface (APB-like)
  input  logic [ADDR_WIDTH-1:0] reg_addr,
  input  logic                  reg_write,
  input  logic [DATA_WIDTH-1:0]  reg_write_data,
  output logic [DATA_WIDTH-1:0]  reg_read_data,
  output logic                   reg_read_valid,
  
  // Status and Control Outputs
  output logic                err_status_valid,
  output logic                any_error_detected,
  output logic [7:0]          error_type_flags, // [0]=ECC, [1]=CRC, [2]=PAR
  output logic                interrupt_out,    // Error interrupt
  output logic [15:0]         total_error_cnt   // Total errors across all types
);

  // ===================================================================
  // Register Definitions
  // ===================================================================
  localparam int REG_STATUS = 5'h00;      // 0x00 - Error Status
  localparam int REG_ECC_CNT = 5'h01;     // 0x04 - ECC Error Count
  localparam int REG_CRC_CNT = 5'h02;     // 0x08 - CRC Error Count
  localparam int REG_PAR_CNT = 5'h03;     // 0x0C - Parity Error Count
  localparam int REG_SBE_CNT = 5'h04;     // 0x10 - SBE Count
  localparam int REG_DBE_CNT = 5'h05;     // 0x14 - DBE Count
  localparam int REG_ERR_ADDR = 5'h06;    // 0x18 - Last Error Address
  localparam int REG_CTRL = 5'h07;        // 0x1C - Control
  localparam int REG_INT_EN = 5'h08;      // 0x20 - Interrupt Enable
  localparam int REG_INT_STA = 5'h09;     // 0x24 - Interrupt Status
  
  // ===================================================================
  // Internal Registers
  // ===================================================================
  logic [31:0] reg_err_status;            // Error status bits
  logic [31:0] reg_ecc_err_count;
  logic [31:0] reg_crc_err_count;
  logic [31:0] reg_par_err_count;
  logic [31:0] reg_sbe_count;
  logic [31:0] reg_dbe_count;
  logic [31:0] reg_last_err_addr;
  logic [31:0] reg_err_ctrl;
  logic [31:0] reg_int_enable;
  logic [31:0] reg_int_status;
  logic [7:0]  reg_err_type_flags;       // Error type indicators
  
  // ===================================================================
  // Error Type Detection
  // ===================================================================
  always_comb begin
    reg_err_type_flags[0] = ecc_err_in;  // ECC error detected
    reg_err_type_flags[1] = crc_err_in;  // CRC error detected
    reg_err_type_flags[2] = par_err_in;  // Parity error detected
    reg_err_type_flags[3] = ecc_sbe_in;  // Single-bit error
    reg_err_type_flags[4] = ecc_dbe_in;  // Double-bit error
    reg_err_type_flags[7:5] = 3'b000;    // Reserved
    
    any_error_detected = |reg_err_type_flags[2:0];
    error_type_flags = reg_err_type_flags;
  end
  
  // ===================================================================
  // Error Status Register Update
  // ===================================================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      reg_err_status <= 32'h00000000;
      reg_ecc_err_count <= 32'h00000000;
      reg_crc_err_count <= 32'h00000000;
      reg_par_err_count <= 32'h00000000;
      reg_sbe_count <= 32'h00000000;
      reg_dbe_count <= 32'h00000000;
      reg_last_err_addr <= 32'h00000000;
      reg_int_status <= 32'h00000000;
    end else if (en) begin
      // Update error counts
      if (ecc_err_in) begin
        reg_ecc_err_count <= ecc_err_cnt_in;
        reg_err_status[0] <= 1'b1;
        if (ecc_sbe_in) reg_sbe_count <= reg_sbe_count + 1;
        if (ecc_dbe_in) reg_dbe_count <= reg_dbe_count + 1;
      end
      
      if (crc_err_in) begin
        reg_crc_err_count <= crc_err_cnt_in;
        reg_err_status[1] <= 1'b1;
      end
      
      if (par_err_in) begin
        reg_par_err_count <= par_err_cnt_in;
        reg_err_status[2] <= 1'b1;
      end
      
      // Update error address
      if (any_error_detected) begin
        reg_last_err_addr <= err_addr_in;
        reg_err_status[31:24] <= err_position_in;
      end
      
      // Update interrupt status based on error and enable settings
      if (reg_int_enable[0] && ecc_err_in) reg_int_status[0] <= 1'b1;
      if (reg_int_enable[1] && crc_err_in) reg_int_status[1] <= 1'b1;
      if (reg_int_enable[2] && par_err_in) reg_int_status[2] <= 1'b1;
    end
  end
  
  // ===================================================================
  // Firmware Register Read Interface
  // ===================================================================
  always_comb begin
    reg_read_valid = 1'b0;
    reg_read_data = 32'h00000000;
    
    if (reg_write == 1'b0) begin  // Read operation
      reg_read_valid = 1'b1;
      case (reg_addr)
        REG_STATUS:   reg_read_data = reg_err_status;
        REG_ECC_CNT:  reg_read_data = reg_ecc_err_count;
        REG_CRC_CNT:  reg_read_data = reg_crc_err_count;
        REG_PAR_CNT:  reg_read_data = reg_par_err_count;
        REG_SBE_CNT:  reg_read_data = reg_sbe_count;
        REG_DBE_CNT:  reg_read_data = reg_dbe_count;
        REG_ERR_ADDR: reg_read_data = reg_last_err_addr;
        REG_CTRL:     reg_read_data = reg_err_ctrl;
        REG_INT_EN:   reg_read_data = reg_int_enable;
        REG_INT_STA:  reg_read_data = reg_int_status;
        default:      reg_read_data = 32'h00000000;
      endcase
    end
  end
  
  // ===================================================================
  // Firmware Register Write Interface
  // ===================================================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      reg_int_enable <= 32'h00000000;
      reg_err_ctrl <= 32'h00000000;
    end else if (en && reg_write) begin
      case (reg_addr)
        REG_CTRL: begin
          // Control register - bit 0: reset counters
          if (reg_write_data[0]) begin
            reg_ecc_err_count <= 32'h00000000;
            reg_crc_err_count <= 32'h00000000;
            reg_par_err_count <= 32'h00000000;
            reg_sbe_count <= 32'h00000000;
            reg_dbe_count <= 32'h00000000;
            reg_err_status <= 32'h00000000;
          end
          reg_err_ctrl <= reg_write_data;
        end
        REG_INT_EN: begin
          // Interrupt enable register
          reg_int_enable <= reg_write_data;
        end
        REG_INT_STA: begin
          // Interrupt status register - write clears bits
          reg_int_status <= reg_int_status & ~reg_write_data;
        end
        default: begin
          // Other registers are read-only
        end
      endcase
    end
  end
  
  // ===================================================================
  // Interrupt Generation
  // ===================================================================
  assign interrupt_out = |reg_int_status;
  
  // ===================================================================
  // Total Error Count (for status monitoring)
  // ===================================================================
  logic [15:0] total_errors;
  always_comb begin
    total_errors = reg_ecc_err_count[15:0] + 
                   reg_crc_err_count[15:0] + 
                   reg_par_err_count[15:0];
  end
  
  assign total_error_cnt = total_errors;
  assign err_status_valid = |reg_err_status;

endmodule

// =====================================================================
// Error Logger with FIFO - Advanced version for detailed error tracking
// =====================================================================
module error_log_fifo #(
  parameter int FIFO_DEPTH = 16,
  parameter int DATA_WIDTH = 32
) (
  input  logic                clk,
  input  logic                rst_n,
  input  logic                err_valid,
  input  logic [DATA_WIDTH-1:0] err_data,  // Error details packed
  
  output logic [DATA_WIDTH-1:0] err_read_data,
  output logic                err_fifo_full,
  output logic                err_fifo_empty,
  output logic [7:0]          err_fifo_count,
  
  input  logic                err_fifo_read
);

  logic [DATA_WIDTH-1:0] fifo_memory [FIFO_DEPTH-1:0];
  logic [7:0] fifo_write_ptr, fifo_read_ptr, fifo_count;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      fifo_write_ptr <= 8'h00;
      fifo_read_ptr <= 8'h00;
      fifo_count <= 8'h00;
    end else begin
      if (err_valid && !err_fifo_full) begin
        fifo_memory[fifo_write_ptr % FIFO_DEPTH] <= err_data;
        fifo_write_ptr <= fifo_write_ptr + 1;
        fifo_count <= fifo_count + 1;
      end
      
      if (err_fifo_read && !err_fifo_empty) begin
        fifo_read_ptr <= fifo_read_ptr + 1;
        fifo_count <= fifo_count - 1;
      end
    end
  end
  
  assign err_fifo_full = (fifo_count >= FIFO_DEPTH);
  assign err_fifo_empty = (fifo_count == 8'h00);
  assign err_fifo_count = fifo_count;
  assign err_read_data = fifo_memory[fifo_read_ptr % FIFO_DEPTH];

endmodule

// =====================================================================
// END OF MODULE
// =====================================================================
