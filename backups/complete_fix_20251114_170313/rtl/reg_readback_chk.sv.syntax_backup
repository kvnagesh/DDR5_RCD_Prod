/**
 * reg_readback_chk.sv - Register Read-Back Checking Module
 * 
 * Purpose: Implements synthesizable register read-back logic with comprehensive
 *          end-to-end error checking for DDR5 RCD register access verification.
 * 
 * Functionality:
 *   - Validates read values against expected/written values
 *   - Detects stuck-at faults (register always returns same value)
 *   - Detects illegal/bad states (values outside valid range)
 *   - Detects bit-flip errors and inconsistencies
 *   - Provides error status and alert signals for firmware/driver
 *   - Supports multiple register configurations
 *   - Generates detailed error flags for debugging
 * 
 * Integration Points:
 *   - Connect to register map (expected_value inputs)
 *   - Interface with config/status modules
 *   - Alert signals to firmware/driver for error handling
 *   - Debug/status signals for test/validation
 * 
 * Author: DDR5 RCD Production Team
 * Date: 2025
 */

module reg_readback_chk #(
  parameter int NUM_REGS = 32,           
  parameter int REG_WIDTH = 32,          
  parameter int ADDR_WIDTH = 8,          
  parameter int ERROR_HISTORY_DEPTH = 16 // Error history buffer depth
)(
  // Clock and Reset
  input  logic                          clk,
  input  logic                          rst_n,
  
  // Register Access Interface
  input  logic [ADDR_WIDTH-1:0]         reg_addr,        
  input  logic [REG_WIDTH-1:0]          read_data,       
  input  logic [REG_WIDTH-1:0]          expected_data,   
  input  logic                          read_enable,     
  input  logic                          write_enable,    
  input  logic [REG_WIDTH-1:0]          write_data,      
  
  // Valid Range Configuration (for illegal state detection)
  input  logic [REG_WIDTH-1:0]          valid_mask,      
  input  logic [REG_WIDTH-1:0]          valid_min [NUM_REGS],  
  input  logic [REG_WIDTH-1:0]          valid_max [NUM_REGS],  
  
  // Error Status Signals
  output logic                          error_detected,  
  output logic [NUM_REGS-1:0]           reg_error_flag,  
  output logic [REG_WIDTH-1:0]          last_error_addr, 
  output logic [REG_WIDTH-1:0]          last_error_data, 
  output logic [REG_WIDTH-1:0]          last_expected,   
  
  // Detailed Error Type Flags
  output logic                          mismatch_error,  
  output logic                          stuck_at_error,  
  output logic                          illegal_state_error, 
  output logic                          bit_flip_error,  
  output logic                          consistency_error, 
  
  // Status/Alert Signals
  output logic                          alert_critical,  
  output logic                          alert_warning,   
  output logic                          status_valid,    
  
  // Test/Debug Interface
  output logic [ERROR_HISTORY_DEPTH-1:0][REG_WIDTH-1:0] error_history, 
  output logic [7:0]                   error_count,     
  output logic                          monitor_enable   // Monitor activity
);
  
  // =========================================================================
  // Internal Registers and Signals
  // =========================================================================
  
  // Per-register state tracking
  logic [NUM_REGS-1:0][REG_WIDTH-1:0] last_read_value;
  logic [NUM_REGS-1:0][REG_WIDTH-1:0] stuck_check_value;
  logic [NUM_REGS-1:0]                stuck_at_detected;
  logic [NUM_REGS-1:0]                read_performed;
  logic [NUM_REGS-1:0][3:0]           read_count; // Consecutive same reads
  
  // Current operation signals
  logic [NUM_REGS-1:0]                reg_idx;
  logic                               error_this_cycle;
  logic [4:0]                         error_type; // Multi-bit error type
  
  // Error history and counters
  logic [ERROR_HISTORY_DEPTH-1:0][REG_WIDTH-1:0] error_hist_fifo;
  logic [7:0]                        error_cnt;
  logic [3:0]                        error_hist_wr_ptr;
  
  // Consistency check
  logic [NUM_REGS-1:0]                prev_read_done;
  logic [NUM_REGS-1:0][REG_WIDTH-1:0] prev_read_data;
  
  // =========================================================================
  // Error Type Definitions (bit field in error_type)
  // =========================================================================
  localparam ERROR_MISMATCH = 4'b0001;
  localparam ERROR_STUCK_AT = 4'b0010;
  localparam ERROR_ILLEGAL  = 4'b0100;
  localparam ERROR_BIT_FLIP = 4'b1000;
  localparam ERROR_CONSISTENCY = 5'b10001;
  
  // =========================================================================
  // MAIN CHECKING LOGIC
  // =========================================================================
  
  // Validate address range
  assign reg_idx = (reg_addr < NUM_REGS) ? reg_addr : 32'h0;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      // Reset all tracking
      last_read_value <= '0;
      stuck_check_value <= '0;
      stuck_at_detected <= '0;
      read_performed <= '0;
      read_count <= '0;
      prev_read_done <= '0;
      prev_read_data <= '0;
      error_hist_fifo <= '0;
      error_cnt <= '0;
      error_hist_wr_ptr <= '0;
      error_type <= '0;
      error_this_cycle <= 1'b0;
    end else begin
      error_this_cycle <= 1'b0;
      error_type <= '0;
      
      // ===== READ PATH: Capture and validate read data =====
      if (read_enable) begin
        
        // Check 1: Value Mismatch (read_data != expected_data)
        if (read_data != expected_data) begin
          error_this_cycle <= 1'b1;
          error_type |= ERROR_MISMATCH;
        end
        
        // Check 2: Stuck-At Detection
        // If same value read multiple times in a row, flag as stuck
        if (prev_read_done[reg_idx] && prev_read_data[reg_idx] == read_data) begin
          read_count[reg_idx] <= read_count[reg_idx] + 1;
          if (read_count[reg_idx] >= 4'd3) begin // Stuck after 3 consistent reads
            stuck_at_detected[reg_idx] <= 1'b1;
            error_this_cycle <= 1'b1;
            error_type |= ERROR_STUCK_AT;
          end
        end else begin
          read_count[reg_idx] <= 4'h1;
          stuck_at_detected[reg_idx] <= 1'b0;
        end
        
        // Check 3: Illegal/Bad State Detection
        // Verify against valid range and mask
        if ((read_data & valid_mask) < valid_min[reg_idx] ||
            (read_data & valid_mask) > valid_max[reg_idx]) begin
          error_this_cycle <= 1'b1;
          error_type |= ERROR_ILLEGAL;
        end
        
        // Check 4: Bit-Flip Error Detection
        // XOR with expected to find bit differences
        if (prev_read_done[reg_idx] && prev_read_data[reg_idx] != read_data) begin
          // Different from previous but not expected - possible bit flip
          if (read_data != expected_data && prev_read_data[reg_idx] == expected_data) begin
            error_this_cycle <= 1'b1;
            error_type |= ERROR_BIT_FLIP;
          end
        end
        
        // Store for next comparison
        prev_read_data[reg_idx] <= read_data;
        prev_read_done[reg_idx] <= 1'b1;
        last_read_value[reg_idx] <= read_data;
        read_performed[reg_idx] <= 1'b1;
      end
      
      // ===== CONSISTENCY CHECK =====
      // Verify back-to-back reads are consistent
      if (read_enable && prev_read_done[reg_idx]) begin
        if (prev_read_data[reg_idx] != read_data) begin
          error_this_cycle <= 1'b1;
          error_type |= ERROR_CONSISTENCY;
        end
      end
      
      // ===== ERROR HISTORY MANAGEMENT =====
      if (error_this_cycle) begin
        error_hist_fifo[error_hist_wr_ptr] <= read_data;
        error_hist_wr_ptr <= error_hist_wr_ptr + 1;
        if (error_cnt < 8'hFF) begin
          error_cnt <= error_cnt + 1;
        end
      end
      
    end // else (!rst_n)
  end // always_ff
  
  // =========================================================================
  // OUTPUT ASSIGNMENT
  // =========================================================================
  
  // Aggregate error flags
  always_comb begin
    error_detected = |reg_error_flag;
    alert_critical = error_detected && (stuck_at_error || bit_flip_error);
    alert_warning = error_detected && ~alert_critical;
  end
  
  // Per-register error flag - latching
  assign reg_error_flag[reg_idx] = error_this_cycle ? 1'b1 : reg_error_flag[reg_idx];
  
  // Detailed error type outputs
  assign mismatch_error = error_type[0];
  assign stuck_at_error = error_type[1];
  assign illegal_state_error = error_type[2];
  assign bit_flip_error = error_type[3];
  assign consistency_error = error_type[4];
  
  // Last error information
  assign last_error_addr = reg_idx;
  assign last_error_data = last_read_value[reg_idx];
  assign last_expected = expected_data;
  
  // Error history
  assign error_history = error_hist_fifo;
  assign error_count = error_cnt;
  
  // Status valid indicator
  assign status_valid = |read_performed;
  assign monitor_enable = |read_performed;
  
endmodule : reg_readback_chk

/**
 * ============================================================================
 * INTEGRATION GUIDE
 * ============================================================================
 * 
 * 1. INSTANTIATION EXAMPLE:
 *    reg_readback_chk #(
 *      .NUM_REGS(32),
 *      .REG_WIDTH(32),
 *      .ADDR_WIDTH(8),
 *      .ERROR_HISTORY_DEPTH(16)
 *    ) u_readback_chk (
 *      .clk(clk),
 *      .rst_n(rst_n),
 *      .reg_addr(addr_bus),
 *      .read_data(data_read_from_reg),
 *      .expected_data(config_expected_val),
 *      .read_enable(reg_read_strobe),
 *      .error_detected(readback_error),
 *      .alert_critical(critical_alert),
 *      ...
 *    );
 * 
 * 2. CONFIGURATION:
 *    - valid_mask: Set bits indicate which bits are checked
 *    - valid_min/max: Define acceptable range per register
 *    - Expected values from register map configuration
 * 
 * 3. ERROR HANDLING:
 *    - Check error_detected every cycle
 *    - Log alert signals for firmware/driver
 *    - Use error history buffer for diagnostics
 *    - Inspect detailed error type flags
 * 
 * 4. FIRMWARE INTEGRATION:
 *    - Read error_count to monitor health
 *    - Use reg_error_flag for per-register diagnostics
 *    - Implement recovery on critical alerts
 *    - Log last_error_* for troubleshooting
 * 
 * 5. TEST/VALIDATION:
 *    - Monitor error_history FIFO during validation
 *    - Verify all error types trigger appropriately
 *    - Check alert signals under fault injection
 *    - Validate consistency checks work correctly
 * 
 * ============================================================================
 */
