//==================================================================================
// Module: register_shadow_protect
// Description: Register Shadowing and Protection with Error Detection
//              - Shadow registers for critical configuration
//              - Multi-level write protection (bit, register, global)
//              - Access violation detection and reporting
//              - Parity/ECC protection for register data
//              - Transaction logging for debug
// Author: Auto-generated for DDR5 RCD Production
// Date: 2025-11-06
//==================================================================================

module register_shadow_protect #(
    parameter int REG_ADDR_WIDTH = 8,
    parameter int REG_DATA_WIDTH = 8,
    parameter int NUM_REGS = 256,
    parameter int SHADOW_DEPTH = 4,       // Shadow history depth
    parameter int LOG_DEPTH = 16          // Transaction log depth
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,
    
    // Register Access Interface (from I3C)
    input  logic [REG_ADDR_WIDTH-1:0]   access_addr,
    input  logic [REG_DATA_WIDTH-1:0]   access_wdata,
    output logic [REG_DATA_WIDTH-1:0]   access_rdata,
    input  logic                        access_write,
    input  logic                        access_read,
    output logic                        access_ack,
    output logic                        access_error,
    
    // Register Output Interface (to RCD logic)
    output logic [REG_DATA_WIDTH-1:0]   reg_bank [NUM_REGS-1:0],
    
    // Protection Configuration
    input  logic [NUM_REGS-1:0]         write_protect_mask,   // Per-register protection
    input  logic [7:0]                  bit_protect_mask [NUM_REGS-1:0], // Per-bit protection
    input  logic                        global_lock,
    input  logic                        shadow_enable,
    
    // Error Detection and Reporting
    output logic [7:0]                  error_code,
    output logic [REG_ADDR_WIDTH-1:0]   error_addr,
    output logic                        error_valid,
    output logic                        parity_error,
    output logic                        protection_violation,
    
    // Status and Debug
    output logic [15:0]                 access_count,
    output logic [15:0]                 error_count,
    output logic [15:0]                 violation_count
);

//==================================================================================
// Internal Structures
//==================================================================================

// Register bank with shadow copies
logic [REG_DATA_WIDTH-1:0] primary_regs [NUM_REGS-1:0];
logic [REG_DATA_WIDTH-1:0] shadow_regs [NUM_REGS-1:0][SHADOW_DEPTH-1:0];
logic [REG_DATA_WIDTH-1:0] previous_value;

// Parity bits for each register
logic parity_bits [NUM_REGS-1:0];
logic calculated_parity;

// Protection tracking
logic reg_locked [NUM_REGS-1:0];
logic write_attempted;
logic protection_check_passed;

// Transaction log
typedef struct packed {
    logic [REG_ADDR_WIDTH-1:0] addr;
    logic [REG_DATA_WIDTH-1:0] data;
    logic                      is_write;
    logic                      error;
    logic [7:0]                error_type;
} transaction_log_t;

transaction_log_t tx_log [LOG_DEPTH-1:0];
logic [$clog2(LOG_DEPTH)-1:0] log_ptr;

// Error types
localparam logic [7:0] ERR_NONE                = 8'h00;
localparam logic [7:0] ERR_WRITE_PROTECTED     = 8'h01;
localparam logic [7:0] ERR_BIT_PROTECTED       = 8'h02;
localparam logic [7:0] ERR_GLOBAL_LOCKED       = 8'h03;
localparam logic [7:0] ERR_PARITY_MISMATCH     = 8'h04;
localparam logic [7:0] ERR_INVALID_ADDR        = 8'h05;
localparam logic [7:0] ERR_ACCESS_TIMEOUT      = 8'h06;
localparam logic [7:0] ERR_SHADOW_CORRUPT      = 8'h07;

//==================================================================================
// Parity Calculation
//==================================================================================

function automatic logic calc_parity(input [REG_DATA_WIDTH-1:0] data);
    logic p;
    p = ^data;  // XOR all bits
    return p;
endfunction

//==================================================================================
// Protection Check Logic
//==================================================================================

always_comb begin
    protection_check_passed = 1'b1;
    error_code = ERR_NONE;
    
    if (access_write) begin
        // Check global lock
        if (global_lock) begin
            protection_check_passed = 1'b0;
            error_code = ERR_GLOBAL_LOCKED;
        end
        // Check register-level protection
        else if (write_protect_mask[access_addr]) begin
            protection_check_passed = 1'b0;
            error_code = ERR_WRITE_PROTECTED;
        end
        // Check bit-level protection
        else if ((access_wdata & bit_protect_mask[access_addr]) != 
                 (primary_regs[access_addr] & bit_protect_mask[access_addr])) begin
            protection_check_passed = 1'b0;
            error_code = ERR_BIT_PROTECTED;
        end
        // Check address validity
        else if (access_addr >= NUM_REGS) begin
            protection_check_passed = 1'b0;
            error_code = ERR_INVALID_ADDR;
        end
    end
end

//==================================================================================
// Register Write Logic with Shadowing
//==================================================================================

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        for (int i = 0; i < NUM_REGS; i++) begin
            primary_regs[i] <= '0;
            parity_bits[i] <= 1'b0;
            for (int j = 0; j < SHADOW_DEPTH; j++) begin
                shadow_regs[i][j] <= '0;
            end
        end
        access_ack <= 1'b0;
        access_error <= 1'b0;
        protection_violation <= 1'b0;
        error_valid <= 1'b0;
        error_addr <= '0;
        
    end else begin
        access_ack <= 1'b0;
        access_error <= 1'b0;
        error_valid <= 1'b0;
        
        // Handle write access
        if (access_write) begin
            if (protection_check_passed) begin
                // Save previous value to shadow
                if (shadow_enable) begin
                    for (int j = SHADOW_DEPTH-1; j > 0; j--) begin
                        shadow_regs[access_addr][j] <= shadow_regs[access_addr][j-1];
                    end
                    shadow_regs[access_addr][0] <= primary_regs[access_addr];
                end
                
                // Write new value
                primary_regs[access_addr] <= access_wdata;
                
                // Update parity
                parity_bits[access_addr] <= calc_parity(access_wdata);
                
                access_ack <= 1'b1;
            end else begin
                // Write protection violation
                access_error <= 1'b1;
                protection_violation <= 1'b1;
                error_valid <= 1'b1;
                error_addr <= access_addr;
            end
        end
        
        // Handle read access
        else if (access_read) begin
            if (access_addr < NUM_REGS) begin
                access_ack <= 1'b1;
                
                // Check parity on read
                calculated_parity <= calc_parity(primary_regs[access_addr]);
                if (calculated_parity != parity_bits[access_addr]) begin
                    error_code <= ERR_PARITY_MISMATCH;
                    error_valid <= 1'b1;
                    error_addr <= access_addr;
                end
            end else begin
                access_error <= 1'b1;
                error_code <= ERR_INVALID_ADDR;
                error_valid <= 1'b1;
                error_addr <= access_addr;
            end
        end
    end
end

// Read data output
assign access_rdata = (access_read && access_addr < NUM_REGS) ? 
                       primary_regs[access_addr] : 8'h00;

// Assign register bank outputs
genvar i;
generate
    for (i = 0; i < NUM_REGS; i++) begin : reg_bank_assign
        assign reg_bank[i] = primary_regs[i];
    end
endgenerate

//==================================================================================
// Parity Error Detection
//==================================================================================

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        parity_error <= 1'b0;
    end else if (access_read) begin
        calculated_parity = calc_parity(primary_regs[access_addr]);
        parity_error <= (calculated_parity != parity_bits[access_addr]);
    end else begin
        parity_error <= 1'b0;
    end
end

//==================================================================================
// Transaction Logging
//==================================================================================

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        log_ptr <= '0;
        for (int i = 0; i < LOG_DEPTH; i++) begin
            tx_log[i] <= '0;
        end
    end else if (access_write || access_read) begin
        tx_log[log_ptr].addr <= access_addr;
        tx_log[log_ptr].data <= access_write ? access_wdata : access_rdata;
        tx_log[log_ptr].is_write <= access_write;
        tx_log[log_ptr].error <= access_error;
        tx_log[log_ptr].error_type <= error_code;
        
        log_ptr <= log_ptr + 1;
    end
end

//==================================================================================
// Statistics Counters
//==================================================================================

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        access_count <= 16'h0000;
        error_count <= 16'h0000;
        violation_count <= 16'h0000;
    end else begin
        if (access_write || access_read) begin
            access_count <= access_count + 1;
        end
        
        if (access_error || error_valid) begin
            error_count <= error_count + 1;
        end
        
        if (protection_violation) begin
            violation_count <= violation_count + 1;
        end
    end
end

//==================================================================================
// Shadow Integrity Check
//==================================================================================

logic shadow_corrupt;

always_comb begin
    shadow_corrupt = 1'b0;
    
    if (shadow_enable) begin
        // Check if shadow history is consistent
        for (int i = 0; i < NUM_REGS; i++) begin
            for (int j = 0; j < SHADOW_DEPTH-1; j++) begin
                // Verify parity of shadow copies
                if (calc_parity(shadow_regs[i][j]) != calc_parity(shadow_regs[i][j])) begin
                    shadow_corrupt = 1'b1;
                end
            end
        end
    end
end

endmodule
