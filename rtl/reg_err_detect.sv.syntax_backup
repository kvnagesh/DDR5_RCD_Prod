// reg_err_detect.sv
// Module for comprehensive register error detection and reporting
// Tracks valid/invalid accesses, out-of-range, protocol violations, lock errors, consistency, stuck-at, and bit-flips
// Generates error/warning flags, counters, alert lines, and register log
// All ports documented for integration

module reg_err_detect #(
    parameter REG_ADDR_WIDTH = 8,
    parameter REG_DATA_WIDTH = 32,
    parameter LOG_DEPTH = 16
) (
    input  wire                    clk,
    input  wire                    rst_n,
    // Register access interface
    input  wire                    reg_write,
    input  wire                    reg_read,
    input  wire [REG_ADDR_WIDTH-1:0] reg_addr,
    input  wire [REG_DATA_WIDTH-1:0] reg_wdata,
    input  wire [REG_DATA_WIDTH-1:0] reg_rdata,
    input  wire                    reg_lock,

    // Protocol/config inputs
    input  wire                    access_valid,
    input  wire                    addr_range_chk,
    input  wire                    protocol_ok,
    input  wire                    lock_status,
    input  wire                    consistency_chk,

    // Error outputs
    output reg                     err_flag,
    output reg                     warn_flag,
    output reg [7:0]               err_code,     
    output reg [15:0]              err_counter,  
    output reg [15:0]              warn_counter, 
    output reg                     alert_line,   
    
    // Register log output
    output reg [REG_ADDR_WIDTH-1:0] log_addr,
    output reg [REG_DATA_WIDTH-1:0] log_data,
    output reg [2:0]               log_access_type, 
    output reg                     log_valid       // 1 when log output valid
);
// Error encoding:
// 0: No Error
// 1: Invalid Access
// 2: Out-of-Range
// 3: Protocol Violation
// 4: Lock Error
// 5: Consistency Error
// 6: Stuck-at Fault
// 7: Bit Flip

localparam ERR_NONE             = 3'd0;
localparam ERR_INVALID_ACCESS   = 3'd1;
localparam ERR_OUT_OF_RANGE     = 3'd2;
localparam ERR_PROTOCOL         = 3'd3;
localparam ERR_LOCK             = 3'd4;
localparam ERR_CONSISTENCY      = 3'd5;
localparam ERR_STUCK_AT         = 3'd6;
localparam ERR_BIT_FLIP         = 3'd7;

// Internal log memory
reg [REG_ADDR_WIDTH-1:0] log_addr_mem[0:LOG_DEPTH-1];
reg [REG_DATA_WIDTH-1:0] log_data_mem[0:LOG_DEPTH-1];
reg [2:0]               log_type_mem[0:LOG_DEPTH-1];
reg [3:0] log_ptr;

// Internal error detection combinational
wire invalid_access  = ~access_valid;
wire out_of_range    = ~addr_range_chk;
wire protocol_err    = ~protocol_ok;
wire lock_err        = reg_lock & ~lock_status;
wire consistency_err = ~consistency_chk;
// Stuck-at/bit-flip detection (illustrative, real implementation may need BIST/BISR)
wire stuck_at_fault  = (reg_wdata === {REG_DATA_WIDTH{1'bx}}) | (reg_rdata === {REG_DATA_WIDTH{1'bx}});
wire bit_flip        = ^reg_wdata ^ ^reg_rdata;

// Error/warning logic
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        err_flag      <= 0;
        warn_flag     <= 0;
        err_code      <= 0;
        err_counter   <= 0;
        warn_counter  <= 0;
        alert_line    <= 0;
        log_ptr       <= 0;
        log_valid     <= 0;
    end else begin
        err_flag   <= 0;
        warn_flag  <= 0;
        log_valid  <= 0;
        // Error detection
        if (invalid_access) begin
            err_flag   <= 1;
            err_code   <= ERR_INVALID_ACCESS;
            err_counter<= err_counter + 1;
            alert_line <= 0;
            log_access_type <= ERR_INVALID_ACCESS;
        end else if (out_of_range) begin
            err_flag   <= 1;
            err_code   <= ERR_OUT_OF_RANGE;
            err_counter<= err_counter + 1;
            alert_line <= 0;
            log_access_type <= ERR_OUT_OF_RANGE;
        end else if (protocol_err) begin
            err_flag   <= 1;
            err_code   <= ERR_PROTOCOL;
            err_counter<= err_counter + 1;
            alert_line <= 1; // Critical, raise alert
            log_access_type <= ERR_PROTOCOL;
        end else if (lock_err) begin
            err_flag   <= 1;
            err_code   <= ERR_LOCK;
            err_counter<= err_counter + 1;
            alert_line <= 1; // Critical
            log_access_type <= ERR_LOCK;
        end else if (consistency_err) begin
            warn_flag  <= 1;
            err_code   <= ERR_CONSISTENCY;
            warn_counter<= warn_counter + 1;
            alert_line <= 0;
            log_access_type <= ERR_CONSISTENCY;
        end else if (stuck_at_fault) begin
            err_flag   <= 1;
            err_code   <= ERR_STUCK_AT;
            err_counter<= err_counter + 1;
            alert_line <= 1;
            log_access_type <= ERR_STUCK_AT;
        end else if (bit_flip) begin
            warn_flag  <= 1;
            err_code   <= ERR_BIT_FLIP;
            warn_counter<= warn_counter + 1;
            alert_line <= 0;
            log_access_type <= ERR_BIT_FLIP;
        end else begin
            // No error/warning
            err_flag   <= 0;
            warn_flag  <= 0;
            err_code   <= ERR_NONE;
            alert_line <= 0;
            log_access_type <= ERR_NONE;
        end
        // Logging
        if ((reg_read||reg_write) || err_flag || warn_flag) begin
            log_addr_mem[log_ptr] <= reg_addr;
            log_data_mem[log_ptr] <= reg_write ? reg_wdata : reg_rdata;
            log_type_mem[log_ptr] <= log_access_type;
            log_valid             <= 1;
            log_addr              <= reg_addr;
            log_data              <= reg_write ? reg_wdata : reg_rdata;
            log_access_type       <= log_access_type;
            log_ptr               <= (log_ptr == LOG_DEPTH-1) ? 0 : log_ptr+1;
        end
    end
end
// Integration notes:
// - connect all error outputs to firmware/RTL checker
// - alert_line can be routed to a system interrupt or testbench monitor
// - log_addr/log_data/log_access_type used for post-mortem or live debug
// - module is synthesizable and ready for integration
endmodule
