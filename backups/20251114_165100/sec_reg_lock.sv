// sec_reg_lock.sv - Secure Register Lock System
// Author: kvnagesh
// Description: Secure access control system with password/key lock, access levels,
//              atomic write, error/alert flags, and flexible register extension.

module sec_reg_lock #(
    parameter REG_WIDTH = 32,
    parameter PASSWORD_WIDTH = 32,
    parameter ACCESS_LEVELS = 2 // 0: No access, 1: RW, 2: Admin
)(
    input                        clk,
    input                        rst_n,
    input [PASSWORD_WIDTH-1:0]   key_in,           // Password/key input (integration)
    input                        key_valid,        // Key input strobing
    input [1:0]                  set_access_lvl,   // Set access level (admin only)
    input                        access_lvl_valid, // Access level update strobing
    input                        lock_req,         // Request lock/unlock
    input                        reg_write_req,    // Write request to protected register
    input [REG_WIDTH-1:0]        reg_write_data,   // Data to write (atomic)
    output reg                   locked,           // Current lock status
    output reg [1:0]             access_level,     // Current access level
    output reg                   write_success,    // Write success flag
    output reg                   error_flag,       // Error on unauthorized access
    output reg                   alert_flag,       // Alert on access violation
    output reg [REG_WIDTH-1:0]   reg_data,         // Protected register output
    // Integration extension signals for register map
    output reg                   lock_state_update,// Register map extension: state update
    output reg                   lock_cfg_alert    // Register map extension: alert status
);

    // Protection mechanism: simple password, lock status, access level logic
    localparam [PASSWORD_WIDTH-1:0] ADMIN_KEY = 32'hDEADBEEF; // Example password
    reg [PASSWORD_WIDTH-1:0]        curr_key;
    reg                             key_authenticated;

    // Lock/unlock logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            locked         <= 1'b1;
            access_level   <= 2'd0;
            write_success  <= 1'b0;
            error_flag     <= 1'b0;
            alert_flag     <= 1'b0;
            reg_data       <= {REG_WIDTH{1'b0}};
            curr_key       <= {PASSWORD_WIDTH{1'b0}};
            key_authenticated <= 1'b0;
            lock_state_update <= 1'b0;
            lock_cfg_alert    <= 1'b0;
        end else begin
            // Authenticate key for lock/unlock
            if (key_valid || access_lvl_valid) begin
                curr_key <= key_in;
                if (key_in == ADMIN_KEY) begin
                    key_authenticated <= 1'b1;
                end else begin
                    key_authenticated <= 1'b0;
                end
            end
            // Lock/Unlock mechanism (admin only)
            if (lock_req & key_authenticated) begin
                locked <= ~locked;
                lock_state_update <= 1'b1;
            end else begin
                lock_state_update <= 1'b0;
            end
            // Access level config (admin only)
            if (access_lvl_valid & key_authenticated & ~locked) begin
                access_level <= set_access_lvl;
            end
            // Atomic register write (RW or Admin level required, and unlocked)
            if (reg_write_req & ~locked & (access_level > 0)) begin
                reg_data      <= reg_write_data;
                write_success <= 1'b1;
                error_flag    <= 1'b0;
                alert_flag    <= 1'b0;
            end else if (reg_write_req & (locked | (access_level == 0))) begin
                // Unauthorized
                write_success   <= 1'b0;
                error_flag      <= 1'b1;
                alert_flag      <= 1'b1;
                lock_cfg_alert  <= 1'b1;
            end else begin
                write_success   <= 1'b0;
                error_flag      <= 1'b0;
                alert_flag      <= 1'b0;
                lock_cfg_alert  <= 1'b0;
            end
        end
    end
endmodule

/*
PORT DOCUMENTATION:
    clk                : Clock signal
    rst_n              : Active-low reset
    key_in             : Password/key input for authentication
    key_valid          : Strobe for key input
    set_access_lvl     : Access level configuration (0=No access, 1=RW, 2=Admin)
    access_lvl_valid   : Strobe to set access level
    lock_req           : Request to lock/unlock register (admin only)
    reg_write_req      : Request write to protected register
    reg_write_data     : Data to write to register
    locked             : Indicates if register is locked
    access_level       : Indicates current access level
    write_success      : Indicates successful write
    error_flag         : Error on unauthorized write attempt
    alert_flag         : Alert on access violation (for integration/monitor)
    reg_data           : Protected register output
    lock_state_update  : State update flag for extension/register map
    lock_cfg_alert     : Alert flag for register map extension
PROTECTION:
    - Only authenticated (password/key) admin can lock/unlock or set access level.
    - Atomic write only allowed if unlocked and with proper access level.
    - Unauthorized accesses trigger error/alert flags for secure integration.
    - Module easily extendable for multiple registers or more access levels.
*/
