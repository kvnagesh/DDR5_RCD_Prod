//-----------------------------------------------------------------------------
// i3c_hotjoin_addr_clkstr.sv
//   I3C Hot-Join Detection/Notification, Broadcast Command Decode, 
//   Dynamic Address Assignment, and Clock Stretching Module
//
// Description:
//   - Synthesizable SystemVerilog module for managing I3C features:
//     1. Hot-Join event detection and host master notification
//     2. Broadcast command decode (RSTDAA, ENEC, DISEC, SETDASA)
//     3. Dynamic address assignment state machine
//     4. Slave-driven clock stretching support
//   - All ports and behaviors are documented for integration.
//-----------------------------------------------------------------------------

module i3c_hotjoin_addr_clkstr #(
    parameter integer ADDR_WIDTH = 7
) (
    // Clock and Reset
    input  logic           clk,              // I3C clock
    input  logic           rst_n,            // Active-low reset

    // I3C Bus Signals
    input  logic           scl,              // I3C clock line (from pad)
    input  logic           sda,              // I3C data line (from pad)
    output logic           sda_oe,           // SDA driver enable (0=hi-Z, 1=drive)
    output logic           scl_oe,           // SCL driver enable (clock stretching)

    // Hot-Join Notification
    input  logic           hj_event_req,     // External hot-join event (e.g. from internal circuitry)
    output logic           hj_notify_host,   // Notifies host master of hot-join (pulse)

    // Dynamic Address Assignment
    input  logic           da_assign_req,    // Request to initiate DA config
    input  logic [ADDR_WIDTH-1:0] new_da,    // New dynamic address
    output logic [ADDR_WIDTH-1:0] curr_da,   // Current dynamic address
    output logic           da_assigned,      // DA has been successfully assigned

    // Commands Decode Output
    output logic           cmd_rstdaa,       // Broadcast: RSTDAA
    output logic           cmd_enec,         // Broadcast: ENEC
    output logic           cmd_disec,        // Broadcast: DISEC
    output logic           cmd_setdasa,      // Broadcast: SETDASA

    // Error/Status
    input  logic           proto_err,        // Protocol error detected
    output logic           clock_stretching  // Asserted when slave holds SCL low
);

//----------------------------------------------------------------------------- 
// Internal Signal Declarations 
//----------------------------------------------------------------------------- 

typedef enum logic [2:0] {
    IDLE, HJ_WAIT, HJ_NOTIFY, DA_WAIT_REQ, DA_ASSIGN, DA_DONE, STRETCH
} state_t;

state_t state, next_state;

logic [ADDR_WIDTH-1:0] da_shadow;
logic broadcast_detect;
logic [7:0] cmd_in;

//------------------------------------------------------------------------------
// Hot-Join Detection and Host Notification
//------------------------------------------------------------------------------
// Detect external hot-join request and notify host master as per I3C timing
// spec-protocol.
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state <= IDLE;
        hj_notify_host <= 0;
    end else begin
        case (state)
            IDLE: begin
                if (hj_event_req)
                    state <= HJ_WAIT;
                hj_notify_host <= 0;
            end
            HJ_WAIT: begin
                // Wait for bus idle and then drive hot-join
                if (scl && sda) // bus is idle
                    state <= HJ_NOTIFY;
            end
            HJ_NOTIFY: begin
                hj_notify_host <= 1;
                state <= DA_WAIT_REQ;
            end
            default: begin
                hj_notify_host <= 0;
                state <= DA_WAIT_REQ;
            end
        endcase
    end
end

//------------------------------------------------------------------------------
// Broadcast Command Decode (Basic example, expand as needed)
//------------------------------------------------------------------------------
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        cmd_rstdaa  <= 0;
        cmd_enec    <= 0;
        cmd_disec   <= 0;
        cmd_setdasa <= 0;
    end else begin
        // Example: Simple broadcast decode (expand with address match, FSM, etc)
        cmd_rstdaa  <= (cmd_in==8'h06);   // RSTDAA opcode
        cmd_enec    <= (cmd_in==8'h22);   // ENEC opcode
        cmd_disec   <= (cmd_in==8'h23);   // DISEC opcode
        cmd_setdasa <= (cmd_in==8'h29);   // SETDASA opcode
    end
end

//------------------------------------------------------------------------------
// Dynamic Address Assignment State Machine
//------------------------------------------------------------------------------
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        da_shadow    <= 0;
        da_assigned  <= 0;
        curr_da      <= 0;
        state        <= DA_WAIT_REQ;
    end else begin
        case (state)
            DA_WAIT_REQ: begin
                da_assigned <= 0;
                if (da_assign_req) begin
                    da_shadow <= new_da;
                    state     <= DA_ASSIGN;
                end
            end
            DA_ASSIGN: begin
                // I3C spec: verify new_da is valid; for now assume always
                curr_da     <= da_shadow;
                da_assigned <= 1;
                state       <= DA_DONE;
            end
            DA_DONE: begin
                // One-shot assignment
                state <= DA_WAIT_REQ;
            end
        endcase
    end
end

//------------------------------------------------------------------------------
// Clock Stretching Logic
//------------------------------------------------------------------------------
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        scl_oe           <= 0;
        clock_stretching <= 0;
    end else begin
        // Initiate clock stretching on protocol error, variable speed, etc.
        if (proto_err) begin
            scl_oe           <= 1;
            clock_stretching <= 1;
            state            <= STRETCH;
        end else if (state == STRETCH) begin
            // Release on error handled
            scl_oe           <= 0;
            clock_stretching <= 0;
            state            <= IDLE;
        end else begin
            scl_oe           <= 0;
            clock_stretching <= 0;
        end
    end
end

//---------------------------------------------------------------------------
// Port and Behavioral documentation at module top, above. 
// Additional expansion/parameterizations recommended per product integration.
//---------------------------------------------------------------------------

endmodule
