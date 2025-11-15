// ------------------------------------------------------------------------------
// DDR5 RCD Bus Command Word (BCW) Manager
// Provides BCW register update, state management, handshake, status/error signals
// Supports burst/parallel updates and fast command/control pipeline integration
// ------------------------------------------------------------------------------
// Author: kvnagesh
// Date: 2025-11-04
//
// Description:
//   - Handles BCW register updates for DDR5 RCD routing and command control
//   - Tracks BCW update cycles, handshake, errors, status
//   - Supports high-speed (parallel/burst) state update management
//   - Interfaces with command distributor
//
// Integration notes:
//   - Connect bcw_reg_out, handshake signals to ca_distributor.sv
//   - Use update_req_burst for fast command and pipeline modes
// ------------------------------------------------------------------------------

module bcw_mgr #(
    parameter BCW_WIDTH = 32,
    parameter BURST_MAX = 4
) (
    input  logic                      clk,
    input  logic                      rst_n,

    // Command Distributor Interface
    input  logic                      update_req,        
    input  logic [BCW_WIDTH-1:0]      bcw_reg_in,        
    input  logic                      update_req_burst,  
    input  logic [$clog2(BURST_MAX):0]burst_len,         
    output logic                      update_ack,        

    // Outputs to CA Distributor
    output logic [BCW_WIDTH-1:0]      bcw_reg_out,       
    output logic                      bcw_valid,         

    // Error/Status
    output logic                      error,             
    output logic                      busy,              
    output logic [$clog2(BURST_MAX):0]processed_count    // How many BCWs processed in burst
);

    // Internal registers and state
    logic [BCW_WIDTH-1:0]     reg_bcw;
    logic [$clog2(BURST_MAX):0] burst_cntr;
    logic burst_mode;
    logic update_in_progress;

    // FSM for update management
    typedef enum logic [1:0] {IDLE, UPDATE, BURST, ERROR} state_t;
    state_t state, state_next;

    // Handshake and status assignment
    assign bcw_reg_out       = reg_bcw;
    assign bcw_valid         = (state == UPDATE || state == BURST);
    assign busy              = (state == BURST);
    assign processed_count   = burst_cntr;
    assign error             = (state == ERROR);
    assign update_ack        = (state == UPDATE || (burst_mode && burst_cntr == burst_len));

    // Sequential part
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_bcw       <= '0;
            state         <= IDLE;
            burst_cntr    <= '0;
            burst_mode    <= 1'b0;
        end else begin
            state         <= state_next;
            if (state_next == UPDATE) begin
                reg_bcw   <= bcw_reg_in;
            end
            if (state_next == BURST) begin
                if (burst_cntr < burst_len) begin
                    reg_bcw   <= bcw_reg_in;
                    burst_cntr <= burst_cntr + 1;
                end
            end else if (state_next != BURST) begin
                burst_cntr <= '0;
            end
            burst_mode <= update_req_burst;
        end
    end

    // Next state logic
    always_comb begin
        state_next = state;
        case (state)
            IDLE: begin
                if (update_req) begin
                    if (update_req_burst) state_next = BURST;
                    else                  state_next = UPDATE;
                end
            end
            UPDATE: begin
                state_next = IDLE;
            end
            BURST: begin
                if (burst_cntr == burst_len) state_next = IDLE;
            end
            ERROR: begin
                state_next = IDLE;
            end
            default: state_next = ERROR;
        endcase
    end

    // Error detection (simple: detect update_req during BUSY/burst)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // error <= 1'b0;  // Already combinational
        end else if (state == BURST && update_req) begin
            // Simultaneous update during burst: signal error
            state <= ERROR;
        end
    end

    // Documentation for integration:
    // ----------------------------------------------
    //  - Connect update_req, bcw_reg_in, update_req_burst, burst_len from control pipeline
    //  - Monitor update_ack and busy for downstream stages
    //  - bcw_reg_out and bcw_valid feed ca_distributor.sv command logic
    //  - processed_count gives burst status
    //  - error signal for diagnostics and robust operation

endmodule
