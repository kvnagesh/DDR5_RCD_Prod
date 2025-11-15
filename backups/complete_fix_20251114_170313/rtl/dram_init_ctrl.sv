// dram_init_ctrl.sv
// DDR5 DRAM Initialization Controller
// Author: [Your Name]
// Description: Robust state machine for DRAM init sequence with parameterized timing/cycles, handshake, and documentation

module dram_init_ctrl #(
    // Timing parameters (adjust as needed)
    parameter int t_powerup_cycles = 10000,    
    parameter int t_nop_cycles     = 20,       
    parameter int t_precharge_cycles = 20,     
    parameter int t_zq_cal_cycles  = 128,      
    parameter int t_mr_cycles      = 16,       
    parameter int t_cke_cycles     = 16,       
    parameter int NUM_MR_COMMANDS  = 8         // Number of mode registers to set
)(
    input  logic clk,
    input  logic rst_n,           
    input  logic start,           
    output logic busy,            
    output logic done,            
    // DRAM command handshake signals
    output logic cmd_valid,
    output logic [4:0] cmd_type,  
    output logic [31:0] cmd_data, 
    input  logic cmd_ready        // Handshake from DRAM interface
);
//----------------------------------------------------------------
// State encoding
//----------------------------------------------------------------
typedef enum logic [3:0] {
    IDLE,
    POWERUP,
    NOP,
    PRECHARGE,
    ZQ_CAL,
    SET_MR,
    CKE_ENABLE,
    COMPLETE
} state_t;
state_t state, state_nxt;

//----------------------------------------------------------------
// Internal registers & timers
//----------------------------------------------------------------
logic [$clog2(t_powerup_cycles)-1:0] timer;
logic [$clog2(NUM_MR_COMMANDS)-1:0] mr_index;

//----------------------------------------------------------------
// State machine logic
//----------------------------------------------------------------
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state      <= IDLE;
        timer      <= '0;
        mr_index   <= '0;
    end else begin
        state <= state_nxt;
        if (state == POWERUP || state == NOP || state == PRECHARGE || state == ZQ_CAL || state == CKE_ENABLE)
            timer <= timer + 1;
        else
            timer <= '0;
        if (state == SET_MR && cmd_valid && cmd_ready)
            mr_index <= mr_index + 1;
        else if (state != SET_MR)
            mr_index <= '0;
    end
end

//----------------------------------------------------------------
// Next-state logic
//----------------------------------------------------------------
always_comb begin
    state_nxt = state;
    busy   = 1'b0;
    done   = 1'b0;
    cmd_valid = 1'b0; cmd_type = '0; cmd_data = '0;
    case (state)
        IDLE: begin
            if (start) begin
                state_nxt = POWERUP;
            end
        end
        POWERUP: begin
            busy = 1'b1;
            if (timer >= t_powerup_cycles) state_nxt = NOP;
        end
        NOP: begin
            busy = 1'b1;
            if (timer >= t_nop_cycles) state_nxt = PRECHARGE;
        end
        PRECHARGE: begin
            busy = 1'b1;
            cmd_valid = 1'b1; cmd_type = 5'd1; // PRECHARGE cmd
            cmd_data = 32'h0;
            if (timer >= t_precharge_cycles) state_nxt = ZQ_CAL;
        end
        ZQ_CAL: begin
            busy = 1'b1;
            cmd_valid = 1'b1; cmd_type = 5'd2; // ZQ CALIBRATION cmd
            cmd_data = 32'h0;
            if (timer >= t_zq_cal_cycles) state_nxt = SET_MR;
        end
        SET_MR: begin
            busy = 1'b1;
            if (mr_index < NUM_MR_COMMANDS) begin
                cmd_valid = 1'b1; cmd_type = 5'd3; // MODE REGISTER SET cmd
                cmd_data = {24'h0, mr_index}; // Example data
                if (cmd_ready) ; // advance
            end else begin
                state_nxt = CKE_ENABLE;
            end
        end
        CKE_ENABLE: begin
            busy = 1'b1;
            cmd_valid = 1'b1; cmd_type = 5'd4; // CKE ENABLE cmd
            cmd_data = 32'h1;
            if (timer >= t_cke_cycles) state_nxt = COMPLETE;
        end
        COMPLETE: begin
            done = 1'b1;
            busy = 1'b0;
        end
        default: state_nxt = IDLE;
    endcase
end

//----------------------------------------------------------------
// Port Interface Documentation
//----------------------------------------------------------------
/*
  Port Descriptions:
    clk       : Source clock for sequencer
    rst_n     : Active-low reset
    start     : Assert to begin DRAM initialization sequence
    busy      : Controller is running sequence
    done      : Sequence completed and controller is idle
    cmd_valid : Assert when command type/data valid for DRAM
    cmd_type  : DRAM command encoding:
                   1: PRECHARGE
                   2: ZQ CALIBRATION
                   3: MODE REGISTER SET
                   4: CKE ENABLE
    cmd_data  : Data/payload for each command (timing, mode value, etc.)
    cmd_ready : Handshake, asserted by DRAM interface when ready for new command
  Sequence:
    1. Power-up delay (t_powerup_cycles)
    2. Issue NOP (t_nop_cycles)
    3. PRECHARGE command (t_precharge_cycles)
    4. ZQ Calibration (t_zq_cal_cycles)
    5. Mode Register programming (NUM_MR_COMMANDS)
    6. CKE Enable (t_cke_cycles)
    7. Complete (done)
  All key timings/cycles are overridable by parameter.
*/
//----------------------------------------------------------------
endmodule
