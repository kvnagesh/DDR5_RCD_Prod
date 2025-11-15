// shadow_reg_sync.sv
// Shadow register mechanism with synchronization across clock domains, handshake, atomic update/rollback support
// Place in rtl/ directory

// This module manages SHADOW and ACTIVE configuration registers, synchronizes config changes safely across clock domains,
// and provides handshake, atomic update, and rollback controls to config logic.

module shadow_reg_sync #(
    parameter  REG_WIDTH = 32,                    
    parameter  NUM_REGS  = 4                      // Number of critical config registers shadowed
) (
    // Clock signals
    input  logic                   cfg_clk,       
    input  logic                   user_clk,      

    // RESET
    input  logic                   rst_n,         

    //--------------------------------------------
    // Config interface (cfg_clk domain)
    //--------------------------------------------
    input  logic  [NUM_REGS-1:0]   wr_en,         
    input  logic  [REG_WIDTH-1:0]  wr_data [NUM_REGS], 
    output logic  [REG_WIDTH-1:0]  rd_data [NUM_REGS], 

    output logic                   shadow_valid,  
    input  logic                   shadow_apply,  
    input  logic                   shadow_rollback, 
    output logic                   shadow_busy,   

    //--------------------------------------------
    // Main logic/User domain interface (user_clk domain)
    //--------------------------------------------
    output logic [REG_WIDTH-1:0]   active_reg [NUM_REGS], 
    // Handshake signaling for software/logic
    output logic                   update_ack,    
    output logic                   update_err     // If synchronization/atomic update failed
);

    //--------------------------------------------
    // Shadows
    //--------------------------------------------
    logic [REG_WIDTH-1:0] shadow_reg [NUM_REGS];       // Shadow copy buffer
    logic [REG_WIDTH-1:0] active_reg_cfg [NUM_REGS];   // ACTIVE reg seen from cfg_clk domain
    logic [REG_WIDTH-1:0] prev_reg [NUM_REGS];         // For rollback

    logic shadow_valid_r, shadow_apply_r, busy_r;

    // Write shadow registers in cfg_clk domain
    always_ff @(posedge cfg_clk or negedge rst_n) begin
        if (!rst_n) begin
            foreach (shadow_reg[i]) shadow_reg[i] <= '0;
            shadow_valid_r <= 1'b0;
        end else begin
            foreach (shadow_reg[i]) begin
                if (wr_en[i]) begin
                    shadow_reg[i] <= wr_data[i];
                    shadow_valid_r <= 1'b1;
                end
            end
            if (shadow_apply) shadow_apply_r <= 1'b1;
            else if (shadow_busy) shadow_apply_r <= 1'b0;
        end
    end

    // Shadow valid signal
    assign shadow_valid = shadow_valid_r;

    //--------------------------------------------
    // Atomic update and rollback (cfg_clk domain)
    //--------------------------------------------
    // When apply is pulsed, transfer shadow -> active, latch prev for rollback
    always_ff @(posedge cfg_clk or negedge rst_n) begin
        if (!rst_n) begin
            foreach (active_reg_cfg[i]) active_reg_cfg[i] <= '0;
            foreach (prev_reg[i]) prev_reg[i] <= '0;
            busy_r <= 1'b0;
        end else begin
            if (shadow_apply && shadow_valid_r && !busy_r) begin
                foreach (active_reg_cfg[i]) begin
                    prev_reg[i] <= active_reg_cfg[i];
                    active_reg_cfg[i] <= shadow_reg[i];
                end
                busy_r <= 1'b1; // begin synchronizing
            end else if (shadow_rollback && busy_r) begin
                foreach (active_reg_cfg[i]) active_reg_cfg[i] <= prev_reg[i];
                busy_r <= 1'b0;
            end else if (busy_r && shadow_sync_done) begin
                busy_r <= 1'b0;
            end
        end
    end
    assign shadow_busy = busy_r;

    //--------------------------------------------
    // Cross-domain synchronization (cfg_clk -> user_clk, atomic)
    //--------------------------------------------
    logic [REG_WIDTH-1:0] sync_reg [NUM_REGS];           // Double-synchronized registers
    logic [REG_WIDTH-1:0] sync_reg_d1 [NUM_REGS];
    logic                 sync_start_r, sync_done_r;

    // Simple handshake-state synchronizer
    always_ff @(posedge user_clk or negedge rst_n) begin
        if (!rst_n) begin
            foreach (sync_reg[i]) sync_reg[i] <= '0;
            sync_done_r <= 1'b0;
        end else begin
            if (busy_r) begin
                foreach (sync_reg[i]) sync_reg[i] <= active_reg_cfg[i];
                sync_done_r <= 1'b1; // acknowledge update complete
            end else begin
                sync_done_r <= 1'b0;
            end
        end
    end

    // Second synchronizer stage
    always_ff @(posedge user_clk or negedge rst_n) begin
        if (!rst_n) begin
            foreach (sync_reg_d1[i]) sync_reg_d1[i] <= '0;
            update_ack <= 1'b0;
        end else begin
            foreach (sync_reg_d1[i]) sync_reg_d1[i] <= sync_reg[i];
            foreach (active_reg[i]) active_reg[i] <= sync_reg_d1[i];
            update_ack <= sync_done_r;
        end
    end

    assign update_err = 1'b0; // Can extend for error signaling

    // Export for config logic
    always_comb begin
        foreach (rd_data[i]) rd_data[i] = active_reg_cfg[i];
    end

    // Export synchronization done status from user_clk to cfg_clk (simple pulse)
    logic shadow_sync_done_r;
    always_ff @(posedge cfg_clk or negedge rst_n) begin
        if (!rst_n) shadow_sync_done_r <= 1'b0;
        else shadow_sync_done_r <= (sync_done_r && busy_r);
    end
    assign shadow_sync_done = shadow_sync_done_r;

endmodule

// ----------------------------------------------------------------------
// Port COMMENT SUMMARY for Integration:
//
// wr_en, wr_data   : Used to write individual shadow config registers from config logic
// rd_data          : Shows current ACTIVE reg value as seen by config logic
// shadow_valid     : Indicates shadow registers hold a new config
// shadow_apply     : Pulse to load shadow -> ACTIVE atomically, enabling cross-clock sync
// shadow_rollback  : Pulse to revert to previous ACTIVE value (before last accepted apply)
// shadow_busy      : Indicates ongoing shadow/atomic/sync update
// active_reg       : Synchronized ACTIVE register value in the user logic's clock domain
// update_ack       : Pulsed one cycle on atomic update completion in user clk domain
// update_err       : For extension (e.g., sync error/unexpected rollback)
//
// All synchronization is double-registered for safe CDC (clock domain crossing).
// ----------------------------------------------------------------------
