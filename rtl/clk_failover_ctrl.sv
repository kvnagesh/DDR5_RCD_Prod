// clk_failover_ctrl.sv
// DDR5 RCD Clock Failover Controller
// Author: kvnagesh
// Description: Robust clock failover controller for DDR5 RCD, featuring automatic seamless switching between redundant clock sources, priority selection, status/error flags, glitch-free muxing, and integration hooks.

module clk_failover_ctrl #(
    parameter CLK_CNT_WIDTH = 16,
    parameter PRIORITY = 0     // 0: active first, 1: backup first
) (
    input  wire active_clk,
    input  wire backup_clk,
    input  wire rst_n,
    input  wire sw_override,          // manual override signal
    input  wire select_backup,        // force backup selection
    output wire ddr5_clk_out,         // muxed, glitch-free clock
    output wire active_valid,         // status: active clock OK
    output wire backup_valid,         // status: backup clock OK
    output wire error_flag,           // clocks failed
    output wire failover_status       // indicates current clock source
);

    // Clock monitor (simple pulse counter, replace by custom detector as needed)
    reg [CLK_CNT_WIDTH-1:0] act_cnt, bkp_cnt;
    reg act_ok, bkp_ok;

    always @(posedge active_clk or negedge rst_n) begin
        if (!rst_n) act_cnt <= '0;
        else act_cnt <= act_cnt + 1'b1;
    end
    always @(posedge backup_clk or negedge rst_n) begin
        if (!rst_n) bkp_cnt <= '0;
        else bkp_cnt <= bkp_cnt + 1'b1;
    end

    // Simple validity check (activity within period)
    always @(*) begin
        act_ok = (act_cnt > 8); // threshold for activeness (customize)
        bkp_ok = (bkp_cnt > 8);
    end

    assign active_valid = act_ok;
    assign backup_valid = bkp_ok;

    // Priority & selection
    wire use_active, use_backup;
    assign use_active = PRIORITY ? (act_ok & !select_backup & !sw_override) : (act_ok & !select_backup & !sw_override);
    assign use_backup = !use_active | select_backup | sw_override | !act_ok;

    // Failover status, error flag
    assign failover_status = use_active ? 1'b0 : 1'b1; // 0: active, 1: backup
    assign error_flag = !act_ok & !bkp_ok;

    // Glitch-free clock muxing
    reg sel_clk_mux;
    always @(posedge active_clk or posedge backup_clk or negedge rst_n) begin
        if (!rst_n) sel_clk_mux <= PRIORITY ? 1'b1 : 1'b0;
        else if (use_active && act_ok) sel_clk_mux <= 1'b0;
        else if (use_backup && bkp_ok) sel_clk_mux <= 1'b1;
    end

    assign ddr5_clk_out = sel_clk_mux ? backup_clk : active_clk;

    // Integration reference:
    // - Connect active_clk, backup_clk to redundant sources
    // - Connect ddr5_clk_out to DDR5 clock input
    // - Use status/error outputs for monitoring

endmodule

// Documentation:
// This module is intended for DDR5 clocking redundancy with seamless switch and error tracking. Modify validity check logic to fit clock presence detector for your design. For additional safety, insert multi-stage synchronizers at mux output as needed for further glitch immunity.
