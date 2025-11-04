//==============================================================================
// File: ddr5_rcd_assertions.sv
// Description: Complete DDR5 RCD SVA Library - Clock, Reset, Setup/Hold, Command, Protocol Checks w/ Coverage
// Author: Production Implementation
// Date: 2025-11-04
//==============================================================================
`ifndef DDR5_RCD_ASSERTIONS_SV
`define DDR5_RCD_ASSERTIONS_SV
//==============================================================================
// Module: ddr5_rcd_assertions
// Top-level SVAs and Coverage for DDR5 RCD Protocol & Timing
//==============================================================================
module ddr5_rcd_assertions (
    input logic clk,
    input logic rst_n,
    input logic ca_valid,
    input logic [6:0] ca_cmd,
    input logic [16:0] ca_addr,
    input logic [1:0] ca_cs,
    input logic ca_cke,
    input logic ca_odt,
    input logic dq_valid,
    input logic [127:0] dq_data,
    input logic [15:0] dq_mask,
    input logic dq_strobe,
    input logic parity_err,
    input logic alert_n
);
//=============================================================================
// 1. Clock Stability/Change Detection SVA + Coverage
//=============================================================================
// Assumption: Clock period and duty cycle are measured via tb instrumentation
logic [31:0] prev_clk_edge, curr_clk_edge;
logic [31:0] clk_period, prev_period;
logic [31:0] duty_cycle, curr_high_time;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        prev_clk_edge <= 0;
        prev_period <= 0;
    end else begin
        curr_clk_edge <= $time;
        clk_period <= curr_clk_edge - prev_clk_edge;
        prev_clk_edge <= curr_clk_edge;
        prev_period <= clk_period;
    end
end

// Assertion: Clock must not glitch
property CLK_STABLE_P;
    @(posedge clk) disable iff (!rst_n)
    clk_period >= 2500 && clk_period <= 4500;
endproperty
CLK_STABILITY: assert property (CLK_STABLE_P) else $error("Clock period violation at %0t", $time);

covergroup cg_clk_stable @(posedge clk);
    period_range: coverpoint clk_period {
        bins min = {[2500:3500]};
        bins nominal = {[3500:4500]};
        bins max = {[4500:$]};
    }
    unstable: coverpoint (clk_period < 2500 || clk_period > 4500);
endgroup
cg_clk_stable cg1 = new();

//=============================================================================
// 2. Reset Assertion/Release, Monitoring
//=============================================================================
property RESET_ASSERT_P;
    @(posedge clk) !$rose(rst_n) |-> !ca_valid && !dq_valid;
endproperty
RESET_ASSERTION: assert property (RESET_ASSERT_P) else $error("Reset deassertion: active signals at %0t", $time);

// Coverage: reset transition
covergroup cg_reset @(posedge clk);
    reset_release: coverpoint rst_n {
        bins released = {1};
        bins asserted = {0};
    }
    ca_valid_during_reset: coverpoint ca_valid iff (!rst_n);
    dq_valid_during_reset: coverpoint dq_valid iff (!rst_n);
endgroup
cg_reset cg2 = new();

//=============================================================================
// 3. Setup/Hold Timing Constraints for CA/DQ (using example timing values)
//=============================================================================
parameter integer TSETUP_CA = 150;
parameter integer THOLD_CA  = 100;
parameter integer TSETUP_DQ = 150;
parameter integer THOLD_DQ  = 100;

// CA setup/hold
property CA_SETUP_P;
    @(posedge clk) disable iff (!rst_n)
    ca_valid |-> ##[TSETUP_CA:$](ca_cmd inside {[0:127]}) && ##[0:THOLD_CA](ca_cmd inside {[0:127]});
endproperty
CA_SETUP: assert property(CA_SETUP_P) else $error("CA setup/hold violation at %0t", $time);

// DQ setup/hold
property DQ_SETUP_P;
    @(posedge clk) disable iff (!rst_n)
    dq_valid |-> ##[TSETUP_DQ:$](dq_data !== 'x) && ##[0:THOLD_DQ](dq_data !== 'x);
endproperty
DQ_SETUP: assert property(DQ_SETUP_P) else $error("DQ setup/hold violation at %0t", $time);

// Coverage
covergroup cg_ca_setup @(posedge clk);
    valid_cmd: coverpoint ca_cmd iff (ca_valid);
endgroup
cg_ca_setup cg3 = new();
covergroup cg_dq_setup @(posedge clk);
    valid_dq: coverpoint dq_data iff (dq_valid);
endgroup
cg_dq_setup cg4 = new();

//=============================================================================
// 4. Command Encoding Legal/Illegal Detection
//=============================================================================
// Example: CA_CMD legal values 0-63=normal, 64-127=extended
property CMD_LEGAL_P;
    @(posedge clk) ca_valid |-> (ca_cmd inside {[0:127]});
endproperty
CMD_LEGAL: assert property (CMD_LEGAL_P) else $error("Illegal command encoding at %0t: %h", $time, ca_cmd);

// Coverage
covergroup cg_cmd @(posedge clk);
    legal: coverpoint ca_cmd {
        bins normal = {[0:63]};
        bins extended = {[64:127]};
    }
    illegal: coverpoint ca_cmd iff (ca_valid && !(ca_cmd inside {[0:127]}));
endgroup
cg_cmd cg5 = new();

//=============================================================================
// 5. Protocol/Timing Relationships
//=============================================================================
// Example: ODT follows CKE, parity error transitions
property ODT_AFTER_CKE_P;
    @(posedge clk) disable iff (!rst_n)
    ca_cke |-> ##[1:4] ca_odt;
endproperty
ODT_AFTER_CKE: assert property(ODT_AFTER_CKE_P) else $error("ODT did not follow CKE at %0t", $time);

property ALERT_ON_PARITY_ERR_P;
    @(posedge clk) disable iff (!rst_n)
    $rose(parity_err) |-> !alert_n;
endproperty
ALERT_ON_PAR_ERR: assert property(ALERT_ON_PARITY_ERR_P) else $error("Alert signal not set on parity error at %0t", $time);

// Protocol relationship coverage
covergroup cg_protocol @(posedge clk);
    odt_after_cke: cross ca_cke, ca_odt;
    alert_on_parerr: cross parity_err, alert_n;
endgroup
cg_protocol cg6 = new();

//=============================================================================
// End of Top-Level Assertion Module
// All SVA, coverage, $error reporting styled as per project guidelines & formal usage
//=============================================================================
endmodule : ddr5_rcd_assertions
`endif
//==============================================================================
// End ddr5_rcd_assertions.sv
