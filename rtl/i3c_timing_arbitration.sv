// i3c_timing_arbitration.sv
// Synthesizable I3C Timing Constraint, Error Detection, and Arbitration Block
//
// Ports and bus timing constraint configuration are thoroughly documented. Integrate with top-level I3C designs.
//
// Author: [Your Name]

module i3c_timing_arbitration #(
    // Timing and Arbitration Parameters (adjust as per I3C spec or target frequency)
    parameter integer tSCL_MIN_HIGH   = 60,   // Min SCL HIGH period (ns)
    parameter integer tSCL_MIN_LOW    = 130,  // Min SCL LOW period (ns)
    parameter integer tSDA_SETUP      = 20,   // Min SDA setup time (ns)
    parameter integer tSDA_HOLD       = 10,   // Min SDA hold time (ns)
    parameter integer CLK_PERIOD_NS   = 10,   // System clock period (ns) for timing ref
    parameter integer N_MASTERS       = 2     // Number of potential masters for arbitration
) (
    input  logic        clk,          // System clock, used for timing measurements
    input  logic        rst_n,        // Active-low synchronous reset
    input  logic        scl_i,        // I3C SCL input (from bus)
    input  logic        sda_i,        // I3C SDA input (from bus)
    input  logic [N_MASTERS-1:0] m_req,      // One-hot: which masters are requesting bus?
    input  logic [N_MASTERS-1:0] m_nack,     // One-hot: NACK issued by masters
    input  logic [N_MASTERS-1:0] arb_priority, // Lower value = Higher priority

    output logic        timing_violation,     // Pulses high on setup/hold or period/freq violations
    output logic        arbitration_lost,     // Pulse on master losing arbitration
    output logic        bus_error,            // Pulse on bus error/detected fault
    output logic        bus_clear,            // Pulse to trigger bus clear sequence
    output logic [N_MASTERS-1:0] gain_bus,   // Grant vector: 1-hot -- which master wins arbitration
    output logic [31:0] violation_capture,   // Encoded timing violation for debug
    output logic [7:0]  arbitration_status   // Encoded arbitration/fault code for debug
);
    // --- Internal signals ---
    
    typedef enum logic [3:0] {
        NO_ERR    = 4'd0,
        SCL_HIGH  = 4'd1,
        SCL_LOW   = 4'd2,
        SDA_SETUP = 4'd3,
        SDA_HOLD  = 4'd4,
        FREQ_VIOL = 4'd5
    } timing_viol_e;
    timing_viol_e timing_fault;
    logic scl_prev, sda_prev;
    integer scl_high_cnt, scl_low_cnt, sda_setup_cnt, sda_hold_cnt;
    logic scl_rising, scl_falling, sda_rising, sda_falling;

    // --- Edge detection for SCL, SDA ---
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            scl_prev <= 0;
            sda_prev <= 0;
        end else begin
            scl_prev <= scl_i;
            sda_prev <= sda_i;
        end
    end
    assign scl_rising = (scl_i & ~scl_prev);
    assign scl_falling = (~scl_i & scl_prev);
    assign sda_rising = (sda_i & ~sda_prev);
    assign sda_falling = (~sda_i & sda_prev);

    // --- Timing checks: SCL period, SDA setup/hold ---
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            scl_high_cnt <= 0;
            scl_low_cnt <= 0;
            sda_setup_cnt <= 0;
            sda_hold_cnt <= 0;
            timing_violation <= 0;
            timing_fault <= NO_ERR;
        end else begin
            // SCL high/low duration
            if (scl_i) scl_high_cnt <= scl_high_cnt + 1;
            else scl_high_cnt <= 0;
            if (!scl_i) scl_low_cnt <= scl_low_cnt + 1;
            else scl_low_cnt <= 0;

            // Pulse width violations
            if (scl_falling && (scl_high_cnt * CLK_PERIOD_NS < tSCL_MIN_HIGH)) begin
                timing_violation <= 1;
                timing_fault <= SCL_HIGH;
            end else if (scl_rising && (scl_low_cnt * CLK_PERIOD_NS < tSCL_MIN_LOW)) begin
                timing_violation <= 1;
                timing_fault <= SCL_LOW;
            end else begin
                timing_violation <= 0;
                timing_fault <= NO_ERR;
            end
            // SDA setup/hold time check
            if (sda_rising || sda_falling) begin
                if (scl_i) begin
                    // Setup: SDA must transition min tSDA_SETUP before SCL rising
                    if (sda_setup_cnt * CLK_PERIOD_NS < tSDA_SETUP) begin
                        timing_violation <= 1;
                        timing_fault <= SDA_SETUP;
                    end
                end else begin
                    // Hold: SDA must hold min tSDA_HOLD after SCL falling
                    if (sda_hold_cnt * CLK_PERIOD_NS < tSDA_HOLD) begin
                        timing_violation <= 1;
                        timing_fault <= SDA_HOLD;
                    end
                end
                sda_setup_cnt <= 0;
                sda_hold_cnt <= 0;
            end else begin
                sda_setup_cnt <= sda_setup_cnt + 1;
                sda_hold_cnt <= sda_hold_cnt + 1;
            end
        end
    end

    // --- Bus Error, Recovery, Bus Clear ---
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bus_error <= 0;
            bus_clear <= 0;
        end else begin
            if (timing_violation) begin
                bus_error <= 1;
                bus_clear <= 1; // Initiate I3C bus clear
            end else begin
                bus_error <= 0;
                bus_clear <= 0;
            end
        end
    end
    // --- Arbitration Logic (priority-based, multi-master) ---
    // Simple example: grant to requesting master with lowest arb_priority vector, break ties using m_nack
    always_comb begin
        arbitration_lost   = 0;
        gain_bus          = '0;
        arbitration_status = 0;
        if (|m_req) begin
            // Get the master(s) with request and minimal priority
            integer i, min_idx, min_pri;
            min_pri = 255;
            min_idx = 0;
            for (i=0; i<N_MASTERS; i++) begin
                if (m_req[i] && arb_priority[i] < min_pri) begin
                    min_pri = arb_priority[i];
                    min_idx = i;
                end
            end
            // Arbitration: NACK overrides, if any
            if (m_nack[min_idx]) begin
                arbitration_lost = 1;
                arbitration_status = 8'h01; // NACK won
            end else begin
                gain_bus = (1 << min_idx);
                arbitration_status = 8'h10 + min_idx; // Grant code
            end
        end
    end
    // --- Violation Debug Capture ---
    always_comb begin
        violation_capture = {28'd0, timing_fault};
    end
endmodule

//
// Integration/Usage:
//  - Instantiate this module in your I3C protocol block or top-level.
//  - Connect SCL/SDA to physical lines being monitored.
//  - Set timing parameters for your application's clock and I3C speed mode.
//  - Use outputs (timing_violation, bus_error, bus_clear) to trigger corrective or reset logic.
//  - Provide bus master request/priority/NACK sources for correct multi-master arbitration.
