// timing_check_agg.sv
// Aggregates timing check results from all submodules, tallies violation counters, and exports summary/statistics
// For DDR5_RCD_Prod testbench and firmware integration

module timing_check_agg #(parameter N_MODULES = 8) (
    input  logic              clk,
    input  logic              rst_n,
    input  logic [N_MODULES-1:0] violation_flags, 
    input  logic [N_MODULES-1:0][15:0] timing_violation_count_in, 
    output logic [N_MODULES-1:0][15:0] timing_violation_count_out, 
    output logic [15:0]     timing_total_violations, 
    output logic            timing_summary_violation, 
    output logic [N_MODULES-1:0] timing_last_violation, 
    output logic            timing_new_violation // Pulse: any new violation event
);
    // Summary statistics aggregation
    logic [N_MODULES-1:0]   violation_pulse;
    logic [N_MODULES-1:0][15:0] violation_counter_reg;
    logic [15:0]            total_reg;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            violation_counter_reg <= '0;
            total_reg <= '0;
            timing_last_violation <= '0;
        end else begin
            total_reg <= '0;
            for (int i = 0; i < N_MODULES; i++) begin
                // Update counters
                if (violation_flags[i]) begin
                    violation_counter_reg[i] <= timing_violation_count_in[i];
                    total_reg <= total_reg + 1;
                    timing_last_violation[i] <= 1'b1;
                end else begin
                    timing_last_violation[i] <= 1'b0;
                end
            end
        end
    end

    assign timing_total_violations = total_reg;
    assign timing_violation_count_out = violation_counter_reg;
    assign timing_summary_violation = |violation_flags;
    assign timing_new_violation = |timing_last_violation;

endmodule

// Documentation:
// N_MODULES: Number of timing check submodules integrated.
// violation_flags: Asserted by submodules on timing violation detection.
// timing_violation_count_in: Per-module running violation count (expands as needed).
// timing_last_violation: One-cycle pulse per module for scoreboard/testbench event capture.
// timing_total_violations: Aggregated count from all modules.
// timing_summary_violation: Summary, high if any violation occurred (use for interrupts/alerts).
// timing_new_violation: High for one cycle when any violation occurs (use for fast logging).
