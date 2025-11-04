//============================================================================
// Module: error_reporter
// Description: ECC Error and Diagnostic Reporter
//              Aggregates error status, provides status counters,
//              inject/error test support, and reports syndrome/diagnostics
//
// Parameters:
//   - DATA_WIDTH: DRAM data width (default: 64)
//   - ECC_WIDTH: ECC check bit width (default: 8)
//
// Features:
//   - Counts and classifies ECC errors
//   - Status flags for current and latched errors
//   - Syndrome reports, injection/test support
//   - Diagnostics for SECDED pipeline
//   - Constrained-random and coverage assertions
//============================================================================

module error_reporter #(
    parameter int DATA_WIDTH = 64,
    parameter int ECC_WIDTH  = 8
) (
    // Clock and Reset
    input  logic clk,
    input  logic rst_n,

    // Inputs from SECDED pipeline
    input  logic error_single,
    input  logic error_double,
    input  logic error_corrected,
    input  logic [ECC_WIDTH-1:0] syndrome,
    input  logic pipeline_blocked,
    input  logic corrected_valid,
    input  logic diagnosed,
    input  logic inject_error,   // error injection (for test)
    input  logic [DATA_WIDTH-1:0] inject_data,

    // Status Outputs
    output logic status_single_error,
    output logic status_double_error,
    output logic status_corrected,
    output logic status_blocked,
    output logic [31:0] single_error_count,
    output logic [31:0] double_error_count,
    output logic [31:0] corrected_count,
    output logic [31:0] injected_count,
    output logic [ECC_WIDTH-1:0] last_syndrome
);

    // Latch current flags
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            status_single_error <= 1'b0;
            status_double_error <= 1'b0;
            status_corrected    <= 1'b0;
            status_blocked      <= 1'b0;
        end else begin
            status_single_error <= error_single;
            status_double_error <= error_double;
            status_corrected    <= error_corrected;
            status_blocked      <= pipeline_blocked;
        end
    end

    // Syndrome and Diagnostics Latching
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            last_syndrome <= '0;
        end else if (corrected_valid || diagnosed) begin
            last_syndrome <= syndrome;
        end
    end

    // Error counters
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            single_error_count <= 0;
            double_error_count <= 0;
            corrected_count    <= 0;
            injected_count     <= 0;
        end else begin
            if (error_single && corrected_valid) single_error_count <= single_error_count + 1;
            if (error_double && corrected_valid) double_error_count <= double_error_count + 1;
            if (error_corrected && corrected_valid) corrected_count <= corrected_count + 1;
            if (inject_error) injected_count <= injected_count + 1;
        end
    end

    //========================================================================
    // Assertions and Coverage
    //========================================================================
`ifdef SIMULATION
    initial begin
        assert (DATA_WIDTH == 64 || DATA_WIDTH == 32 || DATA_WIDTH == 128)
            else $error("Unsupported DATA_WIDTH for error_reporter");
    end
    property p_syndrome_latches_on_err;
        @(posedge clk) disable iff (!rst_n)
        (corrected_valid || diagnosed) |-> ##1 last_syndrome == syndrome;
    endproperty
    assert property (p_syndrome_latches_on_err)
        else $error("Syndrome not reported on error event");
    covergroup cg_error_types @(posedge clk);
        option.per_instance = 1;
        single: coverpoint error_single { bins yes = {1}; bins no = {0}; }
        double: coverpoint error_double { bins yes = {1}; bins no = {0}; }
        corrected: coverpoint error_corrected { bins yes = {1}; bins no = {0}; }
        inj: coverpoint inject_error { bins yes = {1}; bins no = {0}; }
    endgroup
    cg_error_types cg_types = new();
`endif

endmodule
//============================================================================
// End of error_reporter module
//============================================================================
