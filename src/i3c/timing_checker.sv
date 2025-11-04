//============================================================================
// Module: timing_checker
// Description: I3C Timing Constraint Checker
//              Monitors and validates I3C bus timing parameters to ensure
//              compliance with I3C specification requirements
//============================================================================
module timing_checker (
    // Clock and Reset
    input  logic        clk,
    input  logic        rst_n,
    // I3C Bus Signals
    input  logic        scl,           // Serial Clock
    input  logic        sda,           // Serial Data
    // Mode Configuration
    input  logic [1:0]  speed_mode,    // 0: SDR, 1: HDR-DDR, 2: HDR-TSP
    input  logic        enable_check,
    // Timing Violation Outputs
    output logic        setup_violation,
    output logic        hold_violation,
    output logic        scl_low_violation,
    output logic        scl_high_violation,
    output logic        start_setup_violation,
    output logic        stop_setup_violation,
    output logic        spike_detected,
    // Timing Measurement Outputs
    output logic [15:0] scl_period_ns,
    output logic [15:0] sda_setup_time_ns,
    output logic [15:0] sda_hold_time_ns,
    // Violation Counter
    output logic [7:0]  violation_count
);
    //========================================================================
    // Timing Parameter Definitions (in ns)
    //========================================================================
    // I3C SDR Mode Timing Requirements
    localparam TSETUP_SDR_MIN       = 3;    // SDA setup time (min)
    localparam THOLD_SDR_MIN        = 0;    // SDA hold time (min)
    localparam TSCL_LOW_SDR_MIN     = 200;  // SCL low period (min)
    localparam TSCL_HIGH_SDR_MIN    = 41;   // SCL high period (min)
    localparam TSTART_SETUP_MIN     = 260;  // START setup time (min)
    localparam TSTOP_SETUP_MIN      = 260;  // STOP setup time (min)
    // I3C HDR-DDR Mode Timing Requirements
    localparam TSETUP_DDR_MIN       = 2;    // SDA setup time (min)
    localparam THOLD_DDR_MIN        = 2;    // SDA hold time (min)
    localparam TSCL_LOW_DDR_MIN     = 100;  // Example HDR-DDR values
    localparam TSCL_HIGH_DDR_MIN    = 50;   // Example HDR-DDR values
    // Spike Filter Parameters
    localparam SPIKE_FILTER_NS      = 50;   // Spike filter width

    //========================================================================
    // Internal Signals
    //========================================================================
    logic [15:0] scl_low_count, scl_high_count, scl_period_count;
    logic [15:0] sda_stable_count, sda_hold_count;
    logic        scl_prev, sda_prev;
    logic        scl_rising, scl_falling, sda_change;
    logic        start_condition, stop_condition;
    logic        scl_glitch, sda_glitch;
    logic [15:0] tsetup_min, thold_min, tscl_low_min, tscl_high_min;
    logic        crossing_detected;

    //========================================================================
    // Edge Detection
    //========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            scl_prev <= 1'b1;
            sda_prev <= 1'b1;
        end else begin
            scl_prev <= scl;
            sda_prev <= sda;
        end
    end
    assign scl_rising  = scl & ~scl_prev;
    assign scl_falling = ~scl & scl_prev;
    assign sda_change  = sda ^ sda_prev;
    //========================================================================
    // START and STOP Condition Detection
    //========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            start_condition <= 1'b0;
            stop_condition  <= 1'b0;
        end else begin
            start_condition <= (sda_prev && ~sda && scl);
            stop_condition  <= (~sda_prev && sda && scl);
        end
    end
    //========================================================================
    // Timing Threshold Configuration
    //========================================================================
    always_comb begin
        case (speed_mode)
            2'b00: begin  // SDR Mode
                tsetup_min    = TSETUP_SDR_MIN;
                thold_min     = THOLD_SDR_MIN;
                tscl_low_min  = TSCL_LOW_SDR_MIN;
                tscl_high_min = TSCL_HIGH_SDR_MIN;
            end
            2'b01: begin  // HDR-DDR Mode
                tsetup_min    = TSETUP_DDR_MIN;
                thold_min     = THOLD_DDR_MIN;
                tscl_low_min  = TSCL_LOW_DDR_MIN;
                tscl_high_min = TSCL_HIGH_DDR_MIN;
            end
            default: begin
                tsetup_min    = TSETUP_SDR_MIN;
                thold_min     = THOLD_SDR_MIN;
                tscl_low_min  = TSCL_LOW_SDR_MIN;
                tscl_high_min = TSCL_HIGH_SDR_MIN;
            end
        endcase
    end
    //========================================================================
    // SCL Period, Low & High Measurement
    //========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            scl_high_count    <= 16'd0;
            scl_low_count     <= 16'd0;
            scl_period_count  <= 16'd0;
        end else begin
            // SCL period counting
            scl_period_count <= scl_period_count + 1;
            if (scl_rising || scl_falling) scl_period_count <= 16'd0;
            scl_period_ns <= scl_period_count;
            // SCL low counting
            if (~scl)       scl_low_count  <= scl_low_count + 1;
            else            scl_low_count  <= 16'd0;
            // SCL high counting
            if (scl)        scl_high_count <= scl_high_count + 1;
            else            scl_high_count <= 16'd0;
        end
    end
    //========================================================================
    // SCL Pulse Width Checkers
    //========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            scl_low_violation  <= 1'b0;
            scl_high_violation <= 1'b0;
        end else begin
            if (enable_check && scl_rising && scl_low_count < tscl_low_min)
                scl_low_violation <= 1'b1;
            else
                scl_low_violation <= 1'b0;
            if (enable_check && scl_falling && scl_high_count < tscl_high_min)
                scl_high_violation <= 1'b1;
            else
                scl_high_violation <= 1'b0;
        end
    end
    //========================================================================
    // SDA Setup Time Checker
    //========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sda_stable_count <= 16'd0;
        end else begin
            if (sda_change) begin
                sda_stable_count <= 16'd0;
            end else if (!scl_rising) begin
                if (sda_stable_count != 16'hFFFF)
                    sda_stable_count <= sda_stable_count + 16'd1;
            end
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sda_setup_time_ns <= 16'd0;
        end else begin
            if (scl_rising)
                sda_setup_time_ns <= sda_stable_count;
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            setup_violation <= 1'b0;
        end else begin
            if (enable_check && scl_rising) begin
                setup_violation <= (sda_stable_count < tsetup_min);
            end else begin
                setup_violation <= 1'b0;
            end
        end
    end
    assert property (@(posedge clk) disable iff (!rst_n || !enable_check)
        (scl_rising |-> (sda_stable_count >= tsetup_min))
    ) else $error("[TIMING_VIOLATION] SDA Setup Time Violation: %0d ns < %0d ns", sda_stable_count, tsetup_min);
    covergroup setup_time_cg @(posedge clk);
        option.per_instance = 1;
        setup_time: coverpoint sda_setup_time_ns {
            bins zero        = {0};
            bins minimal     = {[1:2]};
            bins adequate    = {[3:10]};
            bins comfortable = {[11:50]};
            bins large       = {[51:$]};
        }
        speed: coverpoint speed_mode {
            bins sdr     = {2'b00};
            bins hdr_ddr = {2'b01};
            bins others  = default;
        }
        setup_x_speed: cross setup_time, speed;
    endgroup
    setup_time_cg setup_cg_inst = new();
    //========================================================================
    // SDA Hold Time Checker
    //========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sda_hold_count <= 16'd0;
        end else begin
            if (scl_falling)  sda_hold_count <= 16'd0;
            else if (!sda_change && ~scl) begin
                if (sda_hold_count != 16'hFFFF)
                    sda_hold_count <= sda_hold_count + 16'd1;
            end
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sda_hold_time_ns <= 16'd0;
        end else begin
            if (sda_change && ~scl)
                sda_hold_time_ns <= sda_hold_count;
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            hold_violation <= 1'b0;
        end else begin
            if (enable_check && sda_change && ~scl)
                hold_violation <= (sda_hold_count < thold_min);
            else
                hold_violation <= 1'b0;
        end
    end
    assert property (@(posedge clk) disable iff (!rst_n || !enable_check)
        (sda_change && ~scl |-> (sda_hold_count >= thold_min))
    ) else $error("[TIMING_VIOLATION] SDA Hold Time Violation: %0d ns < %0d ns", sda_hold_count, thold_min);
    covergroup hold_time_cg @(posedge clk);
        option.per_instance = 1;
        hold_time: coverpoint sda_hold_time_ns {
            bins zero      = {0};
            bins minimal   = {[1:2]};
            bins adequate  = {[3:10]};
            bins comfortable={[11:50]};
            bins large     = {[51:$]};
        }
        speed: coverpoint speed_mode {
            bins sdr     = {2'b00};
            bins hdr_ddr = {2'b01};
            bins others  = default;
        }
        hold_x_speed: cross hold_time, speed;
    endgroup
    hold_time_cg hold_cg_inst = new();
    //========================================================================
    // Clock Domain Crossing Detection
    //========================================================================
    // For illustration, assume crossing_detected is set externally or by integration -- placeholder here
    assign crossing_detected = 1'b0; // TODO: add integration logic if needed
    //========================================================================
    // START/STOP Setup Time Checker (illustrative; spec may require more logic)
    //========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            start_setup_violation <= 1'b0;
            stop_setup_violation  <= 1'b0;
        end else begin
            if (enable_check && start_condition)
                start_setup_violation <= (sda_stable_count < TSTART_SETUP_MIN);
            else
                start_setup_violation <= 1'b0;
            if (enable_check && stop_condition)
                stop_setup_violation  <= (sda_stable_count < TSTOP_SETUP_MIN);
            else
                stop_setup_violation  <= 1'b0;
        end
    end
    //========================================================================
    // Simple Spike Filter (glitch detection)
    //========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            scl_glitch <= 1'b0;
            sda_glitch <= 1'b0;
            spike_detected <= 1'b0;
        end else begin
            scl_glitch <= (scl_rising && (scl_high_count < SPIKE_FILTER_NS)) ||
                          (scl_falling && (scl_low_count < SPIKE_FILTER_NS));
            sda_glitch <= sda_change && (sda_stable_count < SPIKE_FILTER_NS);
            spike_detected <= scl_glitch || sda_glitch;
        end
    end
    //========================================================================
    // Violation Counter
    //========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            violation_count <= 8'h00;
        end else if (enable_check) begin
            // Increment counter on any violation
            if (setup_violation || hold_violation || scl_low_violation ||
                scl_high_violation || start_setup_violation || stop_setup_violation) begin
                if (violation_count != 8'hFF)
                    violation_count <= violation_count + 8'd1;
            end
        end
    end
endmodule
