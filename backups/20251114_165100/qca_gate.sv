/**
 * DDR5 QCA (Quad Command/Address) Gating Module
 * Module: qca_gate.sv
 *
 * Description:
 *   Implements configurable QCA gating logic to support advanced command/address
 *   flow control in DDR5 RCD (Register Clock Driver). Provides enable signals,
 *   dynamic gating masks, pipeline control, and error/overflow reporting.
 *
 * Features:
 *   - Parameterized QCA width and interface configuration
 *   - Dynamic gating mask support for selective command blocking
 *   - Pipeline stage control and depth management
 *   - Overflow and error detection and reporting
 *   - Integration with ca_distributor for flow control
 *   - Internal buffering and flow control mechanisms
 *
 * Parameters:
 *   - QCA_WIDTH: Width of QCA command/address bus (default: 4)
 *   - GATING_DEPTH: Depth of gating pipeline stages (default: 2)
 *   - BUFFER_DEPTH: Internal buffer depth for command queuing (default: 8)
 */

module qca_gate #(
    parameter int QCA_WIDTH      = 4,    // Quad Command/Address bus width
    parameter int GATING_DEPTH   = 2,    // Number of gating pipeline stages
    parameter int BUFFER_DEPTH   = 8     // Internal buffer depth
) (
    // Clock and Reset
    input  logic                    clk,
    input  logic                    rst_n,

    // QCA Command/Address Input Interface
    input  logic [QCA_WIDTH-1:0]   qca_cmd_in,      // Incoming QCA command/address
    input  logic                    qca_valid_in,    // Input valid signal
    output logic                    qca_ready_in,    // Input ready (backpressure)

    // QCA Gating Control
    input  logic                    gating_enable,   // Global gating enable
    input  logic [QCA_WIDTH-1:0]   gating_mask,     // Dynamic gating mask (1=block, 0=allow)
    input  logic [$clog2(GATING_DEPTH)-1:0] gating_depth_cfg,  // Configure gating depth

    // Pipeline Control
    input  logic                    pipeline_stall,  // Stall entire pipeline
    input  logic                    pipeline_flush,  // Flush pipeline stage
    output logic                    pipeline_empty,  // Pipeline is empty

    // QCA Command/Address Output Interface
    output logic [QCA_WIDTH-1:0]   qca_cmd_out,     // Gated QCA command/address
    output logic                    qca_valid_out,   // Output valid signal
    input  logic                    qca_ready_out,   // Output ready (downstream)

    // ca_distributor Integration
    output logic [QCA_WIDTH-1:0]   ca_cmd,          // Command/Address to distributor
    output logic                    ca_valid,        // Valid signal to distributor
    input  logic                    ca_ready,        // Backpressure from distributor

    // Error and Overflow Reporting
    output logic                    buffer_overflow, // Buffer overflow detected
    output logic                    gating_error,    // Gating logic error
    output logic [$clog2(BUFFER_DEPTH)-1:0] buffer_occupancy, // Current buffer usage

    // Status and Debug
    output logic                    gating_active,   // Gating is currently active
    output logic                    cmd_blocked,     // Current command is blocked by mask
    output logic [GATING_DEPTH-1:0] pipeline_stages // Debug: pipeline stage occupancy
);

    // Internal parameters
    localparam int ADDR_WIDTH = $clog2(BUFFER_DEPTH);
    localparam int DEPTH_WIDTH = $clog2(GATING_DEPTH);

    // Internal signals
    logic [QCA_WIDTH-1:0]          buffer_data [BUFFER_DEPTH-1:0];
    logic [BUFFER_DEPTH-1:0]       buffer_valid;
    logic [ADDR_WIDTH-1:0]         wr_ptr, rd_ptr;
    logic [ADDR_WIDTH:0]           buffer_count;
    logic                          buffer_full, buffer_empty_int;

    // Gating pipeline stages
    logic [QCA_WIDTH-1:0]          gating_pipe_data [GATING_DEPTH-1:0];
    logic                          gating_pipe_valid [GATING_DEPTH-1:0];
    logic [GATING_DEPTH-1:0]       gating_pipe_stall;
    logic [DEPTH_WIDTH-1:0]        active_gating_depth;

    // Mask application
    logic [QCA_WIDTH-1:0]          masked_cmd;
    logic                          cmd_gated;

    // Error tracking
    logic                          overflow_detected;
    logic                          error_detected;

    // ====== BUFFER MANAGEMENT ======

    // Write pointer management
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= '0;
        end else if (qca_valid_in && qca_ready_in && !pipeline_flush) begin
            wr_ptr <= (wr_ptr == BUFFER_DEPTH - 1) ? '0 : wr_ptr + 1;
        end
    end

    // Read pointer management
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_ptr <= '0;
        end else if (qca_valid_out && qca_ready_out && !pipeline_flush) begin
            rd_ptr <= (rd_ptr == BUFFER_DEPTH - 1) ? '0 : rd_ptr + 1;
        end
    end

    // Buffer counter for occupancy tracking
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            buffer_count <= '0;
        end else begin
            case ({qca_valid_in && qca_ready_in, qca_valid_out && qca_ready_out})
                2'b01:   buffer_count <= buffer_count - 1;  // Read only
                2'b10:   buffer_count <= buffer_count + 1;  // Write only
                2'b11:   buffer_count <= buffer_count;      // Read and write
                default: buffer_count <= buffer_count;      // No change
            endcase
        end
    end

    // Buffer full and empty conditions
    assign buffer_full       = (buffer_count == BUFFER_DEPTH);
    assign buffer_empty_int  = (buffer_count == '0);

    // Input ready signal (backpressure)
    assign qca_ready_in = gating_enable && !buffer_full && !pipeline_flush;

    // Write to buffer
    always_ff @(posedge clk) begin
        if (qca_valid_in && qca_ready_in) begin
            buffer_data[wr_ptr] <= qca_cmd_in;
            buffer_valid[wr_ptr] <= 1'b1;
        end
    end

    // Read from buffer
    always_comb begin
        if (!buffer_empty_int) begin
            masked_cmd = buffer_data[rd_ptr];
        end else begin
            masked_cmd = '0;
        end
    end

    // ====== GATING LOGIC ======

    // Apply gating mask to command
    always_comb begin
        // Check if any masked bit is set (command is blocked)
        cmd_gated = |(qca_cmd_in & gating_mask);
    end

    // Gating depth configuration
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            active_gating_depth <= GATING_DEPTH[DEPTH_WIDTH-1:0];
        end else begin
            active_gating_depth <= gating_depth_cfg;
        end
    end

    // ====== PIPELINE STAGES ======

    // Generate gating pipeline stages based on depth
    genvar i;
    generate
        for (i = 0; i < GATING_DEPTH; i++) begin : gating_pipeline
            // Stall logic for pipeline
            assign gating_pipe_stall[i] = pipeline_stall || 
                                          (i < (GATING_DEPTH - 1) ? gating_pipe_stall[i+1] : !qca_ready_out);

            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    gating_pipe_valid[i] <= 1'b0;
                    gating_pipe_data[i]  <= '0;
                end else if (pipeline_flush) begin
                    gating_pipe_valid[i] <= 1'b0;
                    gating_pipe_data[i]  <= '0;
                end else if (!gating_pipe_stall[i]) begin
                    if (i == 0) begin
                        // First stage: read from buffer
                        gating_pipe_valid[i] <= !buffer_empty_int && gating_enable;
                        gating_pipe_data[i]  <= masked_cmd;
                    end else begin
                        // Subsequent stages: propagate from previous stage
                        gating_pipe_valid[i] <= gating_pipe_valid[i-1];
                        gating_pipe_data[i]  <= gating_pipe_data[i-1];
                    end
                end
            end
        end
    endgenerate

    // ====== OUTPUT ASSIGNMENT ======

    // Output from final pipeline stage
    always_comb begin
        if (active_gating_depth == '0) begin
            // Bypass mode: direct from buffer
            qca_cmd_out   = masked_cmd;
            qca_valid_out = !buffer_empty_int && gating_enable;
        end else begin
            // Normal mode: from pipeline
            qca_cmd_out   = gating_pipe_data[GATING_DEPTH-1];
            qca_valid_out = gating_pipe_valid[GATING_DEPTH-1];
        end
    end

    // ca_distributor integration (pass through with gating applied)
    assign ca_cmd   = qca_cmd_out;
    assign ca_valid = qca_valid_out && gating_enable;

    // Pipeline ready control
    always_comb begin
        if (active_gating_depth == '0) begin
            // Bypass mode
            qca_ready_out = ca_ready && !cmd_gated && gating_enable;
        end else begin
            // Normal mode: ready when final stage can accept
            qca_ready_out = !gating_pipe_stall[GATING_DEPTH-1];
        end
    end

    // ====== ERROR AND OVERFLOW DETECTION ======

    // Overflow detection: trying to write when buffer full
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            overflow_detected <= 1'b0;
        end else if (qca_valid_in && buffer_full && !qca_ready_in) begin
            overflow_detected <= 1'b1;
        end else if (error_detected) begin
            overflow_detected <= 1'b0;  // Clear on error acknowledge
        end
    end

    // General gating error detection
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            error_detected <= 1'b0;
        end else begin
            // Error if: gating active but command gets masked or buffer overflow
            error_detected <= overflow_detected || 
                             (gating_enable && qca_valid_out && cmd_gated);
        end
    end

    // Error outputs
    assign buffer_overflow = overflow_detected;
    assign gating_error    = error_detected;
    assign buffer_occupancy = buffer_count[ADDR_WIDTH-1:0];

    // ====== STATUS SIGNALS ======

    // Gating is active when enabled and pipeline has data
    assign gating_active = gating_enable && !buffer_empty_int;

    // Command blocked by mask
    assign cmd_blocked = cmd_gated && gating_enable;

    // Pipeline stage occupancy (debug)
    assign pipeline_stages[0] = !buffer_empty_int;
    generate
        for (i = 1; i < GATING_DEPTH; i++) begin : pipeline_stage_status
            assign pipeline_stages[i] = gating_pipe_valid[i-1];
        end
    endgenerate

    // Pipeline empty status
    assign pipeline_empty = buffer_empty_int && ~(|gating_pipe_valid);

endmodule
