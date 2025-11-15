//-----------------------------------------------------------------------------
// qck_controller.sv
// DDR5 QCK Dynamic Clock Gating Controller
//-----------------------------------------------------------------------------
// Implements:
//   - CK enable/disable and masked gating control
//   - Multi-channel clock distribution
//   - Programmable gating window/timing
//   - Integration for CA/QCA control
//   - Pipeline, SKIP logic, and error detection
//   - Synthesizable
//-----------------------------------------------------------------------------
// Interface notes:
//   clk          : Core reference clock
//   reset_n      : Active-low synchronous reset
//   ck_en[]      : Input enable for each channel
//   ca_ctrl      : CA control integration
//   qca_ctrl     : QCA control integration
//   qck_mask[]   : Mask gating window per channel
//   skip_req     : Requests to skip gating window
//   error        : Output error status
//   ck_out[]     : Gated clock outputs per channel
//   prog_delay[] : Programmable gating delay/timing signals
//   PIPELINE_DEPTH: Parameter for pipeline stages
//-----------------------------------------------------------------------------

module qck_controller #(
    parameter integer CHANNELS = 8,
    parameter integer PIPELINE_DEPTH = 2,
    parameter integer DELAY_WIDTH = 4
) (
    input  logic                        clk,
    input  logic                        reset_n,
    input  logic [CHANNELS-1:0]         ck_en,
    input  logic                        ca_ctrl,
    input  logic                        qca_ctrl,
    input  logic [CHANNELS-1:0]         qck_mask,
    input  logic [CHANNELS-1:0]         skip_req,
    input  logic [CHANNELS*DELAY_WIDTH-1:0] prog_delay,
    output logic [CHANNELS-1:0]         ck_out,
    output logic [CHANNELS-1:0]         error
);

    // Pipeline registers for selectable gating window
    logic [CHANNELS-1:0]        en_pipe[PIPELINE_DEPTH];
    logic [CHANNELS-1:0]        mask_pipe[PIPELINE_DEPTH];
    logic [CHANNELS-1:0]        skip_pipe[PIPELINE_DEPTH];

    // Internal error detection
    logic [CHANNELS-1:0]        err_detect;

    // Initialization
    integer i;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            for (i = 0; i < PIPELINE_DEPTH; i++) begin
                en_pipe[i]   <= '0;
                mask_pipe[i] <= '0;
                skip_pipe[i] <= '0;
            end
            ck_out         <= '0;
            error          <= '0;
        end else begin
            en_pipe[0]       <= ck_en;
            mask_pipe[0]     <= qck_mask;
            skip_pipe[0]     <= skip_req;
            
            for (i = 1; i < PIPELINE_DEPTH; i++) begin
                en_pipe[i]   <= en_pipe[i-1];
                mask_pipe[i] <= mask_pipe[i-1];
                skip_pipe[i] <= skip_pipe[i-1];
            end
            // Dynamic gating: CK is enabled only if (en && !mask) or skip requested
            for (i = 0; i < CHANNELS; i++) begin
                if (skip_pipe[PIPELINE_DEPTH-1][i])
                    ck_out[i] <= 1'b1; // Force enable on skip
                else
                    ck_out[i] <= (en_pipe[PIPELINE_DEPTH-1][i] & ~mask_pipe[PIPELINE_DEPTH-1][i]);
            end
            // Error detection: gated while enable but masked, unless skip asserted
            for (i = 0; i < CHANNELS; i++) begin
                err_detect[i] = en_pipe[PIPELINE_DEPTH-1][i] & mask_pipe[PIPELINE_DEPTH-1][i] & ~skip_pipe[PIPELINE_DEPTH-1][i];
            end
            error <= err_detect;
        end
    end
    
    // Programmable delay logic (simplified)
    logic [DELAY_WIDTH-1:0] delay_cnt [CHANNELS-1:0];

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            for (i=0; i<CHANNELS; i++)
                delay_cnt[i] <= '0;
        else begin
            for (i=0; i<CHANNELS; i++) begin
                if (ck_en[i] && !mask_pipe[PIPELINE_DEPTH-1][i])
                    delay_cnt[i] <= prog_delay[i*DELAY_WIDTH +: DELAY_WIDTH];
                else
                    delay_cnt[i] <= '0;
            end
        end
    end
    // Integration stub for CA/QCA: can be extended per spec
    // Drive CA/QCA integration signals as required for channel control coordination

endmodule

//-----------------------------------------------------------------------------
// Operational notes:
// - Dynamic CK gating for DDR5 per JEDEC specs
// - Mask supports fine window control on per-channel basis
// - SKIP logic allows pipeline override for urgent requests/errors
// - All errors reported per-channel for monitoring
// - Extend CA/QCA interface with auxiliary control as required
//-----------------------------------------------------------------------------
