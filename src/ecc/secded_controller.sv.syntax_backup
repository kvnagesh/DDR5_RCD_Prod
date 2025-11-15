//============================================================================
// Module: secded_controller
// Description: SECDED Pipeline Controller
//              Manages ECC encode/decode stages, error handling, and pipeline control
//              For DDR5 ECC flow (Hamming/SECDED)
//
// Parameters:
//   - DATA_WIDTH: Data width (default: 64)
//   - ECC_WIDTH: ECC bits width (default: 8)
//
// Features:
//   - Configurable ECC modes
//   - Pipelining with bubble-insertion for error recovery
//   - Handshaking between ECC encode/decode/report units
//   - Error status aggregation and forwarding
//   - Timing assertions and coverage
//============================================================================

module secded_controller #(
    parameter int DATA_WIDTH = 64,
    parameter int ECC_WIDTH  = 8,
    parameter int TOTAL_WIDTH = DATA_WIDTH + ECC_WIDTH
) (
    // Clock and Reset
    input  logic clk,
    input  logic rst_n,

    // Data In
    input  logic [DATA_WIDTH-1:0] data_in,
    input  logic                  data_valid,
    input  logic [1:0]            ecc_mode,
    input  logic                  enable,

    // Output - Pipeline interface
    output logic [TOTAL_WIDTH-1:0] encoded_data,
    output logic                   encoded_valid,
    output logic [DATA_WIDTH-1:0]  corrected_data,
    output logic                   corrected_valid,

    // Error signals
    output logic                   error_single,
    output logic                   error_double,
    output logic                   error_corrected,
    output logic                   error_pipeline_blocked,
    
    // Diagnostic/status
    output logic                   encoder_busy,
    output logic                   decoder_busy,
    output logic                   pipeline_busy
);

    //========================================================================
    // Pipeline submodules (ECC Encoder and Decoder)
    //========================================================================
    logic [ECC_WIDTH-1:0] ecc_bits_wire;
    logic encoder_error;
    logic decoder_error;
    logic [TOTAL_WIDTH-1:0] encoded_wire;
    logic [DATA_WIDTH-1:0] decoded_wire;
    logic [ECC_WIDTH-1:0] syndrome_wire;
    logic single_err_wire, double_err_wire, correct_wire, decoder_valid_wire;

    ecc_encoder #(
        .DATA_WIDTH(DATA_WIDTH),
        .ECC_WIDTH(ECC_WIDTH),
        .TOTAL_WIDTH(TOTAL_WIDTH)
    ) u_encoder (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(data_in),
        .data_valid(data_valid),
        .ecc_mode(ecc_mode),
        .enable(enable),
        .encoded_data(encoded_wire),
        .ecc_bits(ecc_bits_wire),
        .encoded_valid(encoded_valid),
        .encoder_busy(encoder_busy),
        .encoder_error(encoder_error)
    );

    ecc_decoder #(
        .DATA_WIDTH(DATA_WIDTH),
        .ECC_WIDTH(ECC_WIDTH),
        .TOTAL_WIDTH(TOTAL_WIDTH)
    ) u_decoder (
        .clk(clk),
        .rst_n(rst_n),
        .encoded_data(encoded_wire),
        .data_in(data_in),
        .ecc_in(ecc_bits_wire),
        .data_valid(encoded_valid),
        .ecc_mode(ecc_mode),
        .enable(enable),
        .corrected_data(decoded_wire),
        .syndrome(syndrome_wire),
        .decoded_valid(decoder_valid_wire),
        .error_single(single_err_wire),
        .error_double(double_err_wire),
        .error_position(),
        .error_corrected(correct_wire),
        .decoder_busy(decoder_busy),
        .decoder_error(decoder_error)
    );

    //========================================================================
    // Error & Output Pipeline Handshake Logic
    //========================================================================
    logic pipeline_blocked;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            encoded_data      <= '0;
            corrected_data    <= '0;
            corrected_valid   <= 1'b0;
            error_single      <= 1'b0;
            error_double      <= 1'b0;
            error_corrected   <= 1'b0;
            pipeline_blocked  <= 1'b0;
        end else begin
            encoded_data      <= encoded_wire;
            corrected_data    <= decoded_wire;
            corrected_valid   <= decoder_valid_wire;
            error_single      <= single_err_wire;
            error_double      <= double_err_wire;
            error_corrected   <= correct_wire;
            pipeline_blocked  <= encoder_error | decoder_error | double_err_wire;
        end
    end

    assign error_pipeline_blocked = pipeline_blocked;
    assign pipeline_busy = encoder_busy | decoder_busy;

    //========================================================================
    // Timing Coverage and Protocol Assertions
    //========================================================================
    `ifdef SIMULATION
        initial begin
            assert (DATA_WIDTH == 64 || DATA_WIDTH == 32 || DATA_WIDTH == 128)
                else $error("Unsupported DATA_WIDTH for secded_controller");
        end

        // Data valid handoff to encoder, then to decoder
        property p_valid_pipeline_handoff;
            @(posedge clk) disable iff (!rst_n)
            (data_valid && enable) |-> ##1 encoded_valid |-> ##2 decoder_valid_wire;
        endproperty
        assert property (p_valid_pipeline_handoff)
            else $error("ECC data handoff violated");
        // Blockage and recovery coverage
        covergroup cg_pipeline_blocking @(posedge clk);
            option.per_instance = 1;
            cp_blocked: coverpoint pipeline_blocked {
                bins not_blocked = {0};
                bins blocked = {1};
            }
        endgroup
        cg_pipeline_blocking cg_block = new();
    `endif

endmodule

//============================================================================
// End of secded_controller module
//============================================================================
