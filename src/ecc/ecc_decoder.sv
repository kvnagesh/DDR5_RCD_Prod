//============================================================================
// Module: ecc_decoder
// Description: Error Correction Code (ECC) Decoder
//              Decodes SECDED protected data and performs error detection
//              and correction using syndrome decoding
//
// Parameters:
//   - DATA_WIDTH: Width of data (default 64 for DDR5)
//   - ECC_WIDTH: Width of ECC check bits (8 for 72-bit total)
//
// Features:
//   - Single Error Correction (SEC)
//   - Double Error Detection (DED)
//   - Syndrome-based error localization
//   - Pipelined architecture for high-throughput
//   - Comprehensive error status reporting
//============================================================================

module ecc_decoder #(
    parameter int DATA_WIDTH = 64,  // Data width
    parameter int ECC_WIDTH  = 8,   // ECC check bits width
    parameter int TOTAL_WIDTH = DATA_WIDTH + ECC_WIDTH  // Total encoded width
) (
    // Clock and Reset
    input  logic        clk,
    input  logic        rst_n,
    
    // Encoded Data Input
    input  logic [TOTAL_WIDTH-1:0] encoded_data,  // Data + ECC bits
    input  logic [DATA_WIDTH-1:0]  data_in,       // Raw data for bypass/reference
    input  logic [ECC_WIDTH-1:0]   ecc_in,        // Received ECC bits
    input  logic        data_valid,
    
    // Configuration
    input  logic [1:0]  ecc_mode,       // 0: None, 1: SEC, 2: SECDED, 3: Reserved
    input  logic        enable,
    
    // Corrected Output
    output logic [DATA_WIDTH-1:0] corrected_data,  // Corrected data
    output logic [ECC_WIDTH-1:0]  syndrome,        // Error syndrome bits
    output logic        decoded_valid,
    
    // Error Status
    output logic        error_single,        // Single bit error detected
    output logic        error_double,        // Double bit error detected
    output logic [ECC_WIDTH-1:0] error_position,  // Position of single error
    output logic        error_corrected,     // Error was corrected
    output logic        decoder_busy,
    output logic        decoder_error        // Decoder configuration error
);

    //========================================================================
    // ECC Mode Definitions
    //========================================================================
    typedef enum logic [1:0] {
        ECC_NONE    = 2'b00,
        ECC_SEC     = 2'b01,
        ECC_SECDED  = 2'b10,
        ECC_RSVD    = 2'b11
    } ecc_mode_e;

    //========================================================================
    // Internal Signals - Pipeline Stage 1 (Syndrome Calculation)
    //========================================================================
    logic [ECC_WIDTH-1:0]  syndrome_s1;
    logic [ECC_WIDTH-1:0]  calculated_ecc;
    logic [DATA_WIDTH-1:0] data_s1;
    logic [ECC_WIDTH-1:0]  ecc_s1;
    logic                   valid_s1;
    logic [1:0]            mode_s1;
    
    // Check matrix for syndrome calculation
    logic [TOTAL_WIDTH-1:0] check_matrix [ECC_WIDTH-1:0];

    // Initialize SECDED check matrix
    always_comb begin
        check_matrix[0] = 72'h15555_55555_55555_5555;
        check_matrix[1] = 72'h26666_66666_66666_6666;
        check_matrix[2] = 72'h38787_87878_78787_8787;
        check_matrix[3] = 72'h4F0F0_F0F0F_0F0F0_F0F0;
        check_matrix[4] = 72'h5FF00_FF00F_F00FF_00FF;
        check_matrix[5] = 72'h6FFF0_000FF_FF000_0FFF;
        check_matrix[6] = 72'h7FFFF_FF000_00000_FFFF;
        check_matrix[7] = 72'hFFFFF_FFFFF_FFFFF_FFFF;
    end

    //========================================================================
    // Stage 1: Syndrome Calculation
    //========================================================================
    
    // Calculate syndrome from received data and ECC bits
    always_comb begin
        syndrome_s1 = '0;
        calculated_ecc = '0;
        
        if (enable && data_valid) begin
            // Calculate syndrome (XOR of encoded data with check matrix)
            for (int i = 0; i < ECC_WIDTH; i++) begin
                syndrome_s1[i] = ^(encoded_data & check_matrix[i]);
            end
        end
    end

    //========================================================================
    // Stage 2: Error Detection and Correction (Registered)
    //========================================================================
    
    logic [ECC_WIDTH-1:0]  syndrome_s2;
    logic [DATA_WIDTH-1:0] data_s2;
    logic [ECC_WIDTH-1:0]  ecc_s2;
    logic                   valid_s2;
    logic [1:0]            mode_s2;
    logic                   error_single_raw;
    logic                   error_double_raw;
    logic [ECC_WIDTH-1:0]   error_pos_raw;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            syndrome_s2 <= '0;
            data_s2 <= '0;
            ecc_s2 <= '0;
            valid_s2 <= 1'b0;
            mode_s2 <= ECC_NONE;
        end else begin
            syndrome_s2 <= syndrome_s1;
            data_s2 <= data_in;
            ecc_s2 <= ecc_in;
            valid_s2 <= (enable && data_valid);
            mode_s2 <= ecc_mode;
        end
    end
    
    // Error detection logic
    // For SECDED: 
    //   - If syndrome == 0 and parity == 0: No error
    //   - If syndrome != 0 and parity == 1: Single bit error (correctable)
    //   - If syndrome == 0 and parity == 1: Double bit error (uncorrectable)
    //   - If syndrome != 0 and parity == 0: Double bit error (uncorrectable)
    always_comb begin
        error_single_raw = 1'b0;
        error_double_raw = 1'b0;
        error_pos_raw = syndrome_s2;
        
        if (valid_s2 && mode_s2 == ECC_SECDED) begin
            // Check parity bit (MSB of syndrome)
            logic overall_parity = syndrome_s2[ECC_WIDTH-1];
            logic syndrome_nonzero = (syndrome_s2[ECC_WIDTH-2:0] != '0);
            
            if (syndrome_nonzero) begin
                if (overall_parity == 1'b1) begin
                    // Single bit error: correct it
                    error_single_raw = 1'b1;
                    error_pos_raw = syndrome_s2;
                end else begin
                    // Double bit error: flag but don't correct
                    error_double_raw = 1'b1;
                end
            end
        end else if (valid_s2 && mode_s2 == ECC_SEC) begin
            // SEC only mode: flag any non-zero syndrome
            if (syndrome_s2 != '0) begin
                error_single_raw = 1'b1;
                error_pos_raw = syndrome_s2;
            end
        end
    end

    //========================================================================
    // Stage 3: Data Correction (Pipeline Output)
    //========================================================================
    
    logic [DATA_WIDTH-1:0] corrected_data_s3;
    logic                   error_single_s3;
    logic                   error_double_s3;
    logic [ECC_WIDTH-1:0]   error_pos_s3;
    logic                   error_corrected_s3;
    logic                   valid_s3;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            corrected_data_s3 <= '0;
            error_single_s3 <= 1'b0;
            error_double_s3 <= 1'b0;
            error_pos_s3 <= '0;
            error_corrected_s3 <= 1'b0;
            valid_s3 <= 1'b0;
        end else begin
            valid_s3 <= valid_s2;
            
            // Flip error bit in data if single error detected
            if (error_single_raw && !error_double_raw) begin
                corrected_data_s3 <= data_s2 ^ (1 << error_pos_raw[5:0]);
                error_corrected_s3 <= 1'b1;
            end else begin
                corrected_data_s3 <= data_s2;
                error_corrected_s3 <= 1'b0;
            end
            
            error_single_s3 <= error_single_raw;
            error_double_s3 <= error_double_raw;
            error_pos_s3 <= error_pos_raw;
        end
    end

    //========================================================================
    // Output Assignment
    //========================================================================
    
    assign corrected_data = corrected_data_s3;
    assign syndrome = syndrome_s2;
    assign decoded_valid = valid_s3;
    assign error_single = error_single_s3;
    assign error_double = error_double_s3;
    assign error_position = error_pos_s3;
    assign error_corrected = error_corrected_s3;
    assign decoder_busy = valid_s1 | valid_s2;
    
    // Error flag for invalid configuration
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            decoder_error <= 1'b0;
        end else begin
            if (enable && data_valid) begin
                decoder_error <= (ecc_mode == ECC_RSVD);
            end else begin
                decoder_error <= 1'b0;
            end
        end
    end

    //========================================================================
    // Assertions for Verification
    //========================================================================
    
    `ifdef SIMULATION
        // Configuration check
        initial begin
            assert (DATA_WIDTH == 64 || DATA_WIDTH == 32 || DATA_WIDTH == 128)
                else $error("Unsupported DATA_WIDTH: %0d", DATA_WIDTH);
            assert (ECC_WIDTH >= 7)
                else $error("ECC_WIDTH must be at least 7 for SECDED");
        end
        
        // Protocol checks
        property p_output_valid_after_input;
            @(posedge clk) disable iff (!rst_n)
            (enable && data_valid) |-> ##3 decoded_valid;
        endproperty
        assert property (p_output_valid_after_input)
            else $error("Output valid not asserted after 3-cycle pipeline");
        
        // Error mutual exclusivity
        property p_error_exclusivity;
            @(posedge clk) disable iff (!rst_n)
            decoded_valid |-> !(error_single_s3 && error_double_s3);
        endproperty
        assert property (p_error_exclusivity)
            else $error("Cannot have both single and double error");
        
        // Correction validity check
        property p_correction_validity;
            @(posedge clk) disable iff (!rst_n)
            (decoded_valid && error_corrected_s3) |-> error_single_s3;
        endproperty
        assert property (p_correction_validity)
            else $error("Data corrected without single error detection");
        
        // Coverage: Error scenarios
        covergroup cg_error_scenarios @(posedge clk);
            option.per_instance = 1;
            cp_single_error: coverpoint error_single_s3 {
                bins no_error = {0};
                bins single_error = {1};
            }
            cp_double_error: coverpoint error_double_s3 {
                bins no_error = {0};
                bins double_error = {1};
            }
            cp_corrected: coverpoint error_corrected_s3 {
                bins not_corrected = {0};
                bins corrected = {1};
            }
            // Cross coverage
            cross cp_single_error, cp_double_error, cp_corrected;
        endgroup
        
        cg_error_scenarios cg_errors = new();
        
        // Coverage: Syndrome values
        covergroup cg_syndrome @(posedge clk);
            option.per_instance = 1;
            cp_syndrome_zero: coverpoint syndrome_s2 {
                bins zero = {8'h00};
                bins nonzero[] = {[8'h01:8'hFF]};
            }
        endgroup
        
        cg_syndrome cg_syn = new();
    `endif

endmodule

//============================================================================
// End of ecc_decoder module
//============================================================================
