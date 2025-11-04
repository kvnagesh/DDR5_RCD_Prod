//============================================================================
// Module: ecc_encoder
// Description: Error Correction Code (ECC) Encoder
//              Generates ECC check bits for data protection using
//              SECDED (Single Error Correction, Double Error Detection)
//              Implements extended Hamming code for 64-bit data
//
// Parameters:
//   - DATA_WIDTH: Width of input data (default 64 for DDR5)
//   - ECC_WIDTH: Width of ECC check bits (8 for 72-bit total)
//
// Features:
//   - Configurable ECC modes: None, SEC, SECDED
//   - Parameterized for different DRAM widths
//   - Single-cycle encoding latency
//   - Comprehensive error checking and status reporting
//============================================================================

module ecc_encoder #(
    parameter int DATA_WIDTH = 64,  // Input data width
    parameter int ECC_WIDTH  = 8,   // ECC check bits width
    parameter int TOTAL_WIDTH = DATA_WIDTH + ECC_WIDTH  // Total encoded width
) (
    // Clock and Reset
    input  logic        clk,
    input  logic        rst_n,
    
    // Data Input
    input  logic [DATA_WIDTH-1:0] data_in,       // Input data to be encoded
    input  logic        data_valid,
    
    // ECC Configuration
    input  logic [1:0]  ecc_mode,      // 0: None, 1: SEC, 2: SECDED, 3: Reserved
    input  logic        enable,
    
    // Encoded Output
    output logic [TOTAL_WIDTH-1:0] encoded_data,  // Data + ECC bits
    output logic [ECC_WIDTH-1:0]  ecc_bits,      // ECC check bits only
    output logic        encoded_valid,
    
    // Status
    output logic        encoder_busy,
    output logic        encoder_error
);

    //========================================================================
    // ECC Mode Definitions
    //========================================================================
    typedef enum logic [1:0] {
        ECC_NONE    = 2'b00,  // No ECC
        ECC_SEC     = 2'b01,  // Single Error Correction
        ECC_SECDED  = 2'b10,  // Single Error Correction, Double Error Detection
        ECC_RSVD    = 2'b11   // Reserved for future use
    } ecc_mode_e;

    //========================================================================
    // Internal Signals
    //========================================================================
    logic [ECC_WIDTH-1:0]  calculated_ecc;
    logic [DATA_WIDTH-1:0] data_reg;
    logic                   valid_reg;
    logic                   busy;
    
    // Parity check matrix positions for SECDED (Hsiao Code)
    // For 64-bit data with 8 check bits (72 bits total)
    logic [TOTAL_WIDTH-1:0] check_matrix [ECC_WIDTH-1:0];
    
    //========================================================================
    // ECC Check Bit Generation Matrix (SECDED - Hsiao Code)
    // Using odd-weight columns for better error detection
    //========================================================================
    
    // Initialize check matrix for SECDED encoding
    // Each check bit is XOR of specific data bit positions
    always_comb begin
        // Check bit C0 (Position 0)
        check_matrix[0] = 72'h15555_55555_55555_5555;
        
        // Check bit C1 (Position 1)
        check_matrix[1] = 72'h26666_66666_66666_6666;
        
        // Check bit C2 (Position 2)
        check_matrix[2] = 72'h38787_87878_78787_8787;
        
        // Check bit C3 (Position 3)
        check_matrix[3] = 72'h4F0F0_F0F0F_0F0F0_F0F0;
        
        // Check bit C4 (Position 4)
        check_matrix[4] = 72'h5FF00_FF00F_F00FF_00FF;
        
        // Check bit C5 (Position 5)
        check_matrix[5] = 72'h6FFF0_000FF_FF000_0FFF;
        
        // Check bit C6 (Position 6)
        check_matrix[6] = 72'h7FFFF_FF000_00000_FFFF;
        
        // Check bit C7 (Position 7) - Overall parity for SECDED
        check_matrix[7] = 72'hFFFFF_FFFFF_FFFFF_FFFF;
    end

    //========================================================================
    // ECC Calculation Logic
    //========================================================================
    
    // Calculate ECC check bits using generator matrix
    always_comb begin
        calculated_ecc = '0;
        
        if (enable && data_valid) begin
            case (ecc_mode)
                ECC_NONE: begin
                    // No ECC generation
                    calculated_ecc = '0;
                end
                
                ECC_SEC, ECC_SECDED: begin
                    // Generate each check bit using XOR of data bits
                    for (int i = 0; i < ECC_WIDTH; i++) begin
                        calculated_ecc[i] = ^(data_in & check_matrix[i][DATA_WIDTH-1:0]);
                    end
                    
                    // For SEC mode, clear the overall parity bit
                    if (ecc_mode == ECC_SEC) begin
                        calculated_ecc[ECC_WIDTH-1] = 1'b0;
                    end
                end
                
                default: begin
                    calculated_ecc = '0;
                end
            endcase
        end else begin
            calculated_ecc = '0;
        end
    end

    //========================================================================
    // Pipeline Stage - Register outputs for timing closure
    //========================================================================
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_reg      <= '0;
            ecc_bits      <= '0;
            encoded_data  <= '0;
            valid_reg     <= 1'b0;
            encoded_valid <= 1'b0;
        end else begin
            if (enable && data_valid) begin
                data_reg      <= data_in;
                ecc_bits      <= calculated_ecc;
                encoded_data  <= {calculated_ecc, data_in};  // ECC bits in MSB
                valid_reg     <= 1'b1;
            end else begin
                valid_reg     <= 1'b0;
            end
            
            encoded_valid <= valid_reg;
        end
    end

    //========================================================================
    // Status Signal Generation
    //========================================================================
    
    // Encoder is busy during active encoding
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            busy <= 1'b0;
        end else begin
            busy <= enable && data_valid;
        end
    end
    
    assign encoder_busy = busy;

    // Error detection: invalid mode or configuration
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            encoder_error <= 1'b0;
        end else begin
            // Check for invalid configurations
            if (enable && data_valid) begin
                encoder_error <= (ecc_mode == ECC_RSVD);  // Reserved mode is error
            end else begin
                encoder_error <= 1'b0;
            end
        end
    end

    //========================================================================
    // Assertions for Verification
    //========================================================================
    
    `ifdef SIMULATION
        // Check that data width is valid
        initial begin
            assert (DATA_WIDTH == 64 || DATA_WIDTH == 32 || DATA_WIDTH == 128)
                else $error("Unsupported DATA_WIDTH: %0d", DATA_WIDTH);
            assert (ECC_WIDTH >= 7)
                else $error("ECC_WIDTH must be at least 7 for proper SECDED");
        end
        
        // Protocol checks
        property p_valid_after_enable;
            @(posedge clk) disable iff (!rst_n)
            (enable && data_valid) |-> ##1 valid_reg;
        endproperty
        assert property (p_valid_after_enable)
            else $error("Valid signal not asserted after enable");
        
        // ECC stability check
        property p_ecc_stable_when_valid;
            @(posedge clk) disable iff (!rst_n)
            (valid_reg && $stable(data_reg)) |-> $stable(ecc_bits);
        endproperty
        assert property (p_ecc_stable_when_valid)
            else $error("ECC bits changed with stable data");
        
        // Mode check
        property p_invalid_mode_error;
            @(posedge clk) disable iff (!rst_n)
            (enable && data_valid && ecc_mode == ECC_RSVD) |-> ##1 encoder_error;
        endproperty
        assert property (p_invalid_mode_error)
            else $error("Error not flagged for invalid ECC mode");
            
        // Coverage: ECC modes
        covergroup cg_ecc_modes @(posedge clk);
            option.per_instance = 1;
            cp_mode: coverpoint ecc_mode {
                bins none   = {ECC_NONE};
                bins sec    = {ECC_SEC};
                bins secded = {ECC_SECDED};
                bins rsvd   = {ECC_RSVD};
            }
            cp_enable: coverpoint enable {
                bins enabled  = {1};
                bins disabled = {0};
            }
            cp_valid: coverpoint data_valid {
                bins valid   = {1};
                bins invalid = {0};
            }
            // Cross coverage
            cross cp_mode, cp_enable, cp_valid;
        endgroup
        
        cg_ecc_modes cg_modes = new();
        
        // Coverage: Data patterns
        covergroup cg_data_patterns @(posedge clk);
            option.per_instance = 1;
            cp_data_all_zeros: coverpoint data_in {
                bins all_zeros = {64'h0};
            }
            cp_data_all_ones: coverpoint data_in {
                bins all_ones = {64'hFFFF_FFFF_FFFF_FFFF};
            }
            cp_data_walking: coverpoint data_in {
                bins walking_ones[] = {64'h1, 64'h2, 64'h4, 64'h8, 
                                       64'h10, 64'h20, 64'h40, 64'h80};
            }
        endgroup
        
        cg_data_patterns cg_patterns = new();
    `endif

endmodule

//============================================================================
// End of ecc_encoder module
//============================================================================
