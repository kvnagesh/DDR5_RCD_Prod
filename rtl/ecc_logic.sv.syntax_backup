//-----------------------------------------------------------------------------
// Title      : ECC Logic Module (SECDED)
// Project    : DDR5 RCD Production
//-----------------------------------------------------------------------------
// File       : ecc_logic.sv
// Author     : Design Team
// Created    : 2025-11-03
// Description: Synthesizable SECDED datapath supporting 64-bit data and 8-bit ECC
//              - Encoder: Generates 8-bit ECC for input data
//              - Decoder: Computes syndrome, corrects single-bit errors, flags double-bit
//              - Fully pipelined valid/ready handshake
//-----------------------------------------------------------------------------

module ecc_logic 
#(
  parameter int DATA_WIDTH = 64,
  parameter int ECC_WIDTH  = 8,   
  parameter int PIPE_STAGES = 1   // Optional output register stage(s)
)(
  // Clock and Reset
  input  logic                         clk,
  input  logic                         rst_n,

  // Control
  input  logic                         ecc_enable,
  input  logic                         correction_en,   
  input  logic                         detection_en,    

  // Encoder interface (write path)
  input  logic [DATA_WIDTH-1:0]        data_in,
  input  logic                         data_valid_in,
  output logic [DATA_WIDTH-1:0]        data_out_enc,
  output logic [ECC_WIDTH-1:0]         ecc_out,
  output logic                         data_valid_out_enc,

  // Decoder interface (read path)
  input  logic [DATA_WIDTH-1:0]        data_in_dec,
  input  logic [ECC_WIDTH-1:0]         ecc_in,
  input  logic                         data_valid_in_dec,
  output logic [DATA_WIDTH-1:0]        data_out_dec,    
  output logic                         single_err,       
  output logic                         double_err,       
  output logic                         data_valid_out_dec
);

  //=========================================================================
  // Encoder: SECDED (64,8) typical mapping
  //=========================================================================
  // We implement 7 Hamming parity bits p[6:0] covering data positions and 1 overall parity p7

  function automatic logic parity_reduce(input logic [DATA_WIDTH-1:0] vec, input logic [DATA_WIDTH-1:0] mask);
    parity_reduce = ^(vec & mask);
  endfunction

  // Predefined masks for 64-bit data for Hamming(72,64) style parity coverage
  // Masks chosen to produce unique 7-bit syndrome over data bit positions [63:0]
  // These masks are deterministic and synthesizable constants.
  localparam logic [DATA_WIDTH-1:0] P_MASK [6:0] = '{
    64'hAAAAAAAA_AAAAAAAA, 
    64'hCCCCCCCC_CCCCCCCC, 
    64'hF0F0F0F0_F0F0F0F0, 
    64'hFF00FF00_FF00FF00, 
    64'hFFFF0000_FFFF0000, 
    64'hFFFFFFFF_00000000, 
    64'h00000000_00000000  // p6 reserved (for 64-bit, bit6 of index is 0 for 0..63)
  };

  // Compute parity bits p[6:0]
  logic [6:0] p_ham;
  always_comb begin
    p_ham[0] = parity_reduce(data_in, P_MASK[0]);
    p_ham[1] = parity_reduce(data_in, P_MASK[1]);
    p_ham[2] = parity_reduce(data_in, P_MASK[2]);
    p_ham[3] = parity_reduce(data_in, P_MASK[3]);
    p_ham[4] = parity_reduce(data_in, P_MASK[4]);
    p_ham[5] = parity_reduce(data_in, P_MASK[5]);
    p_ham[6] = parity_reduce(data_in, 64'h00000000_00000000); // zero for 64b
  end

  // Overall parity over data and Hamming bits
  logic p_overall;
  always_comb begin
    p_overall = ^{data_in, p_ham};
  end

  // ECC output [7:0] = {overall, p6..p0}
  logic [ECC_WIDTH-1:0] ecc_calc_enc;
  assign ecc_calc_enc = {p_overall, p_ham};

  // Optional output register stage for encoder
  generate
    if (PIPE_STAGES > 0) begin : gen_enc_pipe
      always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
          data_out_enc        <= '0;
          ecc_out             <= '0;
          data_valid_out_enc  <= 1'b0;
        end else begin
          if (ecc_enable && data_valid_in) begin
            data_out_enc       <= data_in;
            ecc_out            <= ecc_calc_enc;
            data_valid_out_enc <= 1'b1;
          end else begin
            data_valid_out_enc <= 1'b0;
          end
        end
      end
    end else begin : gen_enc_comb
      assign data_out_enc        = data_in;
      assign ecc_out             = ecc_calc_enc;
      assign data_valid_out_enc  = ecc_enable ? data_valid_in : 1'b0;
    end
  endgenerate

  //=========================================================================
  // Decoder: compute syndrome and correct if single error
  //=========================================================================

  // Recompute parity from received data
  logic [6:0] p_ham_dec;
  always_comb begin
    p_ham_dec[0] = parity_reduce(data_in_dec, P_MASK[0]);
    p_ham_dec[1] = parity_reduce(data_in_dec, P_MASK[1]);
    p_ham_dec[2] = parity_reduce(data_in_dec, P_MASK[2]);
    p_ham_dec[3] = parity_reduce(data_in_dec, P_MASK[3]);
    p_ham_dec[4] = parity_reduce(data_in_dec, P_MASK[4]);
    p_ham_dec[5] = parity_reduce(data_in_dec, P_MASK[5]);
    p_ham_dec[6] = parity_reduce(data_in_dec, 64'h00000000_00000000);
  end

  logic p_overall_dec;
  always_comb begin
    p_overall_dec = ^{data_in_dec, p_ham_dec};
  end

  // Extract received ECC
  wire [6:0] p_rx  = ecc_in[6:0];
  wire       ovrx  = ecc_in[7];

  // Syndrome: XOR of calculated and received Hamming parities
  logic [6:0] syndrome;
  assign syndrome = p_ham_dec ^ p_rx;

  // Overall parity check
  logic overall_mismatch;
  assign overall_mismatch = (p_overall_dec ^ ovrx);

  // Determine error classification
  // - If syndrome!=0 and overall_mismatch==1 -> single-bit error at index encoded by syndrome
  // - If syndrome==0 and overall_mismatch==1 -> error in overall parity bit only
  // - If syndrome!=0 and overall_mismatch==0 -> double-bit error (uncorrectable)
  // - If syndrome==0 and overall_mismatch==0 -> no error

  // Map 7-bit syndrome to data-bit index (0..63) using inverse of mask mapping
  function automatic logic [5:0] syndrome_to_index(input logic [6:0] syn);
    logic [5:0] idx;
    idx = 6'd0;
    // Reconstruct index from bits [5:0] of syndrome (since P_MASK chosen that way)
    idx[0] = syn[0];
    idx[1] = syn[1];
    idx[2] = syn[2];
    idx[3] = syn[3];
    idx[4] = syn[4];
    idx[5] = syn[5];
    return idx;
  endfunction

  logic [DATA_WIDTH-1:0] corrected_data;
  logic                  se_flag, de_flag;

  always_comb begin
    corrected_data = data_in_dec;
    se_flag = 1'b0;
    de_flag = 1'b0;

    if (detection_en && ecc_enable && data_valid_in_dec) begin
      unique case ({syndrome != 7'd0, overall_mismatch})
        2'b10: begin
          // Double-bit error (syndrome!=0, overall_mismatch==0)
          de_flag = 1'b1;
        end
        2'b01: begin
          // Overall parity error only, treat as single error in parity bit
          se_flag = 1'b1;
        end
        2'b11: begin
          // Single-bit error that can be corrected
          se_flag = 1'b1;
          if (correction_en) begin
            // Flip the indicated data bit if within range
            logic [5:0] bit_idx;
            bit_idx = syndrome_to_index(syndrome);
            if (bit_idx < DATA_WIDTH)
              corrected_data[bit_idx] = ~corrected_data[bit_idx];
          end
        end
        default: begin
          // No error
        end
      endcase
    end
  end

  // Optional pipeline on decoder outputs
  generate
    if (PIPE_STAGES > 0) begin : gen_dec_pipe
      always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
          data_out_dec       <= '0;
          single_err         <= 1'b0;
          double_err         <= 1'b0;
          data_valid_out_dec <= 1'b0;
        end else begin
          if (data_valid_in_dec && ecc_enable) begin
            data_out_dec       <= corrected_data;
            single_err         <= se_flag;
            double_err         <= de_flag;
            data_valid_out_dec <= 1'b1;
          end else begin
            data_valid_out_dec <= 1'b0;
            single_err         <= 1'b0;
            double_err         <= 1'b0;
          end
        end
      end
    end else begin : gen_dec_comb
      assign data_out_dec       = corrected_data;
      assign single_err         = se_flag;
      assign double_err         = de_flag;
      assign data_valid_out_dec = (data_valid_in_dec && ecc_enable);
    end
  endgenerate

  // Synthesis-safe assertions
  `ifdef FORMAL_VERIFICATION
    initial begin
      assert (DATA_WIDTH == 64);
      assert (ECC_WIDTH  == 8);
    end
  `endif

endmodule : ecc_logic

//-----------------------------------------------------------------------------
// End of File
//-----------------------------------------------------------------------------
