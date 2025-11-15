// =====================================================================
// CRC-5 Calculation Circuit for RCD Bus Protocol
// =====================================================================
// Description: Implements CRC-5 polynomial calculation for RCD data
//              integrity checking. Supports both serial and parallel
//              implementations with configurable polynomial.
//
// CRC Polynomial: G(x) = x^5 + x^2 + 1 (0x05 for RCD protocol)
// Author: RCD Protocol Implementation
// Date: 2025-11-04
// =====================================================================

module crc5_calc #(
  parameter int DWIDTH = 32,           
  parameter logic [4:0] CRC_POLY = 5'b00101, 
  parameter string MODE = "PARALLEL"   // "SERIAL" or "PARALLEL"
) (
  input  logic                clk,
  input  logic                rst_n,
  input  logic                en,
  
  // Data Input
  input  logic [DWIDTH-1:0]   data_in,
  input  logic                valid_in,
  
  // CRC Output
  output logic [4:0]          crc_out,
  output logic                crc_valid,
  
  // Verification/Debug
  input  logic [4:0]          crc_expected, 
  output logic                crc_match,    
  output logic [15:0]         crc_error_cnt // Cumulative CRC errors
);

  // ===================================================================
  // CRC Register (5 bits for CRC-5)
  // ===================================================================
  logic [4:0] crc_reg, crc_next;
  logic [15:0] error_counter;
  
  // ===================================================================
  // Parallel CRC-5 Calculation for 8-bit input
  // ===================================================================
  function automatic logic [4:0] calc_crc5_8bit(
    input logic [7:0] data,
    input logic [4:0] crc_in
  );
    logic [4:0] crc_out;
    logic [12:0] combined; // Combined CRC register + data
    
    // Use Galois LFSR for CRC-5 polynomial x^5 + x^2 + 1
    combined = {crc_in[3:0], data};
    
    // Bit-by-bit calculation (parallel form)
    crc_out[0] = combined[12] ^ combined[11] ^ combined[10] ^ combined[8] ^ 
                 combined[7] ^ combined[6] ^ combined[5] ^ combined[3] ^ 
                 combined[2] ^ combined[0];
    
    crc_out[1] = combined[12] ^ combined[9] ^ combined[8] ^ combined[6] ^ combined[4] ^ combined[3] ^ combined[1];
    
    crc_out[2] = combined[12] ^ combined[11] ^ combined[10] ^ combined[9] ^ 
                 combined[8] ^ combined[7] ^ combined[5] ^ combined[3] ^ combined[2];
    
    crc_out[3] = combined[12] ^ combined[10] ^ combined[9] ^ combined[8] ^ combined[4] ^ combined[2] ^ combined[1];
    
    crc_out[4] = combined[12] ^ combined[11] ^ combined[10] ^ combined[9] ^ combined[5] ^ combined[3] ^ combined[2];
    
    return crc_out;
  endfunction
  
  // ===================================================================
  // Parallel CRC-5 Calculation for 32-bit input
  // ===================================================================
  function automatic logic [4:0] calc_crc5_32bit(
    input logic [31:0] data,
    input logic [4:0] crc_in
  );
    logic [4:0] crc_temp;
    integer i;
    
    crc_temp = crc_in;
    for (i = 0; i < 4; i = i + 1) begin
      crc_temp = calc_crc5_8bit(data[8*i+7:8*i], crc_temp);
    end
    
    return crc_temp;
  endfunction
  
  // ===================================================================
  // CRC Calculation Logic
  // ===================================================================
  logic [4:0] crc_calc;
  
  always_comb begin
    // Calculate CRC based on data width and mode
    if (DWIDTH == 8) begin
      crc_calc = calc_crc5_8bit(data_in[7:0], '0);
    end else if (DWIDTH == 16) begin
      crc_calc = calc_crc5_8bit(data_in[15:8], calc_crc5_8bit(data_in[7:0], '0));
    end else if (DWIDTH == 32) begin
      crc_calc = calc_crc5_32bit(data_in[31:0], '0);
    end else begin
      crc_calc = '0;
    end
  end
  
  // ===================================================================
  // CRC Verification
  // ===================================================================
  always_comb begin
    crc_match = (crc_calc == crc_expected);
  end
  
  // ===================================================================
  // Sequential Logic for CRC Output
  // ===================================================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      crc_reg <= 5'h1F;  // CRC initial value (all ones for RCD)
      error_counter <= 16'h0000;
      crc_valid <= 1'b0;
    end else if (en && valid_in) begin
      crc_reg <= crc_calc;
      crc_valid <= 1'b1;
      
      // Track CRC errors
      if (!crc_match) begin
        error_counter <= error_counter + 1;
      end
    end else begin
      crc_valid <= 1'b0;
    end
  end
  
  // ===================================================================
  // Output Assignment
  // ===================================================================
  assign crc_out = crc_reg;
  assign crc_error_cnt = error_counter;

endmodule

// =====================================================================
// CRC-5 Serial Calculator (for streaming data)
// =====================================================================
module crc5_serial #(
  parameter logic [4:0] CRC_POLY = 5'b00101
) (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        en,
  input  logic        data_bit,     
  input  logic        load_init,    
  input  logic [4:0]  crc_init,     
  
  output logic [4:0]  crc_out       // Current CRC value
);

  logic [4:0] crc_reg, crc_next;
  
  always_comb begin
    crc_next = crc_reg;
    
    // Galois LFSR implementation for CRC-5
    if (data_bit ^ crc_reg[4]) begin
      crc_next = {crc_reg[3:0], 1'b0} ^ CRC_POLY;
    end else begin
      crc_next = {crc_reg[3:0], 1'b0};
    end
  end
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      crc_reg <= 5'h1F;
    end else if (load_init) begin
      crc_reg <= crc_init;
    end else if (en) begin
      crc_reg <= crc_next;
    end
  end
  
  assign crc_out = crc_reg;

endmodule

// =====================================================================
// END OF MODULE
// =====================================================================
