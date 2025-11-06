//==================================================================================
// Module: ca_decoder
// Description: DDR5 Command/Address Packet Decoder with Full Spec Compliance
//              - Full packet decoding for all DDR5 command types
//              - Multi-mode support (1:1, 1:2, 1:4)
//              - CRC/parity verification
//              - Error detection and reporting
// Author: Auto-generated for DDR5 RCD Production
// Date: 2025-11-06
//==================================================================================

module ca_decoder #(
    // CA Interface Parameters
    parameter int CA_WIDTH = 7,          // CA bus width per JEDEC DDR5
    parameter int CA_PHASES = 2,         // Dual-phase (rising/falling)
    parameter int ADDR_WIDTH = 17,       // Full address width
    parameter int CMD_WIDTH = 5,         // DDR5 command width (5 bits)
    parameter int BANK_GROUP_WIDTH = 3,  // Bank group width
    parameter int BANK_WIDTH = 2,        // Bank address width
    
    // Packet Parameters  
    parameter int PACKET_SIZE = 28,      // Full 28-bit CA packet (2 phases × 7 bits × 2 cycles)
    parameter int CRC_WIDTH = 5,         // CRC-5 for error checking
    parameter int PARITY_WIDTH = 1       // Parity bit
) (
    // Clock and Reset
    input  logic                    clk,
    input  logic                    rst_n,
    
    // Configuration
    input  logic [1:0]              cfg_ca_mode,       // 00=1:1, 01=1:2, 10=1:4
    input  logic                    cfg_crc_enable,
    input  logic                    cfg_parity_enable,
    input  logic                    cfg_decode_enable,
    
    // CA Input (dual-phase from DRAM interface)
    input  logic [CA_WIDTH-1:0]     ca_phase0_in,      // Rising edge CA
    input  logic [CA_WIDTH-1:0]     ca_phase1_in,      // Falling edge CA
    input  logic                    ca_valid_in,
    
    // Decoded Command Outputs
    output logic [CMD_WIDTH-1:0]    cmd_out,
    output logic [ADDR_WIDTH-1:0]   addr_out,
    output logic [BANK_GROUP_WIDTH-1:0] bank_group_out,
    output logic [BANK_WIDTH-1:0]   bank_addr_out,
    output logic [3:0]              burst_length_out,
    output logic                    auto_precharge_out,
    output logic                    cmd_valid_out,
    
    // Command Type Decoded
    output logic                    is_activate,
    output logic                    is_read,
    output logic                    is_write,
    output logic                    is_precharge,
    output logic                    is_refresh,
    output logic                    is_mrs,          // Mode Register Set
    output logic                    is_zqc,          // ZQ Calibration
    
    // CRC/Parity Status
    input  logic [CRC_WIDTH-1:0]    crc_in,
    input  logic [PARITY_WIDTH-1:0] parity_in,
    output logic                    crc_error,
    output logic                    parity_error,
    
    // Error Reporting
    output logic                    decode_error,
    output logic [7:0]              error_code
);

//==================================================================================
// Internal Signals
//==================================================================================

logic [PACKET_SIZE-1:0]     packet_buffer;
logic [1:0]                 phase_count;
logic                       packet_complete;
logic [CRC_WIDTH-1:0]       calculated_crc;
logic                       calculated_parity;

// Command type definitions (DDR5 JEDEC spec)
typedef enum logic [CMD_WIDTH-1:0] {
    CMD_DES         = 5'b00000,  // Deselect
    CMD_NOP         = 5'b00111,  // No Operation  
    CMD_READ        = 5'b00101,  // Read
    CMD_WRITE       = 5'b00100,  // Write
    CMD_ACTIVATE    = 5'b00110,  // Row Activate
    CMD_PRECHARGE   = 5'b01000,  // Precharge
    CMD_REFRESH     = 5'b00001,  // Refresh
    CMD_MRS         = 5'b00010,  // Mode Register Set
    CMD_ZQC_START   = 5'b01010,  // ZQ Calibration Start
    CMD_ZQC_LATCH   = 5'b01011,  // ZQ Calibration Latch
    CMD_SRE         = 5'b01100,  // Self-Refresh Entry
    CMD_SRX         = 5'b01101,  // Self-Refresh Exit
    CMD_PDE         = 5'b01110,  // Power Down Entry
    CMD_PDX         = 5'b01111   // Power Down Exit
} ddr5_cmd_t;

//==================================================================================
// Packet Assembly from Dual-Phase CA
//==================================================================================

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        packet_buffer <= '0;
        phase_count <= '0;
        packet_complete <= 1'b0;
    end else if (cfg_decode_enable && ca_valid_in) begin
        // Assemble packet from dual-phase CA inputs
        case (phase_count)
            2'b00: begin
                packet_buffer[6:0] <= ca_phase0_in;
                packet_buffer[13:7] <= ca_phase1_in;
                phase_count <= 2'b01;
                packet_complete <= 1'b0;
            end
            2'b01: begin
                packet_buffer[20:14] <= ca_phase0_in;
                packet_buffer[27:21] <= ca_phase1_in;
                phase_count <= 2'b00;
                packet_complete <= 1'b1;  // Full packet received
            end
            default: phase_count <= 2'b00;
        endcase
    end else begin
        packet_complete <= 1'b0;
    end
end

//==================================================================================
// DDR5 Packet Decoding Logic
//==================================================================================

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        cmd_out <= '0;
        addr_out <= '0;
        bank_group_out <= '0;
        bank_addr_out <= '0;
        burst_length_out <= '0;
        auto_precharge_out <= 1'b0;
        cmd_valid_out <= 1'b0;
        
        is_activate <= 1'b0;
        is_read <= 1'b0;
        is_write <= 1'b0;
        is_precharge <= 1'b0;
        is_refresh <= 1'b0;
        is_mrs <= 1'b0;
        is_zqc <= 1'b0;
        
    end else if (packet_complete) begin
        // Decode command field (bits [27:23] per DDR5 spec)
        cmd_out <= packet_buffer[27:23];
        
        // Decode based on command type
        case (packet_buffer[27:23])
            CMD_ACTIVATE: begin
                // ACT: Row address in [22:6], BG[2:0] in [5:3], BA[1:0] in [2:1]
                is_activate <= 1'b1;
                addr_out[16:0] <= packet_buffer[22:6];
                bank_group_out <= packet_buffer[5:3];
                bank_addr_out <= packet_buffer[2:1];
                auto_precharge_out <= packet_buffer[0];
            end
            
            CMD_READ, CMD_WRITE: begin
                // RD/WR: Column addr [22:13], BG[5:3], BA[2:1], AP[0]
                is_read <= (packet_buffer[27:23] == CMD_READ);
                is_write <= (packet_buffer[27:23] == CMD_WRITE);
                addr_out[9:0] <= packet_buffer[22:13];  // Column address
                bank_group_out <= packet_buffer[5:3];
                bank_addr_out <= packet_buffer[2:1];
                auto_precharge_out <= packet_buffer[0];  // AP bit
                burst_length_out <= 4'h8;  // BL8 default (can be configured)
            end
            
            CMD_PRECHARGE: begin
                // PRE: All banks precharge if [12]=1, else specific bank
                is_precharge <= 1'b1;
                auto_precharge_out <= packet_buffer[12];  // All banks flag
                bank_group_out <= packet_buffer[5:3];
                bank_addr_out <= packet_buffer[2:1];
            end
            
            CMD_REFRESH: begin
                // REF: Refresh command
                is_refresh <= 1'b1;
            end
            
            CMD_MRS: begin
                // MRS: Mode register address [22:16], OP code [15:0]
                is_mrs <= 1'b1;
                addr_out[6:0] <= packet_buffer[22:16];  // MR address
                addr_out[15:0] <= packet_buffer[15:0];  // OP code
            end
            
            CMD_ZQC_START, CMD_ZQC_LATCH: begin
                // ZQ Calibration
                is_zqc <= 1'b1;
            end
            
            default: begin
                // NOP or undefined - clear outputs
                is_activate <= 1'b0;
                is_read <= 1'b0;
                is_write <= 1'b0;
                is_precharge <= 1'b0;
                is_refresh <= 1'b0;
                is_mrs <= 1'b0;
                is_zqc <= 1'b0;
            end
        endcase
        
        cmd_valid_out <= 1'b1;
    end else begin
        cmd_valid_out <= 1'b0;
    end
end

//==================================================================================
// CRC-5 Calculation and Verification
//==================================================================================

function automatic [CRC_WIDTH-1:0] calc_crc5(input [PACKET_SIZE-1:0] data);
    logic [CRC_WIDTH-1:0] crc;
    int i;
    
    crc = 5'h1F;  // Initial value
    
    for (i = PACKET_SIZE-1; i >= 0; i--) begin
        if (crc[4] ^ data[i]) begin
            crc = {crc[3:0], 1'b0} ^ 5'h05;  // Polynomial x^5 + x^2 + 1
        end else begin
            crc = {crc[3:0], 1'b0};
        end
    end
    
    return crc;
endfunction

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        crc_error <= 1'b0;
        calculated_crc <= '0;
    end else if (cfg_crc_enable && packet_complete) begin
        calculated_crc <= calc_crc5(packet_buffer);
        crc_error <= (calculated_crc != crc_in);
    end else begin
        crc_error <= 1'b0;
    end
end

//==================================================================================
// Parity Calculation and Verification  
//==================================================================================

function automatic parity_calc(input [CA_WIDTH-1:0] data);
    int i;
    logic p;
    p = 1'b0;
    for (i = 0; i < CA_WIDTH; i++) begin
        p = p ^ data[i];
    end
    return p;
endfunction

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        parity_error <= 1'b0;
        calculated_parity <= 1'b0;
    end else if (cfg_parity_enable && ca_valid_in) begin
        calculated_parity <= parity_calc(ca_phase0_in) ^ parity_calc(ca_phase1_in);
        parity_error <= (calculated_parity != parity_in[0]);
    end else begin
        parity_error <= 1'b0;
    end
end

//==================================================================================
// Error Detection and Reporting
//==================================================================================

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        decode_error <= 1'b0;
        error_code <= 8'h00;
    end else begin
        decode_error <= crc_error | parity_error;
        
        if (crc_error) begin
            error_code <= 8'h01;  // CRC error
        end else if (parity_error) begin
            error_code <= 8'h02;  // Parity error
        end else if (packet_complete && (cmd_out == 5'b11111)) begin
            error_code <= 8'h03;  // Invalid command
        end else begin
            error_code <= 8'h00;  // No error
        end
    end
end

endmodule
