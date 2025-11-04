//==================================================================================
// Module: ca_packetizer
// Description: Command/Address (CA) packetization logic for DDR5 RCD
//              Converts command/address information into DDR5-compliant packets
//              Handles packet formation, encoding, and transmission scheduling
// Author: Auto-generated skeleton
// Date: 2025-11-04
//==================================================================================
module ca_packetizer #(
  // CA Interface Parameters
  parameter int CA_WIDTH = 7,                   // Width of CA bus
  parameter int CA_PHASES = 2,                  // Number of CA phases per command
  parameter int ADDR_WIDTH = 17,                // Address width
  parameter int CMD_WIDTH = 4,                  // Command width

  // Packet Parameters
  parameter int PACKET_SIZE = 14,               // Total packet size in bits
  parameter int CRC_WIDTH = 5,                  // CRC width for error detection
  parameter int PARITY_WIDTH = 1,               // Parity bit width

  // Timing Parameters
  parameter int PIPELINE_STAGES = 2,            // Number of pipeline stages
  parameter int BUFFER_DEPTH = 4                // Command buffer depth
) (
  // Clock and Reset
  input  logic                              clk,              // Primary clock
  input  logic                              rst_n,            // Active-low reset

  // Configuration Interface
  input  logic                              cfg_enable,       // Enable packetizer
  input  logic [1:0]                        cfg_ca_mode,      // CA mode selection
  input  logic                              cfg_crc_enable,   // Enable CRC generation
  input  logic                              cfg_parity_enable,// Enable parity generation

  // Command/Address Input Interface
  input  logic [CMD_WIDTH-1:0]              cmd_in,           // Command input
  input  logic [ADDR_WIDTH-1:0]             addr_in,          // Address input
  input  logic                              cmd_valid,        // Command valid
  output logic                              cmd_ready,        // Ready to accept command

  // Additional Command Information
  input  logic [2:0]                        bank_group,       // Bank group
  input  logic [1:0]                        bank_addr,        // Bank address
  input  logic [3:0]                        burst_length,     // Burst length
  input  logic                              auto_precharge,   // Auto-precharge flag

  // CA Output Interface (to DRAM)
  output logic [CA_WIDTH-1:0]               ca_out,           // CA output
  output logic                              ca_valid,         // CA valid
  input  logic                              ca_ready,         // CA ready

  // CA Phase Outputs (dual-edge)
  output logic [CA_WIDTH-1:0]               ca_phase0,        // CA phase 0 (rising edge)
  output logic [CA_WIDTH-1:0]               ca_phase1,        // CA phase 1 (falling edge)
  output logic                              ca_phase_valid,   // Both phases valid

  // CRC/Parity Output
  output logic [CRC_WIDTH-1:0]              crc_out,          // CRC value
  output logic [PARITY_WIDTH-1:0]           parity_out,       // Parity value
  output logic                              crc_valid,        // CRC valid

  // Status and Control
  output logic [3:0]                        buffer_count,     // Number of buffered commands
  output logic                              buffer_full,      // Buffer full indicator
  output logic                              buffer_empty,     // Buffer empty indicator
  output logic                              packet_error,     // Packet formation error
  output logic [7:0]                        error_code        // Error code
);
//==================================================================================
// Internal Signals
//==================================================================================
logic [CMD_WIDTH-1:0]           cmd_buf      [BUFFER_DEPTH-1:0]; // Command FIFO
logic [ADDR_WIDTH-1:0]          addr_buf     [BUFFER_DEPTH-1:0]; // Addr FIFO
logic [2:0]                     bank_grp_buf [BUFFER_DEPTH-1:0]; // BankGrp FIFO
logic [1:0]                     bank_addr_buf[BUFFER_DEPTH-1:0]; // BankAddr FIFO
logic [3:0]                     burst_len_buf[BUFFER_DEPTH-1:0]; // BurstLen FIFO
logic                           ap_buf       [BUFFER_DEPTH-1:0]; // AutoPrecharge FIFO
logic [3:0]                     wptr, rptr;      // Buffer write/read pointers
logic                           buf_full, buf_empty; // FIFO flags
logic [PACKET_SIZE-1:0]         packet;     // Internal CA packet
logic [CA_WIDTH-1:0]            phase0_data, phase1_data; // Outputs for DDR5 CA phases
logic [CRC_WIDTH-1:0]           crc_data;   // CRC value
logic                           parity_bit; // Parity value
//==================================================================================
// Command Buffer Management
//==================================================================================
// Simple FIFO logic
assign buf_empty = (wptr == rptr);
assign buf_full  = ((wptr + 1'b1) == rptr);
assign buffer_count = (wptr >= rptr) ? (wptr - rptr) : (BUFFER_DEPTH + wptr - rptr);
assign buffer_full  = buf_full;
assign buffer_empty = buf_empty;
assign cmd_ready    = !buf_full;
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    wptr <= 0;
    rptr <= 0;
  end else begin
    // Write incoming command to buffer
    if (cmd_valid && cmd_ready) begin
      cmd_buf[wptr]       <= cmd_in;
      addr_buf[wptr]      <= addr_in;
      bank_grp_buf[wptr]  <= bank_group;
      bank_addr_buf[wptr] <= bank_addr;
      burst_len_buf[wptr] <= burst_length;
      ap_buf[wptr]        <= auto_precharge;
      wptr                <= wptr + 1;
    end
    // Advance read pointer on CA readiness
    if (ca_ready && ca_valid && !buf_empty) begin
      rptr <= rptr + 1;
    end
  end
end
//==================================================================================
// Packet Formation Logic
//==================================================================================
// DDR5 CA packet format assembly (example mapping)
// | bank[2:0] | bank_addr[1:0] | cmd[3:0] | addr[6:0] |
always_comb begin
  packet = 0;
  packet[13:11] = bank_grp_buf[rptr];                  // Bank group
  packet[10:9]  = bank_addr_buf[rptr];                 // Bank address
  packet[8:5]   = cmd_buf[rptr];                       // Command
  packet[4:0]   = addr_buf[rptr][6:2];                 // Address bits
  // If required by mode, could include burst_len, AP, etc.
  // TODO: Update field mappings per full DDR5 spec if addr/cmd wider
  // ECC/parity fields added in next blocks as per spec
end
//==================================================================================
// CA Phase Generation
//==================================================================================
// Encode CA signals into packet format per DDR5 spec (DUAL-PHASE)
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    ca_phase0     <= 0;
    ca_phase1     <= 0;
    ca_phase_valid<= 0;
    ca_out        <= 0;
    ca_valid      <= 0;
  end else if (cfg_enable && !buf_empty) begin
    // Split packet across 2 CA phases (7 bits each)
    phase0_data = packet[6:0];     // First half (rising edge)
    phase1_data = packet[13:7];    // Second half (falling edge)
    ca_phase0   <= phase0_data;
    ca_phase1   <= phase1_data;
    ca_out      <= phase0_data;    // can be switched based on scheduling
    ca_valid    <= 1'b1;
    ca_phase_valid <= 1'b1;
  end else begin
    ca_valid <= 1'b0;
    ca_phase_valid <= 1'b0;
  end
end
//==================================================================================
// CRC Generation
//==================================================================================
function automatic [CRC_WIDTH-1:0] calc_crc(input [PACKET_SIZE-1:0] data);
  // CRC-5 (example poly 0x15) over packet
  int i;
  logic [CRC_WIDTH-1:0] crc;
  crc = 5'b0;
  for (i = PACKET_SIZE-1; i >= 0; i--) begin
    crc = crc ^ {data[i], crc[CRC_WIDTH-1:1]};
    if (crc[0]) crc = crc ^ 5'h15; // Example polynomial
  end
  return crc;
endfunction
// CRC block
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    crc_out   <= 0;
    crc_valid <= 0;
  end else if (cfg_crc_enable && !buf_empty) begin
    crc_data = calc_crc(packet);
    crc_out   <= crc_data;
    crc_valid <= 1'b1;
  end else begin
    crc_valid <= 1'b0;
  end
end
//==================================================================================
// Parity Generation
//==================================================================================
function automatic parity_calc(input [CA_WIDTH-1:0] data);
  int i;
  logic res;
  res = 0;
  for (i = 0; i < CA_WIDTH; i++)
    res = res ^ data[i];
  return res;
endfunction
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    parity_out <= 0;
  end else if (cfg_parity_enable && !buf_empty) begin
    parity_bit = parity_calc(phase0_data);
    parity_out <= parity_bit;
  end
end
//==================================================================================
// Error Detection and Reporting
//==================================================================================
assign packet_error = buf_full;          // Example: buffer overflow
assign error_code   = buf_full ? 8'h01 : 8'h00;
//==================================================================================
// Endmodule
//==================================================================================
endmodule
