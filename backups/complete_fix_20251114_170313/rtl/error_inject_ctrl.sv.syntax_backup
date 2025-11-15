////////////////////////////////////////////////////////////////////////////////
// Module: error_inject_ctrl.sv
// Description: Error injection module for test bench scenarios
//              Supports runtime configuration, programmable injection sites,
//              ECC/CRC/parity error injection, and active control port
// Author: RTL Design
// Date: November 2025
////////////////////////////////////////////////////////////////////////////////

module error_inject_ctrl #(
  parameter int ERROR_WIDTH = 128,     
  parameter int NUM_INJECT_SITES = 16,  
  parameter int CONFIG_DEPTH = 32       // Configuration register depth
)(
  input  logic                        clk,
  input  logic                        rst_n,
  
  // Control interface
  input  logic                        inject_enable,
  input  logic [3:0]                  inject_type,      
  input  logic [NUM_INJECT_SITES-1:0] inject_site_sel,  
  input  logic [15:0]                 inject_duration,  
  
  // Configuration interface (AXI-Lite compatible)
  input  logic [6:0]                  cfg_addr,
  input  logic                        cfg_wr_valid,
  input  logic                        cfg_rd_valid,
  input  logic [31:0]                 cfg_wr_data,
  output logic [31:0]                 cfg_rd_data,
  
  // Error injection bus
  output logic [ERROR_WIDTH-1:0]       error_inject_bus,
  
  // Status signals
  output logic                        inject_active,
  output logic [NUM_INJECT_SITES-1:0] active_sites,
  output logic [15:0]                 error_count
);

  // Internal registers
  logic [31:0]                        config_mem [0:CONFIG_DEPTH-1];
  logic [ERROR_WIDTH-1:0]              error_payload;
  logic [15:0]                        inject_counter;
  logic [15:0]                        total_errors;
  logic [NUM_INJECT_SITES-1:0]         site_active;
  
  // Configuration register indices
  localparam CTRL_REG = 7'h00;           // Control register
  localparam ERR_TYPE_REG = 7'h04;       // Error type
  localparam SITE_SEL_REG = 7'h08;       // Site selection
  localparam DURATION_REG = 7'h0C;       // Duration
  localparam PAYLOAD_REG = 7'h10;        // Error payload
  localparam STATUS_REG = 7'h14;         // Status register
  localparam ERR_CNT_REG = 7'h18;        // Error count register
  
  // Error injection payload generation
  always_comb begin
    case (inject_type)
      4'h0: begin // ECC Single-bit error (Hamming code)
        error_payload = {ERROR_WIDTH-1{1'b0}};
        case (inject_site_sel) inside
          16'h0001: error_payload[0] = 1'b1;
          16'h0002: error_payload[1] = 1'b1;
          16'h0004: error_payload[2] = 1'b1;
          16'h0008: error_payload[3] = 1'b1;
          16'h0010: error_payload[4] = 1'b1;
          16'h0020: error_payload[5] = 1'b1;
          16'h0040: error_payload[6] = 1'b1;
          16'h0080: error_payload[7] = 1'b1;
          default: error_payload = {ERROR_WIDTH{1'b0}};
        endcase
      end
      
      4'h1: begin // CRC error (multi-bit)
        error_payload = 32'hDEADBEEF;  // CRC syndrome pattern
        error_payload = {error_payload, {ERROR_WIDTH-32{1'b0}}};
      end
      
      4'h2: begin // Parity error
        error_payload = {ERROR_WIDTH{1'b1}} >> 1;
      end
      
      4'h3: begin // Multi-bit error
        error_payload = 32'h0F0F0F0F;  // Alternating bits
        error_payload = {error_payload, {ERROR_WIDTH-32{1'b0}}};
      end
      
      default: error_payload = {ERROR_WIDTH{1'b0}};
    endcase
  end
  
  // Injection control logic
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      inject_counter <= 16'h0000;
      site_active <= {NUM_INJECT_SITES{1'b0}};
      total_errors <= 16'h0000;
      error_inject_bus <= {ERROR_WIDTH{1'b0}};
    end
    else begin
      if (inject_enable && (inject_counter == 16'h0000)) begin
        // Start new injection cycle
        inject_counter <= inject_duration;
        site_active <= inject_site_sel;
        total_errors <= total_errors + 1;
      end
      else if (inject_counter > 16'h0001) begin
        // Maintain injection
        inject_counter <= inject_counter - 1;
      end
      else if (inject_counter == 16'h0001) begin
        // End injection cycle
        inject_counter <= 16'h0000;
        site_active <= {NUM_INJECT_SITES{1'b0}};
      end
      
      // Update error injection bus
      if (inject_counter > 16'h0000) begin
        error_inject_bus <= error_payload;
      end
      else begin
        error_inject_bus <= {ERROR_WIDTH{1'b0}};
      end
    end
  end
  
  // Configuration interface logic
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (int i = 0; i < CONFIG_DEPTH; i++) begin
        config_mem[i] <= 32'h00000000;
      end
    end
    else if (cfg_wr_valid) begin
      config_mem[cfg_addr[6:2]] <= cfg_wr_data;
    end
  end
  
  // Configuration read logic
  always_comb begin
    case (cfg_addr[6:2])
      5'h00: cfg_rd_data = {31'h0, inject_enable}; // Control
      5'h01: cfg_rd_data = {28'h0, inject_type};   // Error type
      5'h02: cfg_rd_data = {{(32-NUM_INJECT_SITES){1'b0}}, inject_site_sel}; // Sites
      5'h03: cfg_rd_data = {16'h0, inject_duration};  // Duration
      5'h04: cfg_rd_data = {16'h0, inject_counter};   // Payload/Status
      5'h05: cfg_rd_data = {15'h0, inject_active, site_active[16:1]}; // Status
      5'h06: cfg_rd_data = {16'h0, total_errors};  // Error count
      default: cfg_rd_data = 32'h00000000;
    endcase
  end
  
  // Output assignments
  assign inject_active = (inject_counter > 16'h0000) ? 1'b1 : 1'b0;
  assign active_sites = site_active;
  assign error_count = total_errors;

endmodule
