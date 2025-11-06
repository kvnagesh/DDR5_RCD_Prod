//==================================================================================
// Module: bcw_controller
// Description: Buffer Control Word (BCW) Controller for DDR5 RCD
//              - Manages BCW register programming and updates
//              - Handles configuration from host via I3C/I2C
//              - Controls RCD operational modes and settings
//              - Implements BCW protection and validation
// Author: Auto-generated for DDR5 RCD Production
// Date: 2025-11-06
//==================================================================================

module bcw_controller #(
    parameter int BCW_ADDR_WIDTH = 8,     // BCW address space
    parameter int BCW_DATA_WIDTH = 8,     // BCW data width
    parameter int NUM_BCW_REGS = 256      // Total BCW registers
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,
    
    // I3C/Configuration Interface
    input  logic                        cfg_write,
    input  logic                        cfg_read,
    input  logic [BCW_ADDR_WIDTH-1:0]   cfg_addr,
    input  logic [BCW_DATA_WIDTH-1:0]   cfg_wdata,
    output logic [BCW_DATA_WIDTH-1:0]   cfg_rdata,
    output logic                        cfg_ack,
    output logic                        cfg_error,
    
    // BCW Outputs to RCD blocks
    output logic [7:0]  bcw00_operating_mode,
    output logic [7:0]  bcw01_qck_driver_settings,
    output logic [7:0]  bcw02_qca_driver_settings,
    output logic [7:0]  bcw03_qcs_driver_settings,
    output logic [7:0]  bcw04_dck_driver_settings,
    output logic [7:0]  bcw05_dca_driver_settings,
    output logic [7:0]  bcw06_dcs_driver_settings,
    output logic [7:0]  bcw10_clock_mode,
    output logic [7:0]  bcw11_frequency_range,
    output logic [7:0]  bcw12_pll_settings,
    output logic [7:0]  bcw20_output_timing,
    output logic [7:0]  bcw21_input_timing,
    output logic [7:0]  bcw30_ecc_mode,
    output logic [7:0]  bcw31_parity_mode,
    output logic [7:0]  bcw40_power_mode,
    
    // Status outputs
    output logic        bcw_locked,           // BCW registers locked
    output logic        bcw_initialized,      // BCW initialization complete
    output logic [7:0]  bcw_error_status
);

//==================================================================================
// BCW Register Bank
//==================================================================================

logic [BCW_DATA_WIDTH-1:0] bcw_regs [NUM_BCW_REGS-1:0];
logic [NUM_BCW_REGS-1:0]   bcw_write_protect;  // Write protection per register
logic                      bcw_global_lock;

//==================================================================================
// BCW Initialization Values (Default per JEDEC spec)
//==================================================================================

localparam logic [7:0] BCW00_DEFAULT = 8'h01;  // Default operating mode
localparam logic [7:0] BCW01_DEFAULT = 8'h40;  // QCK driver mid-strength
localparam logic [7:0] BCW02_DEFAULT = 8'h40;  // QCA driver mid-strength
localparam logic [7:0] BCW03_DEFAULT = 8'h40;  // QCS driver mid-strength
localparam logic [7:0] BCW10_DEFAULT = 8'h00;  // Clock mode default
localparam logic [7:0] BCW11_DEFAULT = 8'h02;  // Frequency range

//==================================================================================
// BCW Register Write Logic
//==================================================================================

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        for (int i = 0; i < NUM_BCW_REGS; i++) begin
            bcw_regs[i] <= 8'h00;
        end
        
        // Load defaults for critical BCWs
        bcw_regs[8'h00] <= BCW00_DEFAULT;
        bcw_regs[8'h01] <= BCW01_DEFAULT;
        bcw_regs[8'h02] <= BCW02_DEFAULT;
        bcw_regs[8'h03] <= BCW03_DEFAULT;
        bcw_regs[8'h10] <= BCW10_DEFAULT;
        bcw_regs[8'h11] <= BCW11_DEFAULT;
        
        bcw_global_lock <= 1'b0;
        cfg_error <= 1'b0;
        
    end else begin
        cfg_error <= 1'b0;
        
        // Handle BCW write requests
        if (cfg_write) begin
            // Check write protection
            if (!bcw_global_lock && !bcw_write_protect[cfg_addr]) begin
                bcw_regs[cfg_addr] <= cfg_wdata;
            end else begin
                cfg_error <= 1'b1;  // Write to protected register
            end
        end
        
        // BCW lock control (BCW 0xFF)
        if (cfg_write && cfg_addr == 8'hFF) begin
            bcw_global_lock <= cfg_wdata[0];
        end
    end
end

//==================================================================================
// BCW Register Read Logic
//==================================================================================

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        cfg_rdata <= 8'h00;
        cfg_ack <= 1'b0;
    end else begin
        if (cfg_read) begin
            cfg_rdata <= bcw_regs[cfg_addr];
            cfg_ack <= 1'b1;
        end else begin
            cfg_ack <= 1'b0;
        end
    end
end

//==================================================================================
// BCW Output Mapping
//==================================================================================

assign bcw00_operating_mode       = bcw_regs[8'h00];
assign bcw01_qck_driver_settings  = bcw_regs[8'h01];
assign bcw02_qca_driver_settings  = bcw_regs[8'h02];
assign bcw03_qcs_driver_settings  = bcw_regs[8'h03];
assign bcw04_dck_driver_settings  = bcw_regs[8'h04];
assign bcw05_dca_driver_settings  = bcw_regs[8'h05];
assign bcw06_dcs_driver_settings  = bcw_regs[8'h06];
assign bcw10_clock_mode           = bcw_regs[8'h10];
assign bcw11_frequency_range      = bcw_regs[8'h11];
assign bcw12_pll_settings         = bcw_regs[8'h12];
assign bcw20_output_timing        = bcw_regs[8'h20];
assign bcw21_input_timing         = bcw_regs[8'h21];
assign bcw30_ecc_mode             = bcw_regs[8'h30];
assign bcw31_parity_mode          = bcw_regs[8'h31];
assign bcw40_power_mode           = bcw_regs[8'h40];

//==================================================================================
// BCW Status and Protection
//==================================================================================

assign bcw_locked = bcw_global_lock;
assign bcw_initialized = (bcw_regs[8'h00] != 8'h00);  // Non-zero operating mode

// Write protection for critical registers
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        bcw_write_protect <= '0;
    end else begin
        // Protect critical BCWs after initialization
        if (bcw_initialized) begin
            bcw_write_protect[8'h00] <= 1'b1;  // Operating mode
            bcw_write_protect[8'h10] <= 1'b1;  // Clock mode
        end
    end
end

// Error status register
assign bcw_error_status = {6'b0, cfg_error, bcw_global_lock};

endmodule
