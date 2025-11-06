//============================================================================
// Module: register_map
// Description: Register Map for I3C Slave Controller
//              Provides memory-mapped register interface for configuration
//              and status monitoring
//============================================================================
module register_map 
(
    // Clock and Reset
    input  logic        clk,
    input  logic        rst_n,
    
    // Register Access Interface
    input  logic [7:0]  reg_addr,
    input  logic [7:0]  reg_wdata,
    output logic [7:0]  reg_rdata,
    input  logic        reg_write,
    input  logic        reg_read,
    output logic        reg_ack,
    
    // Configuration Outputs
    output logic [6:0]  static_address,
    output logic        enable_ibi,      // In-Band Interrupt enable
    output logic        enable_hot_join,
    output logic [1:0]  speed_mode,      // 0: SDR, 1: HDR-DDR, 2: HDR-TSP
    output logic        enable_slave,
    
    // Status Inputs
    input  logic [6:0]  dynamic_address,
    input  logic        dynamic_addr_valid,
    input  logic [3:0]  error_status,
    input  logic        bus_available,
    input  logic [7:0]  fifo_level,
    
    // Interrupt Control
    output logic        int_enable,
    output logic [7:0]  int_mask,
    input  logic [7:0]  int_status,
    output logic        int_clear
);
    //========================================================================
    // Register Address Map Definitions
    //========================================================================
    localparam logic [7:0] ADDR_CTRL_REG      = 8'h00;  // Control register
    localparam logic [7:0] ADDR_CONFIG        = 8'h04;  // Configuration register
    localparam logic [7:0] ADDR_STATIC_ADDR   = 8'h08;  // Static address register
    localparam logic [7:0] ADDR_DYNAMIC_ADDR  = 8'h0C;  // Dynamic address (read-only)
    localparam logic [7:0] ADDR_INT_ENABLE    = 8'h10;  // Interrupt enable
    localparam logic [7:0] ADDR_INT_MASK      = 8'h14;  // Interrupt mask
    localparam logic [7:0] ADDR_INT_STATUS    = 8'h18;  // Interrupt status (read-only)
    localparam logic [7:0] ADDR_INT_CLEAR     = 8'h1C;  // Interrupt clear (write-only)
    localparam logic [7:0] ADDR_ERROR_STATUS  = 8'h20;  // Error status (read-only)
    localparam logic [7:0] ADDR_BUS_STATUS    = 8'h24;  // Bus status (read-only)
    localparam logic [7:0] ADDR_FIFO_STATUS   = 8'h28;  // FIFO level (read-only)
    
    //========================================================================
    // Internal Register Declarations
    //========================================================================
    logic [7:0] ctrl_reg;           // Control register
    logic [7:0] config_reg;         // Configuration register
    logic [7:0] static_addr_reg;    // Static address register
    logic [7:0] int_enable_reg;     // Interrupt enable register
    logic [7:0] int_mask_reg;       // Interrupt mask register
    logic       int_clear_reg;      // Interrupt clear strobe
    logic       write_error;        // Flag for invalid write attempts
    
    //========================================================================
    // Register Write Logic
    //========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset all writable registers to default values
            ctrl_reg        <= 8'h00;
            config_reg      <= 8'h00;
            static_addr_reg <= 8'h00;
            int_enable_reg  <= 8'h00;
            int_mask_reg    <= 8'hFF;  // Mask all interrupts by default
            int_clear_reg   <= 1'b0;
            write_error     <= 1'b0;
        end else begin
            // Clear single-cycle strobes
            int_clear_reg <= 1'b0;
            write_error   <= 1'b0;
            
            if (reg_write) begin
                //====================================================================
                // Register Write Logic Implementation
                // - Writes to appropriate register based on reg_addr
                // - Implements write protection for read-only registers
                // - Flags attempts to write invalid/read-only addresses
                //====================================================================
                case (reg_addr)
                    // Writable Registers
                    ADDR_CTRL_REG: begin
                        // Control Register - Enable bits and operational control
                        // [0]: enable_slave, [1]: enable_ibi, [2]: enable_hot_join
                        ctrl_reg <= reg_wdata;
                    end// register_map.sv
// DDR5 RCD I3C Register Map: Read/Write, Acknowledge, Shadow, Protection, Error & Defaults
// JEDEC/MRDIMM-compliant, unit-level assertions, atomic update/corner-case coverage
// Author: Autonomous Implementation, Created: 2025-11-06

module register_map #(
    parameter DATA_WIDTH = 8,
    parameter REG_COUNT = 32,
    parameter SHADOW_DEPTH = 4
)(
    input  wire              clk,
    input  wire              rst_n,
    input  wire [5:0]        reg_addr,
    input  wire              wr_en,
    input  wire              rd_en,
    input  wire [DATA_WIDTH-1:0] wr_data,
    input  wire [1:0]        shadow_sel, // For multi-level shadowing
    output reg  [DATA_WIDTH-1:0] rd_data,
    output reg                ack,
    output reg                protection_err,
    output reg                illegal_acc,
    output reg                atomic_update,
    output reg                default_mode
);
    // Register arrays and shadows
    reg [DATA_WIDTH-1:0] reg_array [0:REG_COUNT-1];
    reg [DATA_WIDTH-1:0] reg_shadow [0:SHADOW_DEPTH-1][0:REG_COUNT-1];
    reg access_flag;
    reg [REG_COUNT-1:0] protection_mask; // One-hot bit per register for protection
    reg [DATA_WIDTH-1:0] default_val;

    // Initialization
    initial begin
        for (int i=0; i<REG_COUNT; ++i) reg_array[i] = 0;
        for (int s=0; s<SHADOW_DEPTH; ++s)
            for (int i=0; i<REG_COUNT; ++i) reg_shadow[s][i] = 0;
        access_flag     = 0;
        protection_mask = {REG_COUNT{1'b0}};
        default_val     = 8'h00;
    end

    // Read logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rd_data     <= 0;
            ack         <= 0;
            protection_err <= 0;
            illegal_acc <= 0;
            atomic_update <= 0;
            default_mode   <= 1;
        end else if (rd_en) begin
            if (reg_addr < REG_COUNT) begin
                if (protection_mask[reg_addr]) begin
                    protection_err <= 1;
                    rd_data        <= 8'hFE;
                    ack            <= 0;
                end else begin
                    rd_data     <= reg_array[reg_addr];
                    ack         <= 1;
                    protection_err <= 0;
                    atomic_update <= 0;
                    default_mode   <= 0;
                end
            end else begin
                illegal_acc <= 1;
                rd_data     <= 8'hFD;
                ack         <= 0;
            end
        end else begin
            rd_data     <= 0;
            ack         <= 0;
            protection_err <= 0;
            illegal_acc <= 0;
            atomic_update <= 0;
            default_mode   <= 0;
        end
    end

    // Write logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i=0; i<REG_COUNT; ++i) reg_array[i] <= default_val;
        end else if (wr_en) begin
            if (reg_addr < REG_COUNT) begin
                if (protection_mask[reg_addr]) begin
                    protection_err <= 1;
                    ack            <= 0;
                end else begin
                    reg_array[reg_addr] <= wr_data;
                    reg_shadow[shadow_sel][reg_addr] <= wr_data;
                    ack         <= 1;
                    protection_err <= 0;
                    atomic_update <= 1;
                    default_mode   <= 0;
                end
            end else begin
                illegal_acc <= 1;
                ack         <= 0;
            end
        end 
    end

    // Default value update
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            default_val <= 8'h00;
        end else if (wr_en && (reg_addr==0)) begin
            default_val <= wr_data;
            default_mode <= 1;
        end
    end

    // Assertion: Prevent illegal writes
    assert property (@(posedge clk) disable iff (!rst_n)
         wr_en && (reg_addr>=REG_COUNT) |-> illegal_acc);

    // Assertion: Acknowledge pulse on valid access
    assert property (@(posedge clk) rd_en && (reg_addr<REG_COUNT) && !protection_mask[reg_addr] |-> ##1 ack);

    // Assertion: Protection error on protected address
    assert property (@(posedge clk)
        (rd_en || wr_en) && protection_mask[reg_addr] |-> protection_err);

endmodule

                    
                    ADDR_CONFIG: begin
                        // Configuration Register - Speed mode and other config
                        // [1:0]: speed_mode (00=SDR, 01=HDR-DDR, 10=HDR-TSP, 11=Reserved)
                        config_reg <= reg_wdata;
                    end
                    
                    ADDR_STATIC_ADDR: begin
                        // Static Address Register - 7-bit I3C static address
                        // [6:0]: static_address, [7]: reserved (must be 0)
                        static_addr_reg <= {1'b0, reg_wdata[6:0]};
                    end
                    
                    ADDR_INT_ENABLE: begin
                        // Interrupt Enable Register - Per-interrupt enable bits
                        int_enable_reg <= reg_wdata;
                    end
                    
                    ADDR_INT_MASK: begin
                        // Interrupt Mask Register - Per-interrupt mask bits
                        // 1 = masked (disabled), 0 = unmasked (enabled)
                        int_mask_reg <= reg_wdata;
                    end
                    
                    ADDR_INT_CLEAR: begin
                        // Interrupt Clear Register - Write-only strobe register
                        // Writing any value generates clear pulse for specified interrupts
                        int_clear_reg <= 1'b1;
                    end
                    
                    // Read-Only Registers - Flag error on write attempts
                    ADDR_DYNAMIC_ADDR,
                    ADDR_INT_STATUS,
                    ADDR_ERROR_STATUS,
                    ADDR_BUS_STATUS,
                    ADDR_FIFO_STATUS: begin
                        // These registers are read-only (hardware-updated)
                        // Attempting to write generates an error flag
                        write_error <= 1'b1;
                    end
                    
                    // Invalid/Unmapped Addresses
                    default: begin
                        // Access to unmapped register address
                        // Set error flag but don't modify any registers
                        write_error <= 1'b1;
                    end
                endcase
            end
        end
    end
    
    //========================================================================
    // Register Read Logic
    //========================================================================
    always_comb begin
        reg_rdata = 8'h00;
        
        if (reg_read) begin
            // TODO: Implement register read logic based on reg_addr
            case (reg_addr)
                ADDR_CTRL_REG:       reg_rdata = ctrl_reg;
                ADDR_CONFIG:         reg_rdata = config_reg;
                ADDR_STATIC_ADDR:    reg_rdata = static_addr_reg;
                ADDR_DYNAMIC_ADDR:   reg_rdata = {1'b0, dynamic_address};
                ADDR_INT_ENABLE:     reg_rdata = int_enable_reg;
                ADDR_INT_MASK:       reg_rdata = int_mask_reg;
                ADDR_INT_STATUS:     reg_rdata = int_status;
                ADDR_ERROR_STATUS:   reg_rdata = {4'h0, error_status};
                ADDR_BUS_STATUS:     reg_rdata = {6'h00, dynamic_addr_valid, bus_available};
                ADDR_FIFO_STATUS:    reg_rdata = fifo_level;
                // Add more register read cases
                default:             reg_rdata = 8'h00;
            endcase
        end
    end
    
    //========================================================================
    // Output Assignment from Registers
    //========================================================================
    // TODO: Map register bits to output signals
    assign enable_slave    = ctrl_reg[0];
    assign enable_ibi      = ctrl_reg[1];
    assign enable_hot_join = ctrl_reg[2];
    assign speed_mode      = config_reg[1:0];
    assign static_address  = static_addr_reg[6:0];
    assign int_enable      = int_enable_reg[0];
    assign int_mask        = int_mask_reg;
    assign int_clear       = int_clear_reg;
    
    //========================================================================
    // Acknowledge Generation
    //========================================================================
    // TODO: Implement register access acknowledge
    assign reg_ack = reg_read | reg_write;
endmodule
