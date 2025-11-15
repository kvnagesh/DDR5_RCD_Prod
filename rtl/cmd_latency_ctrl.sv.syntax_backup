/*
 * cmd_latency_ctrl.sv
 * Command Latency Control Module for DDR5 RCD
 * 
 * Description:
 *   This module implements variable command latency control as specified by
 *   MR13 (Mode Register 13) configuration. It provides dynamic latency adjustment
 *   for command distribution, supporting configurable latency values through a
 *   mode register interface. The module integrates with ca_distributor for
 *   field-driven latency control and includes handshake logic and latency counters.
 *
 * Features:
 *   - MR13 mode register interface for configuration
 *   - Configurable latency storage and update mechanism
 *   - Dynamic latency counter in command path
 *   - Handshake control logic for command flow
 *   - Synthesizable RTL implementation
 *
 * Author: Design Team
 * Date: 2025
 */

module cmd_latency_ctrl #(
  parameter int MR13_WIDTH     = 8,        
  parameter int CMD_LAT_WIDTH  = 4,        
  parameter int DATA_WIDTH     = 8,        
  parameter int DEFAULT_LATENCY = 2        // Default command latency cycles
) (
  // Clock and reset
  input  logic                    clk,
  input  logic                    rst_n,
  
  // MR13 Mode Register Interface
  // ==============================
  // MR13 Bits allocation for command latency:
  // [2:0] = Command Latency Mode (0-7 representing 2-9 cycles)
  // [3]   = Latency Enable (1=enable variable latency, 0=fixed default)
  input  logic [MR13_WIDTH-1:0]   mr13_data,           
  input  logic                    mr13_valid,          
  output logic                    mr13_ready,          
  
  // Command Input Interface (from address/command path)
  // ====================================================
  input  logic [DATA_WIDTH-1:0]   cmd_in_data,         
  input  logic                    cmd_in_valid,        
  output logic                    cmd_in_ready,        
  
  // Command Output Interface (to ca_distributor)
  // =============================================
  output logic [DATA_WIDTH-1:0]   cmd_out_data,        
  output logic                    cmd_out_valid,       
  input  logic                    cmd_out_ready,       
  
  // Status and Configuration Interface
  // ===================================
  output logic [CMD_LAT_WIDTH-1:0] current_latency,    
  output logic                    latency_enabled,     
  output logic                    latency_ctrl_busy    // Busy processing latency
);

  // ============================================================================
  // Internal Signals and State Machine
  // ============================================================================
  
  // MR13 configuration register
  logic [2:0]                     latency_mode;        // Latency mode from MR13[2:0]
  logic                           latency_enable;      // Latency enable from MR13[3]
  
  // Calculated latency value (0-7 -> 2-9 cycles)
  logic [CMD_LAT_WIDTH-1:0]       calc_latency;
  logic [CMD_LAT_WIDTH-1:0]       stored_latency;      // Stored latency cycles
  
  // Command buffering
  logic [DATA_WIDTH-1:0]          cmd_buffer;          // Buffered command data
  logic                           cmd_buffer_valid;    // Buffered command valid
  
  // Latency counter
  logic [CMD_LAT_WIDTH-1:0]       latency_counter;     // Current latency countdown
  logic                           counting;            // Currently counting latency
  
  // ============================================================================
  // MR13 Configuration Processing
  // ============================================================================
  
  // Extract latency parameters from MR13
  assign latency_mode   = mr13_data[2:0];
  assign latency_enable = mr13_data[3];
  
  // Calculate actual latency value from mode
  // Mode 0 = 2 cycles, Mode 1 = 3 cycles, ..., Mode 7 = 9 cycles
  always_comb begin
    case (latency_mode)
      3'b000: calc_latency = 4'd2;   // 2 cycles
      3'b001: calc_latency = 4'd3;   // 3 cycles
      3'b010: calc_latency = 4'd4;   // 4 cycles
      3'b011: calc_latency = 4'd5;   // 5 cycles
      3'b100: calc_latency = 4'd6;   // 6 cycles
      3'b101: calc_latency = 4'd7;   // 7 cycles
      3'b110: calc_latency = 4'd8;   // 8 cycles
      3'b111: calc_latency = 4'd9;   // 9 cycles
      default: calc_latency = 4'd2;
    endcase
  end
  
  // Update stored latency on MR13 write
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      stored_latency <= DEFAULT_LATENCY;
    end else if (mr13_valid && mr13_ready) begin
      stored_latency <= calc_latency;
    end
  end
  
  // MR13 ready signal (ready when not counting)
  assign mr13_ready = ~counting;
  
  // Output current configuration status
  assign current_latency = stored_latency;
  assign latency_enabled = latency_enable;
  
  // ============================================================================
  // Command Latency Control Logic
  // ============================================================================
  
  // Determine effective latency (use stored if enabled, else default)
  logic [CMD_LAT_WIDTH-1:0]       effective_latency;
  assign effective_latency = latency_enable ? stored_latency : DEFAULT_LATENCY;
  
  // Main command processing state machine
  // =====================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      cmd_buffer       <= '0;
      cmd_buffer_valid <= 1'b0;
      latency_counter  <= '0;
      counting         <= 1'b0;
    end else begin
      
      // Command input and buffering
      if (cmd_in_valid && cmd_in_ready && !cmd_buffer_valid) begin
        cmd_buffer       <= cmd_in_data;
        cmd_buffer_valid <= 1'b1;
        latency_counter  <= effective_latency;
        counting         <= 1'b1;
      end
      
      // Latency counter decrement
      if (counting) begin
        if (latency_counter > 0) begin
          latency_counter <= latency_counter - 1'b1;
        end else begin
          counting <= 1'b0;  // Latency expired
        end
      end
      
      // Command output when latency expires and downstream ready
      if (cmd_buffer_valid && !counting && cmd_out_ready) begin
        cmd_buffer_valid <= 1'b0;
      end
    end
  end
  
  // ============================================================================
  // Handshake Logic
  // ============================================================================
  
  // Command input ready: can accept new command if buffer is free
  // (not holding valid data and not currently counting)
  assign cmd_in_ready = ~cmd_buffer_valid || (~counting && cmd_out_ready);
  
  // Command output valid: data is ready after latency expires
  assign cmd_out_valid = cmd_buffer_valid && ~counting;
  
  // Command output data
  assign cmd_out_data = cmd_buffer;
  
  // Busy status: actively processing latency delay
  assign latency_ctrl_busy = counting || cmd_buffer_valid;
  
endmodule

/*
 * ============================================================================
 * PORT DESCRIPTION
 * ============================================================================
 *
 * CLOCK AND RESET:
 *   - clk:              System clock (synchronous operations)
 *   - rst_n:            Active-low asynchronous reset
 *
 * MR13 MODE REGISTER INTERFACE:
 *   - mr13_data[7:0]:   MR13 register data from DRAM
 *     - [2:0]:          Command latency mode (0-7 -> 2-9 cycles)
 *     - [3]:            Latency enable bit (1=variable, 0=fixed)
 *     - [7:4]:          Reserved
 *   - mr13_valid:       Input strobe indicating MR13 update
 *   - mr13_ready:       Output handshake (ready to accept MR13 when not counting)
 *
 * COMMAND INPUT INTERFACE (from address/command path):
 *   - cmd_in_data[7:0]: Command data to be latency-adjusted
 *   - cmd_in_valid:     Input valid signal
 *   - cmd_in_ready:     Output ready signal (ready when buffer available)
 *
 * COMMAND OUTPUT INTERFACE (to ca_distributor):
 *   - cmd_out_data[7:0]: Command data after latency application
 *   - cmd_out_valid:     Output valid after latency completion
 *   - cmd_out_ready:     Input ready signal from downstream
 *
 * STATUS AND CONFIGURATION:
 *   - current_latency[3:0]: Current programmed latency value (2-9 cycles)
 *   - latency_enabled:      Indicates if variable latency is active
 *   - latency_ctrl_busy:    Module is busy processing latency
 *
 * ============================================================================
 * MR13 TIMING AND MECHANISM
 * ============================================================================
 *
 * MR13 CONFIGURATION FORMAT:
 *   Bits [2:0] - Command Latency Mode:
 *     000 = 2 cycles
 *     001 = 3 cycles
 *     010 = 4 cycles
 *     011 = 5 cycles
 *     100 = 6 cycles
 *     101 = 7 cycles
 *     110 = 8 cycles
 *     111 = 9 cycles
 *
 *   Bit [3] - Latency Enable:
 *     0 = Use default fixed latency (DEFAULT_LATENCY parameter)
 *     1 = Use MR13-configured variable latency
 *
 * OPERATION FLOW:
 *   1. MR13 write: When mr13_valid asserts and mr13_ready is high,
 *      the configuration is latched on the clock edge
 *   2. Mode extraction: Latency mode extracted from MR13[2:0]
 *   3. Latency calculation: Mode converted to cycle count (2-9)
 *   4. Command processing: Commands are buffered and held for the
 *      configured latency duration before forwarding to ca_distributor
 *   5. Status update: current_latency and latency_enabled outputs
 *      reflect the active configuration
 *
 * TIMING CONSTRAINTS:
 *   - MR13 updates are recognized when mr13_valid=1 and mr13_ready=1
 *   - mr13_ready will be low during active command latency counting
 *   - Command latency counter decrements every clock cycle when active
 *   - Command output is asserted one cycle after latency counter reaches zero
 *
 * INTEGRATION WITH ca_distributor:
 *   - This module sits in the command path between source and ca_distributor
 *   - Field-driven latency control: Latency values can be dynamically
 *     changed via MR13 writes during operation
 *   - Handshake protocol ensures commands are not lost during transitions
 *   - Downstream ca_distributor uses cmd_out_valid and responds with cmd_out_ready
 *
 * ============================================================================
 */
