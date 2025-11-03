//==============================================================================
// File: width_controller.sv
// Description: Parameterizable width controller for x4/x8 DRAM configuration
//              Supports runtime width configuration with handshake interface
// Author: Auto-generated for DDR5 RCD Project
// Date: November 2025
//==============================================================================

module width_controller #(
  parameter int DATA_WIDTH_X4 = 4,
  parameter int DATA_WIDTH_X8 = 8,
  parameter int MAX_DATA_WIDTH = 8,
  parameter int NUM_CHANNELS = 2
) (
  // Clock and Reset
  input  logic        clk,
  input  logic        rst_n,
  
  // Configuration Interface (Ready-Valid Handshake)
  input  logic        cfg_valid,
  output logic        cfg_ready,
  input  logic        cfg_width_select,    // 0=x4, 1=x8
  input  logic [1:0]  cfg_channel_mask,    // Channel enable mask
  
  // Status Interface
  output logic        width_config_done,
  output logic        width_config_error,
  output logic [2:0]  current_width_mode,  // Encoded current mode
  
  // Data Path Control
  output logic [MAX_DATA_WIDTH-1:0] dq_enable_mask,
  output logic [NUM_CHANNELS-1:0]   channel_enable,
  output logic                      data_path_ready,
  
  // DFI Interface Signals
  output logic [1:0]  dfi_data_width,      // 00=x4, 01=x8
  output logic        dfi_width_override,
  
  // Diagnostic/Debug
  output logic [7:0]  width_status_reg
);

  // Internal State Machine
  typedef enum logic [2:0] {
    IDLE          = 3'b000,
    VALIDATE_CFG  = 3'b001,
    APPLY_WIDTH   = 3'b010,
    UPDATE_MASK   = 3'b011,
    DONE          = 3'b100,
    ERROR         = 3'b101
  } state_t;
  
  state_t current_state, next_state;
  
  // Internal Registers
  logic        width_select_reg;
  logic [1:0]  channel_mask_reg;
  logic        config_locked;
  logic [3:0]  apply_counter;
  
  // Width Mode Encoding
  localparam logic [2:0] MODE_X4 = 3'b001;
  localparam logic [2:0] MODE_X8 = 3'b010;
  localparam logic [2:0] MODE_INVALID = 3'b111;
  
  //============================================================================
  // State Machine - Sequential Logic
  //============================================================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE;
    end else begin
      current_state <= next_state;
    end
  end
  
  //============================================================================
  // State Machine - Combinational Logic
  //============================================================================
  always_comb begin
    next_state = current_state;
    
    case (current_state)
      IDLE: begin
        if (cfg_valid && cfg_ready) begin
          next_state = VALIDATE_CFG;
        end
      end
      
      VALIDATE_CFG: begin
        // Validate channel mask is non-zero
        if (channel_mask_reg == 2'b00) begin
          next_state = ERROR;
        end else begin
          next_state = APPLY_WIDTH;
        end
      end
      
      APPLY_WIDTH: begin
        if (apply_counter >= 4'd3) begin  // Multi-cycle for timing closure
          next_state = UPDATE_MASK;
        end
      end
      
      UPDATE_MASK: begin
        next_state = DONE;
      end
      
      DONE: begin
        if (!config_locked) begin
          next_state = IDLE;
        end
      end
      
      ERROR: begin
        if (!cfg_valid) begin  // Wait for valid to deassert
          next_state = IDLE;
        end
      end
      
      default: next_state = IDLE;
    endcase
  end
  
  //============================================================================
  // Configuration Registers
  //============================================================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      width_select_reg <= 1'b0;  // Default x4
      channel_mask_reg <= 2'b11; // Both channels enabled
      config_locked    <= 1'b0;
      apply_counter    <= 4'b0;
    end else begin
      case (current_state)
        IDLE: begin
          if (cfg_valid && cfg_ready) begin
            width_select_reg <= cfg_width_select;
            channel_mask_reg <= cfg_channel_mask;
            config_locked    <= 1'b1;
          end
          apply_counter <= 4'b0;
        end
        
        APPLY_WIDTH: begin
          apply_counter <= apply_counter + 4'd1;
        end
        
        DONE: begin
          config_locked <= 1'b0;
        end
        
        ERROR: begin
          config_locked <= 1'b0;
        end
        
        default: begin
          apply_counter <= apply_counter;
        end
      endcase
    end
  end
  
  //============================================================================
  // DQ Enable Mask Generation
  //============================================================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      dq_enable_mask <= '0;
    end else if (current_state == UPDATE_MASK) begin
      if (width_select_reg == 1'b0) begin  // x4 mode
        dq_enable_mask <= {{(MAX_DATA_WIDTH-DATA_WIDTH_X4){1'b0}}, {DATA_WIDTH_X4{1'b1}}};
      end else begin  // x8 mode
        dq_enable_mask <= {MAX_DATA_WIDTH{1'b1}};
      end
    end
  end
  
  //============================================================================
  // Channel Enable Generation
  //============================================================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      channel_enable <= '0;
    end else if (current_state == UPDATE_MASK) begin
      channel_enable <= channel_mask_reg;
    end
  end
  
  //============================================================================
  // Control and Status Outputs
  //============================================================================
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      cfg_ready          <= 1'b1;
      width_config_done  <= 1'b0;
      width_config_error <= 1'b0;
      current_width_mode <= MODE_INVALID;
      data_path_ready    <= 1'b0;
      dfi_data_width     <= 2'b00;
      dfi_width_override <= 1'b0;
      width_status_reg   <= 8'h00;
    end else begin
      case (current_state)
        IDLE: begin
          cfg_ready          <= 1'b1;
          width_config_done  <= 1'b0;
          width_config_error <= 1'b0;
          data_path_ready    <= 1'b0;
        end
        
        VALIDATE_CFG: begin
          cfg_ready <= 1'b0;
        end
        
        APPLY_WIDTH: begin
          if (width_select_reg == 1'b0) begin
            dfi_data_width <= 2'b00;  // x4
            current_width_mode <= MODE_X4;
          end else begin
            dfi_data_width <= 2'b01;  // x8
            current_width_mode <= MODE_X8;
          end
          dfi_width_override <= 1'b1;
        end
        
        UPDATE_MASK: begin
          data_path_ready <= 1'b1;
        end
        
        DONE: begin
          width_config_done  <= 1'b1;
          width_config_error <= 1'b0;
          cfg_ready          <= 1'b1;
        end
        
        ERROR: begin
          width_config_done  <= 1'b0;
          width_config_error <= 1'b1;
          current_width_mode <= MODE_INVALID;
          cfg_ready          <= 1'b1;
        end
        
        default: begin
          cfg_ready <= 1'b1;
        end
      endcase
      
      // Status Register for Debug
      width_status_reg <= {current_state, width_select_reg, channel_mask_reg, 
                          width_config_done, width_config_error, data_path_ready};
    end
  end
  
  //============================================================================
  // Assertions for Verification
  //============================================================================
  `ifdef FORMAL
    // Property: cfg_ready must be high in IDLE state
    property p_ready_in_idle;
      @(posedge clk) disable iff (!rst_n)
      (current_state == IDLE) |-> cfg_ready;
    endproperty
    assert property (p_ready_in_idle);
    
    // Property: Config cannot change during locked state
    property p_locked_stable;
      @(posedge clk) disable iff (!rst_n)
      (config_locked) |-> ##1 ($stable(width_select_reg) && $stable(channel_mask_reg));
    endproperty
    assert property (p_locked_stable);
    
    // Property: Valid width modes only
    property p_valid_width_mode;
      @(posedge clk) disable iff (!rst_n)
      (current_state == DONE) |-> 
        (current_width_mode == MODE_X4) || (current_width_mode == MODE_X8);
    endproperty
    assert property (p_valid_width_mode);
  `endif
  
endmodule

//==============================================================================
// End of width_controller.sv
//==============================================================================
