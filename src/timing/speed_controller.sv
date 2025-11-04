//==================================================================================
// Module: speed_controller
// Description: Multi-speed controller for DDR5 RCD
//              Manages different operating speeds and speed transitions
//              Handles timing parameter adjustments for speed changes
//              Supports MT/s adjustments and bus handshake protocols
// Author: Production Implementation
// Date: 2025-11-04
//==================================================================================

module speed_controller #(
  parameter int NUM_SPEED_GRADES = 8,       // Number of supported speed grades (3'h0..3'h7)
  parameter int MAX_FREQ_MHZ = 6400,        // Maximum frequency in MHz (DDR5-6400)
  parameter int MIN_FREQ_MHZ = 3200         // Minimum frequency in MHz (DDR5-3200)
) (
  input  logic                     clk,
  input  logic                     rst_n,
  
  // Configuration
  input  logic [2:0]               cfg_speed_grade,  // Speed grade selection (0-7)
  input  logic                     cfg_enable,       // Enable speed controller
  
  // Timing Parameters Output
  output logic [7:0]               tCK,              // Clock period in ps
  output logic [7:0]               tRCD,             // RAS to CAS delay in cycles
  output logic [7:0]               tRP,              // Precharge time in cycles
  output logic [7:0]               tCL,              // CAS latency in cycles
  
  // Bus Handshake Signals
  output logic                     req_valid,        // Request valid for speed change
  input  logic                     req_ready,        // Ready to accept speed change
  output logic [2:0]               req_speed,        // Requested speed grade
  
  // Status Signals
  output logic                     speed_valid,      // Current speed parameters valid
  output logic [2:0]               current_speed,    // Current speed grade
  output logic [11:0]              current_freq_mts, // Current frequency in MT/s
  output logic                     speed_changing,   // Speed transition in progress
  output logic                     error             // Error indicator
);

  // ========================================================================
  // Internal Signals and Parameters
  // ========================================================================
  
  // Speed grade frequency mapping (MT/s for DDR5)
  localparam int FREQ_TABLE[8] = '{3200, 3600, 4000, 4400, 4800, 5200, 5600, 6400}; // MT/s
  
  // Speed grade timing parameters (in ps for tCK, cycles for tRCD/tRP/tCL)
  localparam logic [7:0] TCK_TABLE[8] = '{
    8'd312,  // DDR5-3200: 312.5ps = 1000/3200
    8'd278,  // DDR5-3600: 277.8ps = 1000/3600
    8'd250,  // DDR5-4000: 250ps = 1000/4000
    8'd227,  // DDR5-4400: 227.3ps = 1000/4400
    8'd208,  // DDR5-4800: 208.3ps = 1000/4800
    8'd192,  // DDR5-5200: 192.3ps = 1000/5200
    8'd179,  // DDR5-5600: 178.6ps = 1000/5600
    8'd156   // DDR5-6400: 156.25ps = 1000/6400
  };
  
  localparam logic [7:0] TRCD_TABLE[8] = '{
    8'd16, 8'd16, 8'd16, 8'd18, 8'd18, 8'd20, 8'd20, 8'd24
  };
  
  localparam logic [7:0] TRP_TABLE[8] = '{
    8'd16, 8'd16, 8'd16, 8'd18, 8'd18, 8'd20, 8'd20, 8'd24
  };
  
  localparam logic [7:0] TCL_TABLE[8] = '{
    8'd28, 8'd28, 8'd32, 8'd32, 8'd36, 8'd40, 8'd44, 8'd52
  };
  
  // ========================================================================
  // State Machine for Speed Transitions
  // ========================================================================
  
  typedef enum logic [2:0] {
    IDLE = 3'h0,
    REQ_PENDING = 3'h1,
    TRANSITION = 3'h2,
    VALIDATION = 3'h3,
    ERROR_STATE = 3'h4
  } speed_ctrl_state_t;
  
  speed_ctrl_state_t current_state, next_state;
  
  // ========================================================================
  // Internal Registers
  // ========================================================================
  
  logic [2:0]   target_speed_grade;
  logic [2:0]   active_speed_grade;
  logic [7:0]   tCK_current;
  logic [7:0]   tRCD_current;
  logic [7:0]   tRP_current;
  logic [7:0]   tCL_current;
  logic [3:0]   transition_counter;
  logic          enable_ff1, enable_ff2;
  logic [2:0]    speed_grade_ff1, speed_grade_ff2;
  logic          error_flag;
  logic [11:0]   freq_mts;
  
  // ========================================================================
  // Input Synchronizers (CDC - Clock Domain Crossing)
  // ========================================================================
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      enable_ff1 <= 1'b0;
      enable_ff2 <= 1'b0;
      speed_grade_ff1 <= 3'h0;
      speed_grade_ff2 <= 3'h0;
    end else begin
      // Double flop synchronization for metastability protection
      enable_ff1 <= cfg_enable;
      enable_ff2 <= enable_ff1;
      speed_grade_ff1 <= cfg_speed_grade;
      speed_grade_ff2 <= speed_grade_ff1;
    end
  end
  
  // ========================================================================
  // Speed Grade Validation Logic
  // ========================================================================
  
  logic speed_grade_valid;
  logic freq_in_range;
  
  always_comb begin
    // Verify speed grade is within supported range
    speed_grade_valid = (speed_grade_ff2 < NUM_SPEED_GRADES) ? 1'b1 : 1'b0;
    
    // Verify frequency is within MIN/MAX bounds
    freq_in_range = (FREQ_TABLE[speed_grade_ff2] >= MIN_FREQ_MHZ) &&
                    (FREQ_TABLE[speed_grade_ff2] <= MAX_FREQ_MHZ);
  end
  
  // ========================================================================
  // State Machine Implementation
  // ========================================================================
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE;
      target_speed_grade <= 3'h0;
      transition_counter <= 4'h0;
      error_flag <= 1'b0;
    end else begin
      current_state <= next_state;
      
      case (current_state)
        IDLE: begin
          transition_counter <= 4'h0;
          error_flag <= 1'b0;
          if (enable_ff2 && (speed_grade_ff2 != active_speed_grade)) begin
            target_speed_grade <= speed_grade_ff2;
          end
        end
        
        REQ_PENDING: begin
          // Wait for ready signal from bus
          // No action required, state machine advances when ready
        end
        
        TRANSITION: begin
          // Count transition cycles (typically 4-8 cycles)
          if (transition_counter < 4'h7) begin
            transition_counter <= transition_counter + 1'b1;
          end else begin
            transition_counter <= 4'h0;
          end
        end
        
        VALIDATION: begin
          // Verify timing parameters loaded correctly
          if (freq_in_range && speed_grade_valid) begin
            active_speed_grade <= target_speed_grade;
            error_flag <= 1'b0;
          end else begin
            error_flag <= 1'b1;
          end
        end
        
        ERROR_STATE: begin
          error_flag <= 1'b1;
          // Wait for reset or new configuration
        end
        
        default: begin
          current_state <= IDLE;
        end
      endcase
    end
  end
  
  // ========================================================================
  // State Machine Next State Logic
  // ========================================================================
  
  always_comb begin
    next_state = current_state;
    
    case (current_state)
      IDLE: begin
        if (enable_ff2 && (speed_grade_ff2 != active_speed_grade)) begin
          if (speed_grade_valid && freq_in_range) begin
            next_state = REQ_PENDING;
          end else begin
            next_state = ERROR_STATE;
          end
        end
      end
      
      REQ_PENDING: begin
        if (req_ready) begin
          next_state = TRANSITION;
        end
      end
      
      TRANSITION: begin
        if (transition_counter == 4'h7) begin
          next_state = VALIDATION;
        end
      end
      
      VALIDATION: begin
        if (freq_in_range && speed_grade_valid) begin
          next_state = IDLE;
        end else begin
          next_state = ERROR_STATE;
        end
      end
      
      ERROR_STATE: begin
        if (!enable_ff2) begin
          next_state = IDLE;
        end
      end
      
      default: begin
        next_state = IDLE;
      end
    endcase
  end
  
  // ========================================================================
  // Timing Parameter Lookup and Output Assignment
  // ========================================================================
  
  always_comb begin
    // Use active speed grade for current timing parameters
    tCK_current = TCK_TABLE[active_speed_grade];
    tRCD_current = TRCD_TABLE[active_speed_grade];
    tRP_current = TRP_TABLE[active_speed_grade];
    tCL_current = TCL_TABLE[active_speed_grade];
    freq_mts = 12'(FREQ_TABLE[active_speed_grade]);
  end
  
  // ========================================================================
  // Output Generation
  // ========================================================================
  
  always_comb begin
    // Request handshake signals
    req_valid = (current_state == REQ_PENDING) ? 1'b1 : 1'b0;
    req_speed = target_speed_grade;
    
    // Speed changing flag
    speed_changing = (current_state == TRANSITION) ? 1'b1 : 1'b0;
    
    // Valid flag when in IDLE or TRANSITION states
    speed_valid = (current_state == IDLE || current_state == VALIDATION) ? 1'b1 : 1'b0;
  end
  
  // Assign output timing parameters
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      tCK <= 8'd312;  // Default to DDR5-3200
      tRCD <= 8'd16;
      tRP <= 8'd16;
      tCL <= 8'd28;
      current_speed <= 3'h0;
      current_freq_mts <= 12'd3200;
      error <= 1'b0;
    end else begin
      tCK <= tCK_current;
      tRCD <= tRCD_current;
      tRP <= tRP_current;
      tCL <= tCL_current;
      current_speed <= active_speed_grade;
      current_freq_mts <= freq_mts;
      error <= error_flag;
    end
  end
  
  // ========================================================================
  // Assertions for Protocol Compliance
  // ========================================================================
  
  // Assert speed grade is valid when enabled
  assert_valid_speed_grade: assert property (
    @(posedge clk) disable iff (!rst_n || !cfg_enable)
    (cfg_speed_grade < NUM_SPEED_GRADES) || 
    (error == 1'b1)
  ) else $warning("Invalid speed grade: %d", cfg_speed_grade);
  
  // Assert handshake protocol
  assert_handshake_protocol: assert property (
    @(posedge clk) disable iff (!rst_n)
    (req_valid && req_ready) |-> ##1 (current_state == TRANSITION)
  ) else $warning("Handshake protocol violation");
  
  // Assert timing parameters stay constant during non-transition
  assert_stable_params: assert property (
    @(posedge clk) disable iff (!rst_n || speed_changing)
    (current_state == IDLE) |-> (tCK == tCK_current)
  ) else $warning("Timing parameters not stable");
  
endmodule
