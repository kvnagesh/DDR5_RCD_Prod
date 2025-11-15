//============================================================================
// Module: reset_controller
// Description: Reset Controller for I3C Slave
//              Manages reset sequencing and synchronization for I3C slave
//              controller and associated modules
//============================================================================
module reset_controller (
    // Clock Inputs
    input  logic        clk,           
    input  logic        i3c_clk,       

    // Reset Inputs
    input  logic        por_n,         
    input  logic        sys_rst_n,     
    input  logic        sw_rst,        
    input  logic        i3c_rst_req,   

    // Reset Outputs
    output logic        rst_n,         
    output logic        i3c_rst_n,     
    output logic        reg_rst_n,     
    output logic        async_rst_n,   

    // Status Outputs
    output logic        reset_active,  
    output logic [2:0]  reset_source,  
    output logic        reset_done     // Indicates reset is complete
);

    //========================================================================
    // Reset Source Encoding
    //========================================================================
    localparam RST_SRC_NONE     = 3'b000;
    localparam RST_SRC_POR      = 3'b001;  // Power-On Reset
    localparam RST_SRC_SYSTEM   = 3'b010;  // System Reset
    localparam RST_SRC_SOFTWARE = 3'b011;  // Software Reset
    localparam RST_SRC_I3C      = 3'b100;  // I3C Bus Reset

    //========================================================================
    // Reset Sequencing Parameters
    //========================================================================
    localparam RESET_HOLD_CYCLES    = 16;   // Minimum reset assertion cycles
    localparam RELEASE_DELAY_CYCLES = 8;    // Cycles between sequential release
    localparam SYNC_STAGES          = 3;    // Reset synchronizer stages

    //========================================================================
    // Debounce Parameters (Synthesizable)
    //========================================================================
    localparam DEBOUNCE_CYCLES      = 8;    // Debounce time in clock cycles
    localparam DEBOUNCE_WIDTH       = $clog2(DEBOUNCE_CYCLES + 1);

    //========================================================================
    // Internal Signals & FSM Declaration
    //========================================================================
    typedef enum logic [1:0] {
        RESET_IDLE,        
        RESET_ASSERT,      
        RESET_HOLD,        
        RESET_SEQ_RELEASE  // Sequentially releasing resets
    } reset_state_t;

    reset_state_t reset_state, reset_state_next;
    logic [4:0] reset_counter;  // Counter for assertion/hold/release
    logic reset_req;
    logic [2:0] reset_source_reg, reset_source_next;

    // Synchronizers
    logic [SYNC_STAGES-1:0] rst_sync;
    logic [SYNC_STAGES-1:0] i3c_rst_sync;

    // Debounce logic
    logic [DEBOUNCE_WIDTH-1:0] sw_rst_debounce_cnt, i3c_rst_debounce_cnt;
    logic sw_rst_r, sw_rst_rr, sw_rst_debounced;
    logic i3c_rst_req_r, i3c_rst_req_rr, i3c_rst_req_debounced;

    // Internal outputs for controlled reset assertion
    logic rst_n_int, i3c_rst_n_int, reg_rst_n_int;
    logic async_rst_n_int;
    
    //========================================================================
    // Debouncing: Synchronize and Filter Glitchy/Async Inputs
    //========================================================================
    always_ff @(posedge clk or negedge por_n) begin
        if (!por_n) begin
            sw_rst_r  <= 1'b0;
            sw_rst_rr <= 1'b0;
            sw_rst_debounce_cnt <= '0;
            sw_rst_debounced <= 1'b0;
        end else begin
            sw_rst_r  <= sw_rst;
            sw_rst_rr <= sw_rst_r;
            if (sw_rst_rr) begin
                if (sw_rst_debounce_cnt < DEBOUNCE_CYCLES)
                    sw_rst_debounce_cnt <= sw_rst_debounce_cnt + 1'b1;
                else
                    sw_rst_debounced <= 1'b1;
            end else begin
                sw_rst_debounce_cnt <= '0;
                sw_rst_debounced <= 1'b0;
            end
        end
    end
    always_ff @(posedge clk or negedge por_n) begin
        if (!por_n) begin
            i3c_rst_req_r  <= 1'b0;
            i3c_rst_req_rr <= 1'b0;
            i3c_rst_debounce_cnt <= '0;
            i3c_rst_req_debounced <= 1'b0;
        end else begin
            i3c_rst_req_r  <= i3c_rst_req;
            i3c_rst_req_rr <= i3c_rst_req_r;
            if (i3c_rst_req_rr) begin
                if (i3c_rst_debounce_cnt < DEBOUNCE_CYCLES)
                    i3c_rst_debounce_cnt <= i3c_rst_debounce_cnt + 1'b1;
                else
                    i3c_rst_req_debounced <= 1'b1;
            end else begin
                i3c_rst_debounce_cnt <= '0;
                i3c_rst_req_debounced <= 1'b0;
            end
        end
    end

    //========================================================================
    // Consolidate Reset Requests (Priority: POR > SYS > SW > I3C)
    //========================================================================
    always_comb begin
        reset_req = 1'b0;
        reset_source_next = RST_SRC_NONE;
        if (!por_n) begin
            reset_req = 1'b1; reset_source_next = RST_SRC_POR;
        end else if (!sys_rst_n) begin
            reset_req = 1'b1; reset_source_next = RST_SRC_SYSTEM;
        end else if (sw_rst_debounced) begin
            reset_req = 1'b1; reset_source_next = RST_SRC_SOFTWARE;
        end else if (i3c_rst_req_debounced) begin
            reset_req = 1'b1; reset_source_next = RST_SRC_I3C;
        end
    end

    //========================================================================
    // FSM: Reset Assertion, Hold, and Sequenced Release
    //========================================================================
    always_ff @(posedge clk or negedge por_n) begin
        if (!por_n) begin
            reset_state     <= RESET_IDLE;
            reset_state_next<= RESET_IDLE;
            reset_counter   <= 0;
            reset_source_reg<= RST_SRC_POR;
        end else if (!sys_rst_n) begin
            reset_state     <= RESET_IDLE;
            reset_state_next<= RESET_IDLE;
            reset_counter   <= 0;
            reset_source_reg<= RST_SRC_SYSTEM;
        end else begin
            reset_state <= reset_state_next;
            if (reset_req && (reset_state == RESET_IDLE)) begin
                reset_source_reg <= reset_source_next;
            end
            // Reset the counter when transitioning to new phase
            if (reset_state != reset_state_next)
                reset_counter <= 0;
            else if ((reset_state == RESET_HOLD) || (reset_state == RESET_SEQ_RELEASE))
                reset_counter <= reset_counter + 1;
        end
    end

    always_comb begin
        reset_state_next = reset_state;
        case (reset_state)
            RESET_IDLE: begin
                if (reset_req)
                    reset_state_next = RESET_ASSERT;
            end
            RESET_ASSERT: begin
                reset_state_next = RESET_HOLD;
            end
            RESET_HOLD: begin
                if (reset_counter >= RESET_HOLD_CYCLES-1)
                    reset_state_next = RESET_SEQ_RELEASE;
            end
            RESET_SEQ_RELEASE: begin
                if (reset_counter >= RELEASE_DELAY_CYCLES-1)
                    reset_state_next = RESET_IDLE;
            end
        endcase
    end

    //========================================================================
    // Reset Output Assertion Logic (Main/Reg/I3C/Async)
    //========================================================================
    always_comb begin
        // Default: all resets de-asserted
        rst_n_int      = 1'b1;
        i3c_rst_n_int  = 1'b1;
        reg_rst_n_int  = 1'b1;
        async_rst_n_int= por_n & sys_rst_n;
        reset_active   = 1'b0;
        reset_done     = 1'b1;

        case (reset_state)
            RESET_ASSERT: begin
                rst_n_int      = 1'b0; // Assert all resets
                i3c_rst_n_int  = 1'b0;
                reg_rst_n_int  = 1'b0;
                reset_active   = 1'b1;
                reset_done     = 1'b0;
            end
            RESET_HOLD: begin
                rst_n_int      = 1'b0;
                i3c_rst_n_int  = 1'b0;
                reg_rst_n_int  = 1'b0;
                reset_active   = 1'b1;
                reset_done     = 1'b0;
            end
            RESET_SEQ_RELEASE: begin
                rst_n_int      = 1'b1; // Release main/reset first
                reg_rst_n_int  = 1'b1;
                i3c_rst_n_int  = (reset_counter < (RELEASE_DELAY_CYCLES/2)) ? 1'b0 : 1'b1;
                reset_active   = 1'b1;
                reset_done     = 1'b0;
            end
            default: begin
                // Resets deasserted, outputs reflect synchronizers
                reset_active = 1'b0;
                reset_done = 1'b1;
            end
        endcase
    end

    //========================================================================
    // Reset Synchronizers
    //========================================================================
    always_ff @(posedge clk or negedge por_n) begin
        if (!por_n)
            rst_sync <= '0;
        else if (!rst_n_int)
            rst_sync <= '0;
        else
            rst_sync <= {rst_sync[SYNC_STAGES-2:0], 1'b1};
    end
    always_ff @(posedge i3c_clk or negedge por_n) begin
        if (!por_n)
            i3c_rst_sync <= '0;
        else if (!i3c_rst_n_int)
            i3c_rst_sync <= '0;
        else
            i3c_rst_sync <= {i3c_rst_sync[SYNC_STAGES-2:0], 1'b1};
    end

    // Assign output signals
    assign rst_n       = rst_sync[SYNC_STAGES-1];
    assign i3c_rst_n   = i3c_rst_sync[SYNC_STAGES-1];
    assign reg_rst_n   = rst_sync[SYNC_STAGES-1];
    assign async_rst_n = async_rst_n_int;
    assign reset_source= reset_source_reg;

endmodule

// ---------------------------------------------------------------------
// FSM States:
//   - RESET_IDLE:    Await a consolidated reset event.
//   - RESET_ASSERT:  Immediately assert all output resets.
//   - RESET_HOLD:    Hold resets for RESET_HOLD_CYCLES.
//   - RESET_SEQ_RELEASE: Sequential release (main+reg first, then i3c).
//
// All resets are passed through synchronizers for clock domain safety.
// Inputs are debounced & synchronized where appropriate.
// ---------------------------------------------------------------------
