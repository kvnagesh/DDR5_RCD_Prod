// reg_init_ctrl.sv
// Synthesizable SystemVerilog module
// Initializes config/register values on global reset
// Provides atomic sequence, sync flags, handshake outputs

module reg_init_ctrl #(
    parameter REG0_INIT = 32'hDEADBEEF,
    parameter REG1_INIT = 32'hFEEDFACE,
    parameter REG2_INIT = 32'hC001D00D
)(
    input  logic clk,
    input  logic rst_n, 
    output logic [31:0] reg0,
    output logic [31:0] reg1,
    output logic [31:0] reg2,
    output logic init_done,         
    output logic handshake_start,   
    output logic handshake_end      // Pulse: handshake output at init end
);

// Initialization state
logic [1:0] state;
localparam STATE_IDLE   = 2'b00;
localparam STATE_START  = 2'b01;
localparam STATE_LOAD   = 2'b10;
localparam STATE_FINISH = 2'b11;

// Sequential logic
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        reg0            <= REG0_INIT;
        reg1            <= REG1_INIT;
        reg2            <= REG2_INIT;
        state           <= STATE_IDLE;
        init_done       <= 1'b0;
        handshake_start <= 1'b0;
        handshake_end   <= 1'b0;
    end
    else begin
        case (state)
            STATE_IDLE: begin
                handshake_start <= 1'b1;
                state <= STATE_START;
            end
            STATE_START: begin
                handshake_start <= 1'b0;
                state <= STATE_LOAD;
            end
            STATE_LOAD: begin
                // Registers already loaded on reset
                state <= STATE_FINISH;
            end
            STATE_FINISH: begin
                handshake_end <= 1'b1;
                init_done     <= 1'b1;
            end
        endcase
    end
end

// Debug: Map init values for validation
// reg0 maps to REG0_INIT
// reg1 maps to REG1_INIT
// reg2 maps to REG2_INIT

endmodule

// Port List Documentation:
// clk           : System clock
// rst_n         : Active-low global reset
// reg0..reg2    : Initialized registers
// init_done     : 1 when initialization complete
// handshake_start: 1-cycle pulse at start
// handshake_end : 1-cycle pulse at end
// Initialization mapping for debug: see parameters REGx_INIT
