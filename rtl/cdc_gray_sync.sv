//
// cdc_gray_sync.sv
// Clock Domain Crossing (CDC) Synchronizer using Gray Code Logic
// DDR5 RCD Production
//
// Description:
//   Implements synthesizable clock domain crossing synchronizers using gray-coded logic.
//   Features include:
//   - Source-to-destination clock domain transfer
//   - Gray code encoder and decoder
//   - Multi-stage synchronization registers for metastability reduction
//   - Handshake protocol with ready/valid outputs
//   - Support for both narrow and wide bus crossings
//
// Integration Notes:
//   - Use for asynchronous FIFO pointers, command paths, and status signals
//   - Minimum 2-stage synchronizer; 3-4 stages recommended for high-frequency designs
//   - Gray code preferred for pointer synchronization (single-bit transitions)
//

module cdc_gray_sync #(
    parameter int WIDTH = 8,              // Data width (bits)
    parameter int SYNC_STAGES = 3,        // Number of synchronization stages
    parameter bit USE_HANDSHAKE = 1'b0,   // Enable handshake protocol
    parameter bit USE_VALID_READY = 1'b1  // Enable valid/ready signaling
) (
    // Source clock domain
    input  logic                 src_clk,
    input  logic                 src_reset_n,
    input  logic [WIDTH-1:0]     src_data,
    input  logic                 src_valid,
    output logic                 src_ready,
    
    // Destination clock domain
    input  logic                 dst_clk,
    input  logic                 dst_reset_n,
    output logic [WIDTH-1:0]     dst_data,
    output logic                 dst_valid,
    input  logic                 dst_ready,
    
    // Optional handshake signals
    output logic                 src_ack,     // Acknowledge from destination
    input  logic                 dst_req      // Request from source (for handshake)
);

    // Gray code intermediate signals
    logic [WIDTH-1:0]  src_gray;           // Source data in gray code
    logic [WIDTH-1:0]  src_gray_next;      // Next gray code value
    logic [WIDTH-1:0]  dst_gray_sync [0:SYNC_STAGES-1];
    logic [WIDTH-1:0]  dst_gray;           // Synchronized gray code at destination
    logic [WIDTH-1:0]  dst_data_next;      // Decoded data
    
    // Handshake signals
    logic              req_sync [0:SYNC_STAGES-1];
    logic              req_dst;
    logic              req_src_ff, req_src;
    logic              ack_sync [0:SYNC_STAGES-1];
    logic              ack_src;
    logic              ack_dst_ff, ack_dst;
    
    // ======================================================================
    // Gray Code Encoder
    // ======================================================================
    // Convert binary to gray code: Gray = Binary XOR (Binary >> 1)
    function automatic logic [WIDTH-1:0] bin2gray(
        input logic [WIDTH-1:0] bin
    );
        logic [WIDTH-1:0] result;
        for (int i = 0; i < WIDTH; i++) begin
            if (i == WIDTH-1)
                result[i] = bin[i];
            else
                result[i] = bin[i] ^ bin[i+1];
        end
        return result;
    endfunction
    
    // ======================================================================
    // Gray Code Decoder
    // ======================================================================
    // Convert gray code to binary: Binary[MSB] = Gray[MSB]
    //                              Binary[i] = Binary[i+1] XOR Gray[i]
    function automatic logic [WIDTH-1:0] gray2bin(
        input logic [WIDTH-1:0] gray
    );
        logic [WIDTH-1:0] result;
        result[WIDTH-1] = gray[WIDTH-1];
        for (int i = WIDTH-2; i >= 0; i--) begin
            result[i] = result[i+1] ^ gray[i];
        end
        return result;
    endfunction
    
    // ======================================================================
    // SOURCE CLOCK DOMAIN (SRC_CLK)
    // ======================================================================
    always_ff @(posedge src_clk or negedge src_reset_n) begin
        if (!src_reset_n) begin
            src_gray <= '0;
            req_src_ff <= 1'b0;
            ack_src <= 1'b0;
        end
        else begin
            // Capture source data when valid and ready
            if (src_valid && src_ready) begin
                src_gray <= bin2gray(src_data);
                if (USE_HANDSHAKE)
                    req_src_ff <= ~req_src_ff;  // Toggle request
            end
            
            // Synchronize ACK from destination
            ack_src <= ack_sync[SYNC_STAGES-1];
        end
    end
    
    // Source ready logic
    generate
        if (USE_HANDSHAKE) begin : gen_handshake_ready
            // In handshake mode, ready when ACK matches REQ
            assign src_ready = (req_src_ff == ack_src);
        end
        else begin : gen_always_ready
            // Always ready when not in handshake mode
            assign src_ready = 1'b1;
        end
    endgenerate
    
    assign src_ack = ack_src;
    
    // ======================================================================
    // CDC SYNCHRONIZER STAGES (SRC_CLK -> DST_CLK)
    // ======================================================================
    always_ff @(posedge dst_clk or negedge dst_reset_n) begin
        if (!dst_reset_n) begin
            for (int i = 0; i < SYNC_STAGES; i++) begin
                dst_gray_sync[i] <= '0;
            end
        end
        else begin
            dst_gray_sync[0] <= src_gray;           // First stage: capture from source
            for (int i = 1; i < SYNC_STAGES; i++) begin
                dst_gray_sync[i] <= dst_gray_sync[i-1];  // Subsequent stages: pipeline
            end
        end
    end
    
    assign dst_gray = dst_gray_sync[SYNC_STAGES-1];
    assign dst_data_next = gray2bin(dst_gray);
    
    // ======================================================================
    // DESTINATION CLOCK DOMAIN (DST_CLK)
    // ======================================================================
    always_ff @(posedge dst_clk or negedge dst_reset_n) begin
        if (!dst_reset_n) begin
            dst_data <= '0;
            dst_valid <= 1'b0;
            ack_dst_ff <= 1'b0;
        end
        else begin
            // Update destination data and validity
            if (USE_VALID_READY && dst_ready) begin
                dst_data <= dst_data_next;
                dst_valid <= 1'b1;
            end
            else if (!USE_VALID_READY) begin
                dst_data <= dst_data_next;
                dst_valid <= 1'b1;
            end
            
            if (USE_HANDSHAKE) begin
                // Synchronize request from source
                req_dst <= req_sync[SYNC_STAGES-1];
                
                // Toggle acknowledge when request changes
                if (req_dst != req_src_ff)
                    ack_dst_ff <= ~ack_dst_ff;
            end
        end
    end
    
    // ======================================================================
    // HANDSHAKE CDC SYNCHRONIZER STAGES (DST_CLK -> SRC_CLK)
    // ======================================================================
    always_ff @(posedge dst_clk or negedge dst_reset_n) begin
        if (!dst_reset_n) begin
            for (int i = 0; i < SYNC_STAGES; i++) begin
                req_sync[i] <= '0;
            end
        end
        else begin
            req_sync[0] <= dst_req;              // Capture request from source
            for (int i = 1; i < SYNC_STAGES; i++) begin
                req_sync[i] <= req_sync[i-1];    // Pipeline stages
            end
        end
    end
    
    always_ff @(posedge src_clk or negedge src_reset_n) begin
        if (!src_reset_n) begin
            for (int i = 0; i < SYNC_STAGES; i++) begin
                ack_sync[i] <= '0;
            end
        end
        else begin
            ack_sync[0] <= ack_dst_ff;           // Capture acknowledge from destination
            for (int i = 1; i < SYNC_STAGES; i++) begin
                ack_sync[i] <= ack_sync[i-1];    // Pipeline stages
            end
        end
    end
    
endmodule

// ========================================================================
// MODULE: cdc_gray_sync_wrapper
// Purpose: Wrapper for integrating CDC synchronizers in DDR5 RCD paths
// ========================================================================
module cdc_gray_sync_wrapper #(
    parameter int DATA_WIDTH = 8,
    parameter int SYNC_DEPTH = 3,
    parameter string SYNC_MODE = "GRAY"  // "GRAY" or "BINARY"
) (
    // Source interface
    input  logic                    src_clk,
    input  logic                    src_rst_n,
    input  logic [DATA_WIDTH-1:0]   src_data,
    input  logic                    src_data_valid,
    output logic                    src_data_ready,
    
    // Destination interface
    input  logic                    dst_clk,
    input  logic                    dst_rst_n,
    output logic [DATA_WIDTH-1:0]   dst_data,
    output logic                    dst_data_valid,
    input  logic                    dst_data_ready
);
    
    cdc_gray_sync #(
        .WIDTH(DATA_WIDTH),
        .SYNC_STAGES(SYNC_DEPTH),
        .USE_HANDSHAKE(1'b0),
        .USE_VALID_READY(1'b1)
    ) gray_sync_inst (
        .src_clk(src_clk),
        .src_reset_n(src_rst_n),
        .src_data(src_data),
        .src_valid(src_data_valid),
        .src_ready(src_data_ready),
        .dst_clk(dst_clk),
        .dst_reset_n(dst_rst_n),
        .dst_data(dst_data),
        .dst_valid(dst_data_valid),
        .dst_ready(dst_data_ready),
        .src_ack(),
        .dst_req(1'b0)
    );
    
endmodule
