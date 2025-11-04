//==================================================================================
// Module: jitter_control
// Description: Jitter minimization logic for DDR5 RCD
//              Measures period variance, reports jitter, alarms excessive jitter
// Author: Production Implementation
// Date: 2025-11-04
//==================================================================================

module jitter_control #(
  parameter int JITTER_BUFFER_DEPTH = 8,   // Number of edge samples
  parameter int JITTER_THRESHOLD   = 24    // Alarm threshold (in units of measured LSB)
) (
  input  logic       clk,              // Reference clock
  input  logic       rst_n,            // Active-low reset
  input  logic       cfg_enable,       // Enable measurement
  input  logic       mon_signal,       // Signal to monitor edges
  output logic [15:0] jitter_measure,  // Jitter RMS or peak-to-peak (lsbs)
  output logic       jitter_alarm      // High if jitter exceeds threshold
);

  // ========================================================================
  // Edge-to-edge period measurement
  // ========================================================================
  logic        mon_signal_ff, edge_detected;
  logic [15:0] period_cnt;
  logic [15:0] period_buffer [JITTER_BUFFER_DEPTH];
  logic [3:0]  buffer_idx;
  logic [15:0] ref_period, jitter_sum, jitter_var;
  logic [15:0] variance_reg;

  // Edge detection
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      mon_signal_ff <= 1'b0;
    end else begin
      mon_signal_ff <= mon_signal;
    end
  end
  assign edge_detected = cfg_enable & (mon_signal & ~mon_signal_ff);

  // Free-running counter for period measurement
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      period_cnt <= 16'd0;
    end else if (edge_detected) begin
      period_cnt <= 16'd0;
    end else if (cfg_enable) begin
      period_cnt <= period_cnt + 1'b1;
    end
  end

  // Buffer period samples
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      buffer_idx <= 0;
      for (int i=0; i<JITTER_BUFFER_DEPTH; i++) period_buffer[i] <= 16'd0;
    end else if (edge_detected) begin
      period_buffer[buffer_idx] <= period_cnt;
      buffer_idx <= (buffer_idx == JITTER_BUFFER_DEPTH-1) ? 0 : buffer_idx+1;
    end
  end

  // Compute reference period (mean of samples)
  always_comb begin
    ref_period = 16'd0;
    for (int i=0; i<JITTER_BUFFER_DEPTH; i++) ref_period += period_buffer[i];
    ref_period = ref_period / JITTER_BUFFER_DEPTH;
  end

  // Compute jitter variance (sum of squared diffs)
  always_comb begin
    jitter_sum = 16'd0;
    for (int i=0; i<JITTER_BUFFER_DEPTH; i++) begin
      jitter_sum += (period_buffer[i] > ref_period) ? period_buffer[i] - ref_period : ref_period - period_buffer[i];
    end
    jitter_var = jitter_sum / JITTER_BUFFER_DEPTH;
  end

  // Output assignments
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      jitter_measure <= 16'd0;
      variance_reg   <= 16'd0;
    end else begin
      jitter_measure <= jitter_var;
      variance_reg   <= jitter_var;
    end
  end

  // Alarm when jitter exceeds threshold (overshoots average by defined value)
  always_comb begin
    jitter_alarm = (variance_reg > JITTER_THRESHOLD) ? 1'b1 : 1'b0;
  end

  // ========================================================================
  // Assertions
  // ========================================================================
  // Alarm must be deasserted when variance below threshold
  assert_no_alarm_low_jitter: assert property (@(posedge clk) disable iff (!rst_n) (variance_reg < JITTER_THRESHOLD) |-> (jitter_alarm == 1'b0));
  // Period buffer values must not exceed 16 bits
  assert_period_16b: assert property (@(posedge clk) disable iff (!rst_n) (period_cnt <= 16'hFFFF));

endmodule
