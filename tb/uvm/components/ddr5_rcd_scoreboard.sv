//==============================================================================
// File: ddr5_rcd_scoreboard.sv
// Description: UVM Scoreboard Component for DDR5 RCD Verification
// Author: Production Implementation
// Date: 2025-11-04
//==============================================================================
`ifndef DDR5_RCD_SCOREBOARD_SV
`define DDR5_RCD_SCOREBOARD_SV

`include "uvm_macros.svh"
import uvm_pkg::*;

//==============================================================================
// Class: ddr5_rcd_scoreboard
// Description: Scoreboard to compare expected vs actual transactions
//==============================================================================
class ddr5_rcd_scoreboard extends uvm_scoreboard;

  // Factory registration
  `uvm_component_utils(ddr5_rcd_scoreboard)

  // Analysis ports and exports
  uvm_analysis_export #(uvm_sequence_item) expected_export;
  uvm_analysis_export #(uvm_sequence_item) actual_export;

  // Received transaction FIFOs
  uvm_tlm_analysis_fifo #(uvm_sequence_item) expected_fifo;
  uvm_tlm_analysis_fifo #(uvm_sequence_item) actual_fifo;

  // Internal error counters
  int unsigned error_count;
  int unsigned match_count;
  int unsigned total_count;
  int unsigned coverage_sample_count;

  //============================================================================
  // Constructor
  //============================================================================
  function new(string name, uvm_component parent);
    super.new(name, parent);
    expected_export = new("expected_export", this);
    actual_export = new("actual_export", this);
    expected_fifo = new("expected_fifo", this);
    actual_fifo = new("actual_fifo", this);
    error_count = 0;
    match_count = 0;
    total_count = 0;
    coverage_sample_count = 0;
  endfunction

  //============================================================================
  // Build Phase: Connect exports to FIFOs
  //============================================================================
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    expected_export.connect(expected_fifo.analysis_export);
    actual_export.connect(actual_fifo.analysis_export);
  endfunction

  //============================================================================
  // Run Phase: Compare expected and actual transactions
  //============================================================================
  task run_phase(uvm_phase phase);
    uvm_sequence_item expected_item;
    uvm_sequence_item actual_item;
    forever begin
      expected_fifo.get(expected_item);
      actual_fifo.get(actual_item);
      compare_transaction(expected_item, actual_item);
      total_count++;
    end
  endtask

  //============================================================================
  // Comparison Method: Checks fields and signals
  //============================================================================
  function void compare_transaction(uvm_sequence_item expected, uvm_sequence_item actual);
    bit matched = 1;
    string mismatch_msg;
    // Field-by-field comparison
    foreach (expected) begin
      if (expected[i] !== actual[i]) begin
        matched = 0;
        mismatch_msg = $sformatf("Mismatch @ field %s: expected %0h, actual %0h", i, expected[i], actual[i]);
        `uvm_error("SCOREBOARD", mismatch_msg)
        error_count++;
      end
    end
    if (matched) begin
      match_count++;
      `uvm_info("SCOREBOARD", $sformatf("MATCH transaction #%0d", total_count), UVM_MEDIUM)
    end
  endfunction

  //============================================================================
  // Report Phase: Print summary
  //============================================================================
  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info("SCOREBOARD", $sformatf("DDR5 RCD Scoreboard Report:"), UVM_LOW)
    `uvm_info("SCOREBOARD", $sformatf("  Total Compared: %0d", total_count), UVM_LOW)
    `uvm_info("SCOREBOARD", $sformatf("  Matches: %0d", match_count), UVM_LOW)
    `uvm_info("SCOREBOARD", $sformatf("  Errors: %0d", error_count), UVM_LOW)
  endfunction

endclass : ddr5_rcd_scoreboard

`endif // DDR5_RCD_SCOREBOARD_SV
