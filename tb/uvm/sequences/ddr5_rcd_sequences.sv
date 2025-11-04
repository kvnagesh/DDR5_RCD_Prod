//==============================================================================
// File: ddr5_rcd_sequences.sv
// Description: Comprehensive Randomized Sequence Generator for DDR5 RCD Verification
// Author: Production Implementation
// Date: 2025-11-04
//==============================================================================
`ifndef DDR5_RCD_SEQUENCES_SV
`define DDR5_RCD_SEQUENCES_SV
`include "uvm_macros.svh"
import uvm_pkg::*;

//==============================================================================
// Base Transaction Sequence Item for DDR5 RCD
//==============================================================================
class ddr5_rcd_sequence_item extends uvm_sequence_item;
  rand bit [6:0]   ca_cmd;
  rand bit [16:0]  ca_addr;
  rand bit [1:0]   ca_cs;
  rand bit         ca_cke;
  rand bit         ca_odt;
  rand bit [127:0] dq_data;
  rand bit [15:0]  dq_mask;
  rand bit         dq_strobe;
  rand bit         parity_err;
  rand bit         alert_n;

  constraint valid_cmd { ca_cmd inside {[0:127]}; }
  constraint valid_addr { ca_addr inside {[0:131071]}; }

  `uvm_object_utils(ddr5_rcd_sequence_item)
  function new(string name = "ddr5_rcd_sequence_item"); super.new(name); endfunction
endclass : ddr5_rcd_sequence_item

//==============================================================================
// Sequence: DDR5 RCD Random Transaction Sequence
//==============================================================================
class ddr5_rcd_random_sequence extends uvm_sequence#(ddr5_rcd_sequence_item);
  `uvm_object_utils(ddr5_rcd_random_sequence)

  int trans_count = 100; // Default number of transactions

  function new(string name = "ddr5_rcd_random_sequence"); super.new(name); endfunction

  virtual task body();
    ddr5_rcd_sequence_item req;
    repeat (trans_count) begin
      req = ddr5_rcd_sequence_item::type_id::create("req");
      if (!req.randomize()) `uvm_error(get_name(), "Randomization failed")
      start_item(req);
      finish_item(req);
      `uvm_info(get_type_name(), $sformatf("Sent transaction:
  CMD=%0h ADDR=%0h CS=%0h CKE=%0b ODT=%0b DQ_DATA=%0h DQ_MASK=%0h DQ_STROBE=%0b", req.ca_cmd, req.ca_addr, req.ca_cs, req.ca_cke, req.ca_odt, req.dq_data, req.dq_mask, req.dq_strobe), UVM_MEDIUM)
    end
  endtask
endclass : ddr5_rcd_random_sequence

//==============================================================================
// Virtual Sequence for Corner and Directed Cases
//==============================================================================
class ddr5_rcd_virtual_sequence extends uvm_sequence#(uvm_sequence_item);
  `uvm_object_utils(ddr5_rcd_virtual_sequence)

  ddr5_rcd_random_sequence rand_seq;

  function new(string name = "ddr5_rcd_virtual_sequence"); super.new(name); endfunction

  virtual task body();
    // Example: Run random followed by directed sequences
    rand_seq = ddr5_rcd_random_sequence::type_id::create("rand_seq");
    rand_seq.trans_count = 200;
    rand_seq.start(null);
    // Add more directed/corner cases here
    `uvm_info(get_type_name(), "Completed virtual sequence", UVM_LOW)
  endtask
endclass : ddr5_rcd_virtual_sequence

`endif // DDR5_RCD_SEQUENCES_SV
