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
  constraint valid_cmd { ca_cmd inside {[0:127]}; } // All legal commands
  constraint valid_addr { ca_addr inside {[0:131071]}; } // All legal addresses
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
      if (!req.randomize())
        `uvm_error(get_name(), "Randomization failed")
      start_item(req);
      finish_item(req);
      `uvm_info(get_type_name(), $sformatf("Sent transaction: CMD=%0h ADDR=%0h CS=%0h CKE=%0b ODT=%0b DQ_DATA=%0h DQ_MASK=%0h DQ_STROBE=%0b", req.ca_cmd, req.ca_addr, req.ca_cs, req.ca_cke, req.ca_odt, req.dq_data, req.dq_mask, req.dq_strobe), UVM_MEDIUM)
    end
  endtask
endclass : ddr5_rcd_random_sequence
//==============================================================================
// Sequence: DDR5 RCD Burst Transaction Sequence
// This sequence generates bursts of transactions with customizable burst length.
//==============================================================================
class ddr5_rcd_burst_sequence extends uvm_sequence#(ddr5_rcd_sequence_item);
  `uvm_object_utils(ddr5_rcd_burst_sequence)
  int burst_length = 8; // Default burst length
  function new(string name = "ddr5_rcd_burst_sequence"); super.new(name); endfunction
  virtual task body();
    ddr5_rcd_sequence_item req;
    for (int i = 0; i < burst_length; i++) begin
      req = ddr5_rcd_sequence_item::type_id::create($sformatf("burst_req_%0d", i));
      // Protocol-specific constraints for burst (e.g. sequential addresses, READ/WRITE)
      req.ca_cmd = (i % 2 == 0) ? 8 : 0; // Example: alternate READ (8) and WRITE (0) commands
      req.ca_addr = 1024 + i; // Example: burst incremented addressing
      assert(req.randomize() with {ca_cs == 0; ca_cke == 1;}) else `uvm_error(get_name(), "Burst randomization failed")
      start_item(req);
      finish_item(req);
      `uvm_info(get_type_name(), $sformatf("Burst transaction %0d: CMD=%0h ADDR=%0h", i, req.ca_cmd, req.ca_addr), UVM_LOW)
    end
  endtask
endclass : ddr5_rcd_burst_sequence
//==============================================================================
// Sequence: DDR5 RCD Protocol Command Sequence
// Generates protocol-defined command sequences (e.g. ACTIVATE-PRECHARGE-READ-WRITE-REFRESH)
//==============================================================================
class ddr5_rcd_protocol_sequence extends uvm_sequence#(ddr5_rcd_sequence_item);
  `uvm_object_utils(ddr5_rcd_protocol_sequence)
  int seq_length = 5;
  function new(string name = "ddr5_rcd_protocol_sequence"); super.new(name); endfunction
  virtual task body();
    ddr5_rcd_sequence_item req;
    bit [6:0] protocol_cmds [5] = '{1, 4, 8, 0, 32}; // ACT(1), PRE(4), READ(8), WRITE(0), REFRESH(32)
    for (int i = 0; i < seq_length; i++) begin
      req = ddr5_rcd_sequence_item::type_id::create($sformatf("protocol_req_%0d", i));
      req.ca_cmd = protocol_cmds[i % protocol_cmds.size()];
      req.ca_addr = 2048 + i*64;
      assert(req.randomize() with {ca_cs == 1; ca_cke == 1;}) else `uvm_error(get_name(), "Protocol command randomization failed")
      start_item(req);
      finish_item(req);
      `uvm_info(get_type_name(), $sformatf("Protocol command %0d: CMD=%0h ADDR=%0h", i, req.ca_cmd, req.ca_addr), UVM_LOW)
    end
  endtask
endclass : ddr5_rcd_protocol_sequence
//==============================================================================
// Sequence: DDR5 RCD Error Injection Sequence
// This sequence injects various types of errors for robustness verification
//==============================================================================
class ddr5_rcd_error_injection_sequence extends uvm_sequence#(ddr5_rcd_sequence_item);
  `uvm_object_utils(ddr5_rcd_error_injection_sequence)
  int error_count = 10; // Default number of errors injected
  function new(string name = "ddr5_rcd_error_injection_sequence"); super.new(name); endfunction
  virtual task body();
    ddr5_rcd_sequence_item req;
    for (int i = 0; i < error_count; i++) begin
      req = ddr5_rcd_sequence_item::type_id::create($sformatf("err_req_%0d", i));
      assert(req.randomize()) else `uvm_error(get_name(), "Error item randomization failed")
      // Parity error injection
      req.parity_err = (i % 2 == 0);
      // Alert_n signal toggling for error notification
      req.alert_n = (i % 3 == 0);
      // Illegal command injection on certain iterations
      if (i == error_count-1) req.ca_cmd = 127; // illegal
      start_item(req);
      finish_item(req);
      `uvm_info(get_type_name(), $sformatf("Error injection %0d: CMD=%0h ALERT_N=%0b PARITY_ERR=%0b", i, req.ca_cmd, req.alert_n, req.parity_err), UVM_HIGH)
    end
  endtask
endclass : ddr5_rcd_error_injection_sequence
//==============================================================================
// Virtual Sequence for Corner and Directed Cases
//==============================================================================
class ddr5_rcd_virtual_sequence extends uvm_sequence#(uvm_sequence_item);
  `uvm_object_utils(ddr5_rcd_virtual_sequence)
  ddr5_rcd_random_sequence rand_seq;
  ddr5_rcd_burst_sequence burst_seq;
  ddr5_rcd_protocol_sequence proto_seq;
  ddr5_rcd_error_injection_sequence err_seq;
  function new(string name = "ddr5_rcd_virtual_sequence"); super.new(name); endfunction
  virtual task body();
    rand_seq = ddr5_rcd_random_sequence::type_id::create("rand_seq");
    rand_seq.trans_count = 200;
    rand_seq.start(null);
    burst_seq = ddr5_rcd_burst_sequence::type_id::create("burst_seq");
    burst_seq.burst_length = 16;
    burst_seq.start(null);
    proto_seq = ddr5_rcd_protocol_sequence::type_id::create("proto_seq");
    proto_seq.seq_length = 5;
    proto_seq.start(null);
    err_seq = ddr5_rcd_error_injection_sequence::type_id::create("err_seq");
    err_seq.error_count = 12;
    err_seq.start(null);
    `uvm_info(get_type_name(), "Completed virtual sequence", UVM_LOW)
  endtask
endclass : ddr5_rcd_virtual_sequence
`endif
// DDR5_RCD_SEQUENCES_SV
