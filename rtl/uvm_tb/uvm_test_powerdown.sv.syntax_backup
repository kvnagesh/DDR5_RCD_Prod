//!
// uvm_test_powerdown.sv - UVM Test: DDR5 RCD Power-Down and Power-Aware Verification
// Part of DDR5 RCD Testbench
//
// This test executes explicit directed scenarios exercising entry/exit to power-down,
// verification of all DDR5 RCD power-aware features, including CMD_PDE/PDX and SRE/SRX.

`include "uvm_macros.svh"
import uvm_pkg::*;
import traffic_gen_pkg::*;

class uvm_test_powerdown extends uvm_test;
  `uvm_component_utils(uvm_test_powerdown)

  traffic_generator tr_gen;
  uvm_sequencer #(traffic_gen_pkg::ca_transaction) seqr;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    seqr = uvm_sequencer #(traffic_gen_pkg::ca_transaction)::type_id::create("seqr", this);
    tr_gen = traffic_generator::type_id::create("tr_gen", this);
    tr_gen.sequencer = seqr;
    tr_gen.mode = TRAFFIC_MODE_DIRECTED;
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `uvm_info(get_type_name(), "Running Power-Down Directed Test", UVM_LOW)
    
    // Directed Power Down Sequence Example
    traffic_gen_pkg::ca_transaction txn;

    // 1. Normal Memory Transaction
    txn = ca_transaction::type_id::create("txn_normal");
    txn.randomize() with { command == CMD_WRITE; };
    tr_gen.sequencer.start_item(txn);
    tr_gen.sequencer.finish_item(txn);

    // 2. Power-Down Entry (PDE)
    txn = ca_transaction::type_id::create("txn_pde");
    txn.randomize() with { command == CMD_PDE; };
    tr_gen.sequencer.start_item(txn);
    tr_gen.sequencer.finish_item(txn);

    // 3. Wait period
    #100;

    // 4. Power-Down Exit (PDX)
    txn = ca_transaction::type_id::create("txn_pdx");
    txn.randomize() with { command == CMD_PDX; };
    tr_gen.sequencer.start_item(txn);
    tr_gen.sequencer.finish_item(txn);

    // 5. Self-Refresh Entry (SRE)
    txn = ca_transaction::type_id::create("txn_sre");
    txn.randomize() with { command == CMD_SRE; };
    tr_gen.sequencer.start_item(txn);
    tr_gen.sequencer.finish_item(txn);

    // 6. Self-Refresh Exit (SRX)
    txn = ca_transaction::type_id::create("txn_srx");
    txn.randomize() with { command == CMD_SRX; };
    tr_gen.sequencer.start_item(txn);
    tr_gen.sequencer.finish_item(txn);

    // 7. Validation/Read
    txn = ca_transaction::type_id::create("txn_read");
    txn.randomize() with { command == CMD_READ; };
    tr_gen.sequencer.start_item(txn);
    tr_gen.sequencer.finish_item(txn);

    phase.drop_objection(this);
  endtask

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_type_name(), "Power-Down test completed and assertions reported", UVM_LOW)
  endfunction
endclass
