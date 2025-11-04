//!
// stress_test_env.sv - DDR5 RCD Stress Test Environment
// Part of DDR5 RCD Verification Testbench
//
// Provides stress and max-performance simulation environment, includes traffic bursting,
// race/timing edge-case probing, protocol violation attempt scenarios.

`include "uvm_macros.svh"
import uvm_pkg::*;
import traffic_gen_pkg::*;

class stress_test_env extends uvm_env;
  `uvm_component_utils(stress_test_env)

  traffic_generator str_tr_gen;
  uvm_sequencer #(traffic_gen_pkg::ca_transaction) seqr;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    seqr = uvm_sequencer #(traffic_gen_pkg::ca_transaction)::type_id::create("seqr", this);
    str_tr_gen = traffic_generator::type_id::create("str_tr_gen", this);
    str_tr_gen.sequencer = seqr;
    str_tr_gen.mode = TRAFFIC_MODE_STRESS;
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `uvm_info(get_type_name(), "Running STRESS Environment: Max traffic burst, edge cases, timing stress", UVM_LOW)
    
    // Launch stress pattern sequence
    stress_pattern_sequence str_seq = stress_pattern_sequence::type_id::create("str_seq");
    str_tr_gen.sequencer.start(str_seq);
    
    // Insert race conditions & edge-case scenarios
    repeat(10) begin
      ca_transaction txn = ca_transaction::type_id::create($sformatf("rc_edge_%0d", $time));
      txn.randomize() with { command == ( ($urandom()%2) ? CMD_READ : CMD_WRITE ); };
      fork
        begin
          str_tr_gen.sequencer.start_item(txn);
          str_tr_gen.sequencer.finish_item(txn);
        end
        begin
          #($urandom_range(1, 10)); // Overlap with timing
          str_tr_gen.sequencer.start_item(txn);
          str_tr_gen.sequencer.finish_item(txn);
        end
      join
    end

    // Simulate timing violation attempts (optional)
    // TODO: Optionally inject known timing aggressors here

    phase.drop_objection(this);
  endtask
endclass
