//==============================================================================
// File: ddr5_rcd_coverage.sv
// Description: Functional and Cross Coverage for DDR5 RCD Verification
// Author: Production Implementation
// Date: 2025-11-04
//==============================================================================
`ifndef DDR5_RCD_COVERAGE_SV
`define DDR5_RCD_COVERAGE_SV
`include "uvm_macros.svh"
import uvm_pkg::*;

//==============================================================================
// Class: ddr5_rcd_coverage
// Description: Functional/timing and cross-coverage collector for DDR5 RCD
//==============================================================================
class ddr5_rcd_coverage extends uvm_subscriber #(uvm_sequence_item);

  `uvm_component_utils(ddr5_rcd_coverage)

  // Coverage instances
  covergroup cg_main_transaction;
    option.per_instance = 1;
    // Coverage bins for CA commands
    cmd: coverpoint trans.ca_cmd;
    // Coverage bins for address
    addr: coverpoint trans.ca_addr {
      bins all_addr[] = {[0:131071]}; // 17-bit address
    }
    // Coverage bins for chip select
    cs: coverpoint trans.ca_cs;
    // Coverage bins for CKE and ODT
    cke: coverpoint trans.ca_cke;
    odt: coverpoint trans.ca_odt;
    // Cross coverage example
    cmd_addr_cs: cross cmd, addr, cs;
    // Coverage bins for DQ burst
    dq_valid: coverpoint trans.dq_valid;
    dq_mask: coverpoint trans.dq_mask;
    dq_strobe: coverpoint trans.dq_strobe;
    // Error/Alert status coverage
    parity: coverpoint trans.parity_err;
    alert: coverpoint trans.alert_n;
  endgroup

  // Transaction for coverage sampling
  uvm_sequence_item trans;

  //============================================================================
  // Constructor
  //============================================================================
  function new(string name="ddr5_rcd_coverage", uvm_component parent);
    super.new(name, parent);
    cg_main_transaction = new();
  endfunction

  //============================================================================
  // Coverage Write: Sample transaction in covergroup
  //============================================================================
  function void write(uvm_sequence_item t);
    trans = t;
    cg_main_transaction.sample();
    `uvm_info(get_type_name(), $sformatf("Sampled coverage for transaction"), UVM_LOW)
  endfunction

endclass : ddr5_rcd_coverage

`endif // DDR5_RCD_COVERAGE_SV
