//==============================================================================
// File: ddr5_rcd_coverage.sv
// Description: Functional Coverage Model for DDR5 RCD Verification
// Author: Auto-generated skeleton
// Date: 2025-11-04
//==============================================================================

`ifndef DDR5_RCD_COVERAGE_SV
`define DDR5_RCD_COVERAGE_SV

// Include UVM macros and base library
`include "uvm_macros.svh"
import uvm_pkg::*;

//==============================================================================
// Class: ddr5_rcd_coverage
// Description: Coverage subscriber to collect functional coverage
//==============================================================================
class ddr5_rcd_coverage extends uvm_subscriber #(uvm_sequence_item);
  
  // UVM Factory Registration
  `uvm_component_utils(ddr5_rcd_coverage)

  //============================================================================
  // Coverage Configuration Parameters
  //============================================================================
  bit enable_coverage = 1;           // Enable/disable coverage collection
  bit enable_address_coverage = 1;   // Enable address coverage
  bit enable_command_coverage = 1;   // Enable command coverage
  bit enable_timing_coverage = 1;    // Enable timing coverage
  bit enable_cross_coverage = 1;     // Enable cross coverage

  //============================================================================
  // Transaction Fields for Coverage Sampling
  //============================================================================
  // TODO: Define transaction fields to be sampled
  // These should match the actual transaction type
  logic [15:0] address;
  logic [7:0]  command;
  logic [31:0] data;
  logic        read_write;
  logic [3:0]  rank;
  logic [2:0]  bank_group;
  logic [1:0]  bank;
  
  //============================================================================
  // Coverage Group: Command Coverage
  // Description: Cover all DDR5 commands and their combinations
  //============================================================================
  covergroup command_coverage;
    option.per_instance = 1;
    option.name = "command_coverage";
    
    // Command type coverage
    cp_command: coverpoint command {
      bins cmd_activate    = {8'h00};
      bins cmd_precharge   = {8'h01};
      bins cmd_read        = {8'h02};
      bins cmd_write       = {8'h03};
      bins cmd_refresh     = {8'h04};
      bins cmd_mrs         = {8'h05};
      bins cmd_zqcal       = {8'h06};
      // TODO: Add more command bins
      bins cmd_other       = default;
    }
    
    // Read/Write direction coverage
    cp_read_write: coverpoint read_write {
      bins read  = {0};
      bins write = {1};
    }
    
    // Command and direction cross coverage
    cross_cmd_rw: cross cp_command, cp_read_write {
      // Only valid combinations
      ignore_bins invalid_cmd = binsof(cp_command.cmd_refresh) || 
                                 binsof(cp_command.cmd_zqcal);
    }
  endgroup

  //============================================================================
  // Coverage Group: Address Coverage
  // Description: Cover address space and boundary conditions
  //============================================================================
  covergroup address_coverage;
    option.per_instance = 1;
    option.name = "address_coverage";
    
    // Row address coverage
    cp_address: coverpoint address {
      bins addr_min       = {16'h0000};
      bins addr_low       = {[16'h0001:16'h3FFF]};
      bins addr_mid       = {[16'h4000:16'hBFFF]};
      bins addr_high      = {[16'hC000:16'hFFFE]};
      bins addr_max       = {16'hFFFF};
    }
    
    // Bank group coverage
    cp_bank_group: coverpoint bank_group {
      bins bg0 = {0};
      bins bg1 = {1};
      bins bg2 = {2};
      bins bg3 = {3};
      bins bg4 = {4};
      bins bg5 = {5};
      bins bg6 = {6};
      bins bg7 = {7};
    }
    
    // Bank coverage
    cp_bank: coverpoint bank {
      bins bank0 = {0};
      bins bank1 = {1};
      bins bank2 = {2};
      bins bank3 = {3};
    }
    
    // Rank coverage
    cp_rank: coverpoint rank {
      bins rank0 = {0};
      bins rank1 = {1};
      bins rank2 = {2};
      bins rank3 = {3};
      // TODO: Add more ranks if needed
    }
    
    // Cross coverage: Bank Group x Bank
    cross_bg_bank: cross cp_bank_group, cp_bank;
    
    // Cross coverage: Rank x Bank Group
    cross_rank_bg: cross cp_rank, cp_bank_group;
  endgroup

  //============================================================================
  // Coverage Group: Data Pattern Coverage
  // Description: Cover various data patterns
  //============================================================================
  covergroup data_pattern_coverage;
    option.per_instance = 1;
    option.name = "data_pattern_coverage";
    
    // Data patterns
    cp_data: coverpoint data {
      bins data_all_zeros  = {32'h00000000};
      bins data_all_ones   = {32'hFFFFFFFF};
      bins data_walking_1  = {32'h00000001, 32'h00000002, 32'h00000004, 
                              32'h00000008, 32'h00000010, 32'h00000020};
      bins data_walking_0  = {32'hFFFFFFFE, 32'hFFFFFFFD, 32'hFFFFFFFB};
      bins data_alternating = {32'hAAAAAAAA, 32'h55555555};
      bins data_random     = default;
    }
  endgroup

  //============================================================================
  // Coverage Group: Timing Coverage
  // Description: Cover timing-related scenarios
  //============================================================================
  covergroup timing_coverage;
    option.per_instance = 1;
    option.name = "timing_coverage";
    
    // TODO: Add timing-related coverpoints
    // Example:
    // cp_tRCD: coverpoint tRCD_value {
    //   bins min_timing = {MIN_TRCD};
    //   bins typ_timing = {[MIN_TRCD+1:TYP_TRCD]};
    //   bins max_timing = {[TYP_TRCD+1:MAX_TRCD]};
    // }
  endgroup

  //============================================================================
  // Coverage Group: Protocol Coverage
  // Description: Cover DDR5 protocol sequences
  //============================================================================
  covergroup protocol_coverage;
    option.per_instance = 1;
    option.name = "protocol_coverage";
    
    // TODO: Add protocol sequence coverage
    // Example:
    // cp_activate_read_seq: coverpoint command_sequence {
    //   bins act_read = (ACTIVATE => READ);
    //   bins act_write = (ACTIVATE => WRITE);
    //   bins act_pre = (ACTIVATE => PRECHARGE);
    // }
  endgroup

  //============================================================================
  // Coverage Group: Error Injection Coverage
  // Description: Cover error scenarios
  //============================================================================
  covergroup error_coverage;
    option.per_instance = 1;
    option.name = "error_coverage";
    
    // TODO: Add error scenario coverage
    // Example:
    // cp_ecc_errors: coverpoint ecc_error_type {
    //   bins no_error = {0};
    //   bins single_bit_error = {1};
    //   bins double_bit_error = {2};
    //   bins multi_bit_error = {[3:7]};
    // }
  endgroup

  //============================================================================
  // Constructor
  //============================================================================
  function new(string name = "ddr5_rcd_coverage", uvm_component parent = null);
    super.new(name, parent);
    
    // Instantiate coverage groups
    if (enable_coverage) begin
      command_coverage = new();
      address_coverage = new();
      data_pattern_coverage = new();
      timing_coverage = new();
      protocol_coverage = new();
      error_coverage = new();
    end
  endfunction

  //============================================================================
  // Build Phase
  //============================================================================
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info(get_type_name(), "Build phase", UVM_LOW)
    
    // Get configuration from config_db
    // TODO: Retrieve coverage configuration
    // if (!uvm_config_db#(coverage_config)::get(this, "", "config", cfg))
    //   `uvm_warning(get_type_name(), "Config not found, using defaults")
  endfunction

  //============================================================================
  // Write Method (from uvm_subscriber)
  // Description: Called when a transaction is received
  //============================================================================
  virtual function void write(uvm_sequence_item t);
    if (!enable_coverage) return;
    
    `uvm_info(get_type_name(), "Sampling coverage", UVM_HIGH)
    
    // TODO: Extract fields from transaction
    // Example:
    // ddr5_rcd_transaction txn;
    // if ($cast(txn, t)) begin
    //   address = txn.address;
    //   command = txn.command;
    //   data = txn.data;
    //   read_write = txn.read_write;
    //   rank = txn.rank;
    //   bank_group = txn.bank_group;
    //   bank = txn.bank;
    // end
    
    // Sample all coverage groups
    sample_coverage();
  endfunction

  //============================================================================
  // Task: sample_coverage
  // Description: Sample all enabled coverage groups
  //============================================================================
  virtual function void sample_coverage();
    if (enable_command_coverage)
      command_coverage.sample();
    
    if (enable_address_coverage)
      address_coverage.sample();
    
    data_pattern_coverage.sample();
    
    if (enable_timing_coverage)
      timing_coverage.sample();
    
    if (enable_cross_coverage) begin
      protocol_coverage.sample();
      error_coverage.sample();
    end
  endfunction

  //============================================================================
  // Report Phase
  //============================================================================
  virtual function void report_phase(uvm_phase phase);
    string report;
    real cmd_cov, addr_cov, data_cov, total_cov;
    
    super.report_phase(phase);
    
    // Get coverage percentages
    if (enable_coverage) begin
      cmd_cov = command_coverage.get_coverage();
      addr_cov = address_coverage.get_coverage();
      data_cov = data_pattern_coverage.get_coverage();
      total_cov = $get_coverage();
      
      // Generate coverage report
      report = $sformatf("\n========================================\n");
      report = {report, $sformatf("DDR5 RCD COVERAGE REPORT\n")};
      report = {report, $sformatf("========================================\n")};
      report = {report, $sformatf("Command Coverage:      %0.2f%%\n", cmd_cov)};
      report = {report, $sformatf("Address Coverage:      %0.2f%%\n", addr_cov)};
      report = {report, $sformatf("Data Pattern Coverage: %0.2f%%\n", data_cov)};
      report = {report, $sformatf("----------------------------------------\n")};
      report = {report, $sformatf("Total Coverage:        %0.2f%%\n", total_cov)};
      report = {report, $sformatf("========================================\n")};
      
      `uvm_info(get_type_name(), report, UVM_LOW)
      
      // Report coverage goal status
      if (total_cov >= 95.0)
        `uvm_info(get_type_name(), "Coverage goal ACHIEVED (>= 95%)", UVM_LOW)
      else if (total_cov >= 80.0)
        `uvm_warning(get_type_name(), 
                     $sformatf("Coverage goal PARTIAL (%.2f%% < 95%%)", total_cov))
      else
        `uvm_error(get_type_name(), 
                   $sformatf("Coverage goal NOT MET (%.2f%% < 80%%)", total_cov))
    end
  endfunction

  //============================================================================
  // Function: get_coverage_summary
  // Description: Return coverage summary as string
  //============================================================================
  virtual function string get_coverage_summary();
    string summary;
    real total_cov = $get_coverage();
    
    summary = $sformatf("Total Coverage: %.2f%%", total_cov);
    return summary;
  endfunction

endclass : ddr5_rcd_coverage

`endif // DDR5_RCD_COVERAGE_SV
