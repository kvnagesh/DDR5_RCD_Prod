// uvm_testbench_pkg.sv - UVM Testbench Package for DDR5 RCD Modules
// Author: [Your Name]
// Description: Top-level UVM package for RCD module testbench. Includes classes, metrics, covergroups, and documentation for ECC, CRC, parity, error log, clock, I3C, etc.

package uvm_testbench_pkg;

   import uvm_pkg::*;
   `include "uvm_macros.svh"

   // ***************************************************************
   // 1. Configuration and Run Templates
   // ***************************************************************
   class test_config extends uvm_object;
      bit enable_ecc;
      bit enable_crc;
      bit enable_parity;
      bit enable_errorlog;
      bit enable_clock;
      bit enable_i3c;
      rand int scenario_selector;
      // Further config parameters as needed
      `uvm_field_int(enable_ecc, UVM_ALL_ON)
      `uvm_field_int(enable_crc, UVM_ALL_ON)
      // ...
      `uvm_field_int(scenario_selector, UVM_ALL_ON)
      function new(string name = "test_config"); super.new(name); endfunction
   endclass

   // ***************************************************************
   // 2. Metrics and Coverage Classes
   // ***************************************************************
   class rcd_metrics extends uvm_object;
      int unsigned total_tests;
      int unsigned errors;
      // Add metric counters for each block
      function void report();
         // Report metrics at end-of-test
      endfunction
      function new(string name = "rcd_metrics"); super.new(name); endfunction
   endclass

   // Covergroup for each module feature/scenario
   class ecc_coverage extends uvm_object;
      covergroup cg_ecc;
         option.per_instance = 1;
         cp_ecc: coverpoint ...;  // ECC scenarios
         cp_err: coverpoint ...;  // ECC error types
      endgroup
      function new(string name = "ecc_coverage"); super.new(name); cg_ecc = new(); endfunction
   endclass
   // Repeat similarly for CRC, parity, errorlog, clock, i3c blocks

   // ***************************************************************
   // 3. UVM Testbench Class Hierarchy
   // ***************************************************************
   class rcd_env extends uvm_env;
      // env contains agents/interfaces for all modules
      // ...
      function new(string name = "rcd_env"); super.new(name); endfunction
   endclass

   class rcd_top_test extends uvm_test;
      rcd_env env;
      test_config cfg;
      rcd_metrics metrics;
      // coverage objects for all blocks
      // ...
      function new(string name = "rcd_top_test"); super.new(name); endfunction
      virtual function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         env = rcd_env::type_id::create("env", this);
         cfg = test_config::type_id::create("cfg", this);
         metrics = rcd_metrics::type_id::create("metrics", this);
         // ...
      endfunction
      virtual function void run_phase(uvm_phase phase);
         // randomized testing, error injection, statistics collection
      endfunction
   endclass

   // ***************************************************************
   // 4. Class Documentation
   // ***************************************************************
   // All sections describe config, agents, run phases, coverage, error injection
   // See above comments per class section

endpackage
