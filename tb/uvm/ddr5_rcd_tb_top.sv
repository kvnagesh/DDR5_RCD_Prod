//==============================================================================
// File: ddr5_rcd_tb_top.sv
// Description: UVM Testbench Top Module for DDR5 RCD Verification
// Author: Production Implementation
// Date: 2025-11-04
//==============================================================================

`timescale 1ns/1ps

// Include UVM macros and base library
`include "uvm_macros.svh"
import uvm_pkg::*;

// Import DDR5 RCD UVM environment package
import ddr5_rcd_pkg::*;

module ddr5_rcd_tb_top;

  //============================================================================
  // Clock and Reset Signals
  //============================================================================
  logic clk;
  logic rst_n;
  
  // Clock parameters
  parameter CLK_PERIOD = 10;       // 100MHz clock
  parameter RST_DURATION = 100;    // Reset duration in ns
  parameter DDR_CLK_PERIOD = 0.625; // 1600MHz DDR5 clock
  
  //============================================================================
  // Interface Instantiations
  //============================================================================
  
  // CA (Command/Address) Interface
  ddr5_rcd_ca_if ca_if(
    .clk(clk),
    .rst_n(rst_n)
  );
  
  // DQ (Data) Interface
  ddr5_rcd_dq_if dq_if(
    .clk(clk),
    .rst_n(rst_n)
  );
  
  // Control Interface
  ddr5_rcd_ctrl_if ctrl_if(
    .clk(clk),
    .rst_n(rst_n)
  );
  
  // I2C/I3C Configuration Interface
  ddr5_rcd_i2c_if i2c_if(
    .clk(clk),
    .rst_n(rst_n)
  );
  
  //============================================================================
  // DUT Instantiation
  //============================================================================
  
  ddr5_rcd_top dut (
    .clk_i(clk),
    .rst_n_i(rst_n),
    
    // CA interface connections
    .ca_valid_i(ca_if.ca_valid),
    .ca_cmd_i(ca_if.ca_cmd),
    .ca_addr_i(ca_if.ca_addr),
    .ca_cs_i(ca_if.ca_cs),
    .ca_cke_i(ca_if.ca_cke),
    .ca_odt_i(ca_if.ca_odt),
    
    // DQ interface connections
    .dq_valid_o(dq_if.dq_valid),
    .dq_data_o(dq_if.dq_data),
    .dq_mask_o(dq_if.dq_mask),
    .dq_strobe_o(dq_if.dq_strobe),
    
    // Control interface connections
    .parity_err_o(ctrl_if.parity_err),
    .alert_n_o(ctrl_if.alert_n),
    .qca_valid_o(ctrl_if.qca_valid),
    .qcs_valid_o(ctrl_if.qcs_valid),
    
    // I2C interface connections
    .scl_i(i2c_if.scl),
    .sda_io(i2c_if.sda)
  );
  
  //============================================================================
  // Clock Generation
  //============================================================================
  
  // System clock generation
  initial begin
    clk = 0;
    forever #(CLK_PERIOD/2) clk = ~clk;
  end
  
  //============================================================================
  // Reset Generation
  //============================================================================
  
  initial begin
    rst_n = 0;
    repeat(10) @(posedge clk);
    rst_n = 1;
    `uvm_info("TB_TOP", "Reset de-asserted", UVM_MEDIUM)
  end
  
  //============================================================================
  // UVM Test Configuration and Execution
  //============================================================================
  
  initial begin
    // Configure UVM database with virtual interfaces
    uvm_config_db#(virtual ddr5_rcd_ca_if)::set(null, "uvm_test_top", "ca_vif", ca_if);
    uvm_config_db#(virtual ddr5_rcd_dq_if)::set(null, "uvm_test_top", "dq_vif", dq_if);
    uvm_config_db#(virtual ddr5_rcd_ctrl_if)::set(null, "uvm_test_top", "ctrl_vif", ctrl_if);
    uvm_config_db#(virtual ddr5_rcd_i2c_if)::set(null, "uvm_test_top", "i2c_vif", i2c_if);
    
    // Set global timeout
    uvm_top.set_timeout(100ms);
    
    // Enable UVM command line processor
    uvm_cmdline_processor clp;
    clp = uvm_cmdline_processor::get_inst();
    
    // Dump waveforms if enabled
    if (clp.get_arg_value("+UVM_DUMP_VCD=", dump_file)) begin
      $dumpfile(dump_file);
      $dumpvars(0, ddr5_rcd_tb_top);
    end
    
    // Run the test
    run_test();
  end
  
  //============================================================================
  // Watchdog Timer
  //============================================================================
  
  initial begin
    #10ms;
    `uvm_fatal("TB_TOP", "Watchdog timeout - simulation hung")
  end
  
  //============================================================================
  // Protocol Assertions Binding
  //============================================================================
  
  bind ddr5_rcd_top ddr5_rcd_assertions ddr5_assertions_inst (
    .clk(clk_i),
    .rst_n(rst_n_i),
    .ca_valid(ca_valid_i),
    .ca_cmd(ca_cmd_i),
    .ca_addr(ca_addr_i),
    .dq_valid(dq_valid_o),
    .parity_err(parity_err_o),
    .alert_n(alert_n_o)
  );
  
  //============================================================================
  // Signal Monitoring and Debug
  //============================================================================
  
  // Monitor critical errors
  always @(posedge clk) begin
    if (rst_n && ctrl_if.alert_n === 1'b0) begin
      `uvm_warning("TB_TOP", $sformatf("ALERT signal asserted at time %0t", $time))
    end
    if (rst_n && ctrl_if.parity_err === 1'b1) begin
      `uvm_warning("TB_TOP", $sformatf("Parity error detected at time %0t", $time))
    end
  end
  
  //============================================================================
  // Simulation Control
  //============================================================================
  
  // Finish simulation gracefully
  final begin
    `uvm_info("TB_TOP", "Simulation completed", UVM_LOW)
  end
  
  //============================================================================
  // Coverage and Assertion Enables
  //============================================================================
  
  initial begin
    // Enable assertion checking
    $assertcontrol(1);
    
    // Configure coverage options
    $coverage_control(1); // Enable coverage
  end
  
  // Variable for waveform dump
  string dump_file;
  
endmodule : ddr5_rcd_tb_top

//============================================================================
// Interface Definitions
//============================================================================

// CA (Command/Address) Interface
interface ddr5_rcd_ca_if(input logic clk, input logic rst_n);
  logic        ca_valid;
  logic [6:0]  ca_cmd;
  logic [16:0] ca_addr;
  logic [1:0]  ca_cs;
  logic        ca_cke;
  logic        ca_odt;
  
  // Clocking blocks for synchronous communication
  clocking cb @(posedge clk);
    default input #1step output #1ns;
    output ca_valid, ca_cmd, ca_addr, ca_cs, ca_cke, ca_odt;
  endclocking
  
  modport tb(clocking cb, input clk, rst_n);
  modport dut(input ca_valid, ca_cmd, ca_addr, ca_cs, ca_cke, ca_odt, input clk, rst_n);
endinterface : ddr5_rcd_ca_if

// DQ (Data) Interface
interface ddr5_rcd_dq_if(input logic clk, input logic rst_n);
  logic         dq_valid;
  logic [127:0] dq_data;
  logic [15:0]  dq_mask;
  logic         dq_strobe;
  
  clocking cb @(posedge clk);
    default input #1step output #1ns;
    input dq_valid, dq_data, dq_mask, dq_strobe;
  endclocking
  
  modport tb(clocking cb, input clk, rst_n);
  modport dut(output dq_valid, dq_data, dq_mask, dq_strobe, input clk, rst_n);
endinterface : ddr5_rcd_dq_if

// Control Interface
interface ddr5_rcd_ctrl_if(input logic clk, input logic rst_n);
  logic parity_err;
  logic alert_n;
  logic qca_valid;
  logic qcs_valid;
  
  clocking cb @(posedge clk);
    default input #1step output #1ns;
    input parity_err, alert_n, qca_valid, qcs_valid;
  endclocking
  
  modport tb(clocking cb, input clk, rst_n);
  modport dut(output parity_err, alert_n, qca_valid, qcs_valid, input clk, rst_n);
endinterface : ddr5_rcd_ctrl_if

// I2C/I3C Configuration Interface
interface ddr5_rcd_i2c_if(input logic clk, input logic rst_n);
  logic scl;
  wire  sda;
  logic sda_out;
  logic sda_oe;
  
  assign sda = sda_oe ? sda_out : 1'bz;
  
  clocking cb @(posedge clk);
    default input #1step output #1ns;
    output scl, sda_out, sda_oe;
    input sda;
  endclocking
  
  modport tb(clocking cb, input clk, rst_n);
  modport dut(input scl, inout sda, input clk, rst_n);
endinterface : ddr5_rcd_i2c_if
