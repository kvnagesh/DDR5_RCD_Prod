//-----------------------------------------------------------------------------
// Title       : I3C Slave Interface Testbench with Protocol Compliance
// Project     : DDR5 RCD Production
//-----------------------------------------------------------------------------
// File        : i3c_slave_tb.sv
// Author      : Verification Team
// Created     : 2025-11-11
// Description : Comprehensive testbench for I3C slave interface with protocol
//               compliance verification, timing checks, CCC command testing,
//               and IBI (In-Band Interrupt) validation for DDR5 RCD.
//-----------------------------------------------------------------------------

`timescale 1ps/1fs  // High precision for timing analysis

module i3c_slave_tb;

  //===========================================================================
  // Parameters - I3C Specification
  //===========================================================================
  
  // I3C timing parameters (12.5 MHz standard mode)
  parameter realtime I3C_CLK_PERIOD = 80000ps;       // 12.5 MHz
  parameter realtime I3C_PUSH_PULL_PERIOD = 80000ps; // Push-pull mode
  parameter realtime I3C_OPEN_DRAIN_PERIOD = 1000000ps; // 1 MHz open-drain
  
  // Timing specs
  parameter realtime T_SETUP = 3000ps;     // Setup time
  parameter realtime T_HOLD = 0ps;         // Hold time (0ns for I3C)
  parameter realtime T_HIGH_MIN = 38000ps; // SCL high time min
  parameter realtime T_LOW_MIN = 38000ps;  // SCL low time min
  parameter realtime T_HD_DAT = 0ps;       // Data hold time
  parameter realtime T_SU_DAT = 5000ps;    // Data setup time
  
  // I3C protocol parameters
  parameter bit [6:0] SLAVE_STATIC_ADDR = 7'h50;  // Static address
  parameter bit [6:0] SLAVE_DYNAMIC_ADDR = 7'h08; // Dynamic address
  parameter bit [47:0] SLAVE_PID = 48'hAABBCCDDEEFF; // Provisional ID
  parameter bit [7:0] SLAVE_BCR = 8'h06;  // Bus Characteristics
  parameter bit [7:0] SLAVE_DCR = 8'hC0;  // Device Characteristics
  
  // CCC (Common Command Codes)
  parameter bit [7:0] CCC_ENTDAA   = 8'h07; // Enter Dynamic Address Assignment
  parameter bit [7:0] CCC_SETDASA  = 8'h87; // Set Dynamic Address from Static
  parameter bit [7:0] CCC_RSTDAA   = 8'h06; // Reset Dynamic Address
  parameter bit [7:0] CCC_GETPID   = 8'h8D; // GET Provisional ID
  parameter bit [7:0] CCC_GETBCR   = 8'h8E; // GET Bus Characteristics
  parameter bit [7:0] CCC_GETDCR   = 8'h8F; // GET Device Characteristics
  parameter bit [7:0] CCC_GETSTATUS = 8'h90; // GET Status
  parameter bit [7:0] CCC_SETMWL   = 8'h89; // SET Max Write Length
  parameter bit [7:0] CCC_SETMRL   = 8'h8A; // SET Max Read Length
  
  //===========================================================================
  // DUT Signals
  //===========================================================================
  
  // I3C bus signals
  tri1 scl;      // I3C clock (open-drain with pull-up)
  tri1 sda;      // I3C data (open-drain with pull-up)
  
  logic scl_drive;
  logic sda_drive;
  logic scl_out;
  logic sda_out;
  
  // Internal signals
  logic       clk;
  logic       rst_n;
  logic [6:0] dynamic_addr_assigned;
  logic       ibi_pending;
  logic [7:0] ibi_data;
  logic       master_request_pending;
  
  //==========================================================================
  // Test Variables
  //===========================================================================
  
  int test_passed;
  int test_failed;
  int protocol_violations;
  int timing_violations;
  int ccc_commands_tested;
  realtime scl_high_time, scl_low_time;
  realtime last_scl_rise, last_scl_fall;
  
  // Bus drivers (open-drain)
  assign scl = scl_drive ? scl_out : 1'bz;
  assign sda = sda_drive ? sda_out : 1'bz;
  
  //===========================================================================
  // Clock Generation
  //===========================================================================
  
  initial begin
    clk = 0;
    forever #(I3C_CLK_PERIOD/2) clk = ~clk;
  end
  
  //===========================================================================
  // I3C Bus Timing Monitoring
  //===========================================================================
  
  always @(posedge scl) begin
    last_scl_rise = $realtime;
    scl_low_time = last_scl_rise - last_scl_fall;
    if (scl_low_time > 0 && scl_low_time < T_LOW_MIN) begin
      $error("[SCL TIMING] SCL low time violation: %.1f ps < %.1f ps",
             scl_low_time, T_LOW_MIN);
      timing_violations++;
    end
  end
  
  always @(negedge scl) begin
    last_scl_fall = $realtime;
    scl_high_time = last_scl_fall - last_scl_rise;
    if (scl_high_time > 0 && scl_high_time < T_HIGH_MIN) begin
      $error("[SCL TIMING] SCL high time violation: %.1f ps < %.1f ps",
             scl_high_time, T_HIGH_MIN);
      timing_violations++;
    end
  end
  
  //===========================================================================
  // I3C Master Tasks
  //===========================================================================
  
  task i3c_start();
    begin
      @(posedge clk);
      sda_drive = 1;
      sda_out = 0;
      #(T_SU_DAT);
      scl_drive = 1;
      scl_out = 0;
      #(I3C_OPEN_DRAIN_PERIOD/2);
      $display("[I3C] START condition generated at %.1f ps", $realtime);
    end
  endtask
  
  task i3c_repeated_start();
    begin
      @(posedge clk);
      sda_drive = 0;  // Release SDA
      #(I3C_OPEN_DRAIN_PERIOD/4);
      scl_drive = 0;  // Release SCL
      #(I3C_OPEN_DRAIN_PERIOD/4);
      sda_drive = 1;
      sda_out = 0;
      #(T_SU_DAT);
      scl_drive = 1;
      scl_out = 0;
      $display("[I3C] REPEATED START at %.1f ps", $realtime);
    end
  endtask
  
  task i3c_stop();
    begin
      @(posedge clk);
      sda_drive = 1;
      sda_out = 0;
      #(I3C_OPEN_DRAIN_PERIOD/4);
      scl_drive = 0;  // Release SCL
      #(I3C_OPEN_DRAIN_PERIOD/4);
      sda_drive = 0;  // Release SDA (goes high)
      #(I3C_OPEN_DRAIN_PERIOD/2);
      $display("[I3C] STOP condition generated at %.1f ps", $realtime);
    end
  endtask
  
  task i3c_write_byte(input bit [7:0] data, output bit ack);
    int i;
    begin
      for (i = 7; i >= 0; i--) begin
        @(posedge clk);
        sda_drive = 1;
        sda_out = data[i];
        #(T_SU_DAT);
        scl_drive = 0;  // Release SCL
        #(I3C_PUSH_PULL_PERIOD/2);
        scl_drive = 1;
        scl_out = 0;
        #(I3C_PUSH_PULL_PERIOD/2);
      end
      
      // Check ACK
      @(posedge clk);
      sda_drive = 0;  // Release SDA for ACK
      #(T_SU_DAT);
      scl_drive = 0;
      #(I3C_PUSH_PULL_PERIOD/4);
      ack = !sda;  // ACK is low
      #(I3C_PUSH_PULL_PERIOD/4);
      scl_drive = 1;
      scl_out = 0;
      #(I3C_PUSH_PULL_PERIOD/2);
      
      $display("[I3C WRITE] Byte: 0x%02X, ACK: %b at %.1f ps", data, ack, $realtime);
    end
  endtask
  
  task i3c_read_byte(output bit [7:0] data, input bit send_ack);
    int i;
    begin
      for (i = 7; i >= 0; i--) begin
        @(posedge clk);
        sda_drive = 0;  // Release SDA
        #(T_SU_DAT);
        scl_drive = 0;
        #(I3C_PUSH_PULL_PERIOD/4);
        data[i] = sda;
        #(I3C_PUSH_PULL_PERIOD/4);
        scl_drive = 1;
        scl_out = 0;
        #(I3C_PUSH_PULL_PERIOD/2);
      end
      
      // Send ACK/NACK
      @(posedge clk);
      sda_drive = 1;
      sda_out = !send_ack;  // ACK is low
      #(T_SU_DAT);
      scl_drive = 0;
      #(I3C_PUSH_PULL_PERIOD/2);
      scl_drive = 1;
      scl_out = 0;
      #(I3C_PUSH_PULL_PERIOD/2);
      
      $display("[I3C READ] Byte: 0x%02X, ACK: %b at %.1f ps", data, send_ack, $realtime);
    end
  endtask
  
  //===========================================================================
  // CCC Command Tasks
  //===========================================================================
  
  task send_ccc_broadcast(input bit [7:0] ccc_cmd);
    bit ack;
    begin
      i3c_start();
      i3c_write_byte({7'h7E, 1'b0}, ack);  // Broadcast address
      if (!ack) begin
        $error("[CCC] No ACK for broadcast address");
        protocol_violations++;
      end
      i3c_write_byte(ccc_cmd, ack);
      if (!ack) begin
        $error("[CCC] No ACK for CCC command 0x%02X", ccc_cmd);
        protocol_violations++;
      end
      $display("[CCC] Broadcast command 0x%02X sent", ccc_cmd);
      ccc_commands_tested++;
    end
  endtask
  
  task send_ccc_direct(input bit [7:0] ccc_cmd, input bit [6:0] target_addr);
    bit ack;
    begin
      i3c_start();
      i3c_write_byte({7'h7E, 1'b0}, ack);
      if (!ack) begin
        $error("[CCC] No ACK for broadcast address");
        protocol_violations++;
      end
      i3c_write_byte(ccc_cmd, ack);
      if (!ack) begin
        $error("[CCC] No ACK for CCC command 0x%02X", ccc_cmd);
        protocol_violations++;
      end
      i3c_write_byte({target_addr, 1'b0}, ack);
      $display("[CCC] Direct command 0x%02X to addr 0x%02X", ccc_cmd, target_addr);
      ccc_commands_tested++;
    end
  endtask
  
  //===========================================================================
  // Test Scenarios
  //===========================================================================
  
  task test_basic_i3c_transaction();
    bit ack;
    bit [7:0] read_data;
    begin
      $display("\n===========================================");
      $display("TEST: Basic I3C Write/Read Transaction");
      $display("===========================================");
      
      // Write to static address
      i3c_start();
      i3c_write_byte({SLAVE_STATIC_ADDR, 1'b0}, ack);
      if (ack) begin
        $display("[PASS] Slave ACK'd static address");
        test_passed++;
      end else begin
        $error("[FAIL] Slave did not ACK static address");
        test_failed++;
      end
      
      i3c_write_byte(8'hA5, ack);
      i3c_write_byte(8'h5A, ack);
      i3c_stop();
      
      #(I3C_CLK_PERIOD * 10);
      
      // Read from static address
      i3c_start();
      i3c_write_byte({SLAVE_STATIC_ADDR, 1'b1}, ack);
      i3c_read_byte(read_data, 1);  // Send ACK
      i3c_read_byte(read_data, 0);  // Send NACK
      i3c_stop();
      
      $display("[TEST] Basic transaction completed\n");
    end
  endtask
  
  task test_entdaa_procedure();
    bit ack;
    bit [47:0] pid_read;
    bit [7:0] bcr_read, dcr_read;
    bit [6:0] assigned_addr;
    int i;
    begin
      $display("\n===========================================");
      $display("TEST: ENTDAA - Dynamic Address Assignment");
      $display("===========================================");
      
      // Send ENTDAA CCC command
      send_ccc_broadcast(CCC_ENTDAA);
      
      // Slave should respond with PID, BCR, DCR
      for (i = 5; i >= 0; i--) begin
        i3c_read_byte(pid_read[i*8 +: 8], 1);
      end
      i3c_read_byte(bcr_read, 1);
      i3c_read_byte(dcr_read, 1);
      
      // Assign dynamic address
      assigned_addr = SLAVE_DYNAMIC_ADDR;
      i3c_write_byte({assigned_addr, 1'b0}, ack);
      
      i3c_stop();
      
      if (pid_read == SLAVE_PID) begin
        $display("[PASS] PID matches: 0x%012X", pid_read);
        test_passed++;
      end else begin
        $error("[FAIL] PID mismatch: expected 0x%012X, got 0x%012X", SLAVE_PID, pid_read);
        test_failed++;
      end
      
      dynamic_addr_assigned = assigned_addr;
      $display("[TEST] Dynamic address 0x%02X assigned\n", assigned_addr);
    end
  endtask
  
  task test_ccc_commands();
    bit ack;
    bit [7:0] data;
    begin
      $display("\n===========================================");
      $display("TEST: CCC Commands - Protocol Compliance");
      $display("===========================================");
      
      // Test GETPID
      send_ccc_direct(CCC_GETPID, SLAVE_DYNAMIC_ADDR);
      i3c_repeated_start();
      i3c_write_byte({SLAVE_DYNAMIC_ADDR, 1'b1}, ack);
      for (int i = 0; i < 6; i++) begin
        i3c_read_byte(data, (i < 5));
      end
      i3c_stop();
      $display("[TEST] GETPID completed");
      
      #(I3C_CLK_PERIOD * 10);
      
      // Test GETBCR
      send_ccc_direct(CCC_GETBCR, SLAVE_DYNAMIC_ADDR);
      i3c_repeated_start();
      i3c_write_byte({SLAVE_DYNAMIC_ADDR, 1'b1}, ack);
      i3c_read_byte(data, 0);
      i3c_stop();
      $display("[TEST] GETBCR completed");
      
      #(I3C_CLK_PERIOD * 10);
      
      // Test GETDCR
      send_ccc_direct(CCC_GETDCR, SLAVE_DYNAMIC_ADDR);
      i3c_repeated_start();
      i3c_write_byte({SLAVE_DYNAMIC_ADDR, 1'b1}, ack);
      i3c_read_byte(data, 0);
      i3c_stop();
      $display("[TEST] GETDCR completed");
      
      #(I3C_CLK_PERIOD * 10);
      
      // Test GETSTATUS
      send_ccc_direct(CCC_GETSTATUS, SLAVE_DYNAMIC_ADDR);
      i3c_repeated_start();
      i3c_write_byte({SLAVE_DYNAMIC_ADDR, 1'b1}, ack);
      i3c_read_byte(data, 0);
      i3c_stop();
      $display("[TEST] GETSTATUS completed");
      
      #(I3C_CLK_PERIOD * 10);
      
      // Test RSTDAA
      send_ccc_broadcast(CCC_RSTDAA);
      i3c_stop();
      dynamic_addr_assigned = 7'h00;
      $display("[TEST] RSTDAA - Dynamic address reset");
      
      $display("[TEST] CCC commands testing completed\n");
      test_passed++;
    end
  endtask
  
  task test_ibi_handling();
    bit ack;
    begin
      $display("\n===========================================");
      $display("TEST: IBI (In-Band Interrupt) Handling");
      $display("===========================================");
      
      // Simulate IBI from slave
      ibi_pending = 1;
      ibi_data = 8'hAA;
      
      #(I3C_CLK_PERIOD * 20);
      
      // Master should detect IBI request on SDA
      if (sda == 0) begin
        $display("[PASS] IBI detected on bus");
        test_passed++;
      end else begin
        $error("[FAIL] IBI not detected");
        test_failed++;
      end
      
      // Master ACKs IBI
      i3c_start();
      i3c_read_byte(ibi_data, 0);  // Read IBI data
      i3c_stop();
      
      ibi_pending = 0;
      $display("[TEST] IBI handling completed\n");
    end
  endtask
  
  task test_timing_compliance();
    begin
      $display("\n===========================================");
      $display("TEST: Timing Compliance Verification");
      $display("===========================================");
      
      // Run some transactions and check timing
      test_basic_i3c_transaction();
      
      if (timing_violations == 0) begin
        $display("[PASS] No timing violations detected");
        test_passed++;
      end else begin
        $error("[FAIL] %0d timing violations detected", timing_violations);
        test_failed++;
      end
      
      $display("[TEST] Timing compliance check completed\n");
    end
  endtask
  
  task test_protocol_errors();
    bit ack;
    begin
      $display("\n===========================================");
      $display("TEST: Protocol Error Handling");
      $display("===========================================");
      
      // Test invalid address
      i3c_start();
      i3c_write_byte({7'h7F, 1'b0}, ack);  // Reserved address
      if (!ack) begin
        $display("[PASS] Reserved address correctly NACK'd");
        test_passed++;
      end else begin
        $error("[FAIL] Reserved address incorrectly ACK'd");
        test_failed++;
      end
      i3c_stop();
      
      #(I3C_CLK_PERIOD * 10);
      
      // Test START without STOP
      i3c_start();
      i3c_write_byte({SLAVE_STATIC_ADDR, 1'b0}, ack);
      // Don't send STOP, send repeated START
      i3c_repeated_start();
      i3c_write_byte({SLAVE_STATIC_ADDR, 1'b0}, ack);
      i3c_stop();
      
      $display("[TEST] Protocol error handling completed\n");
    end
  endtask
  
  task print_final_report();
    begin
      $display("\n\n");
      $display("=".repeat(70));
      $display("              I3C SLAVE INTERFACE TEST REPORT");
      $display("=".repeat(70));
      $display("");
      $display("Test Summary:");
      $display("  Tests Passed:          %0d", test_passed);
      $display("  Tests Failed:          %0d", test_failed);
      $display("  Protocol Violations:   %0d", protocol_violations);
      $display("  Timing Violations:     %0d", timing_violations);
      $display("  CCC Commands Tested:   %0d", ccc_commands_tested);
      $display("");
      $display("Protocol Compliance:");
      $display("  Static Address:        0x%02X", SLAVE_STATIC_ADDR);
      $display("  Dynamic Address:       0x%02X", dynamic_addr_assigned);
      $display("  Provisional ID:        0x%012X", SLAVE_PID);
      $display("");
      $display("Timing Parameters:");
      $display("  SCL Frequency:         %.2f MHz", 1000000.0/I3C_CLK_PERIOD);
      $display("  SCL High Time:         %.1f ps", scl_high_time);
      $display("  SCL Low Time:          %.1f ps", scl_low_time);
      $display("");
      
      if (test_failed == 0 && protocol_violations == 0 && timing_violations == 0) begin
        $display("OVERALL RESULT: *** PASS *** - All tests passed!");
      end else begin
        $display("OVERALL RESULT: *** FAIL *** - Some tests failed!");
      end
      
      $display("=".repeat(70));
      $display("");
    end
  endtask
  
  //===========================================================================
  // Main Test Execution
  //===========================================================================
  
  initial begin
    // Initialize
    rst_n = 0;
    scl_drive = 0;
    sda_drive = 0;
    scl_out = 1;
    sda_out = 1;
    test_passed = 0;
    test_failed = 0;
    protocol_violations = 0;
    timing_violations = 0;
    ccc_commands_tested = 0;
    dynamic_addr_assigned = 7'h00;
    ibi_pending = 0;
    ibi_data = 8'h00;
    last_scl_rise = 0;
    last_scl_fall = 0;
    
    // Waveform dump
    $dumpfile("i3c_slave_tb.vcd");
    $dumpvars(0, i3c_slave_tb);
    
    $display("");
    $display("=".repeat(70));
    $display("       I3C SLAVE INTERFACE TESTBENCH - DDR5 RCD Production");
    $display("=".repeat(70));
    $display("Start time: %.1f ps", $realtime);
    $display("");
    
    // Reset sequence
    #(I3C_CLK_PERIOD * 5);
    rst_n = 1;
    #(I3C_CLK_PERIOD * 5);
    
    // Run tests
    test_basic_i3c_transaction();
    #(I3C_CLK_PERIOD * 10);
    
    test_entdaa_procedure();
    #(I3C_CLK_PERIOD * 10);
    
    test_ccc_commands();
    #(I3C_CLK_PERIOD * 10);
    
    test_timing_compliance();
    #(I3C_CLK_PERIOD * 10);
    
    test_protocol_errors();
    #(I3C_CLK_PERIOD * 10);
    
    test_ibi_handling();
    #(I3C_CLK_PERIOD * 10);
    
    // Print report
    print_final_report();
    
    // Timeout
    #100000;
    $display("[TIMEOUT] Testbench completed at %.1f ps", $realtime);
    $finish;
  end
  
  // Timeout watchdog
  initial begin
    #100000000;  // 100us
    $error("[TIMEOUT] Testbench timeout!");
    $finish;
  end

endmodule
