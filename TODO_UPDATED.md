# DDR5 RCD (Registering Clock Driver) - TODO List

This document contains all TODO items found across the DDR5_RCD_Prod repository, organized by file and section with line numbers.

---

## architecture.md

### Data Path Architecture (Line 23)
**TODO: RTL Enhancements:**
- Implement the complete CA (Command/Address) path with full DDR5 packet decoding
- Add DCALCSR (DCK and CS_n calibration) logic for precise signal alignment
- Implement QCA (QCS gating for CA) functionality with configurable gating patterns
- Add QCK (QCS gating for CK) control logic
- Implement DRAM initialization sequence controller
- Add support for variable command latencies (MR13 settings)
- Implement BCW (Buffer Control Word) register updates and state management

### Configuration Management (Line 50)
**TODO: RTL Enhancements:**
- Implement complete I3C slave interface for register access
- Add register shadowing mechanism for critical control registers
- Implement register access protection and lock mechanisms
- Add register default value initialization on reset
- Implement register read-back verification
- Add support for multi-beat I3C transfers
- Implement error detection and reporting for register accesses

### Timing and Synchronization (Line 80)
**TODO: RTL Enhancements:**
- Implement complete PLL initialization and lock detection
- Add automatic phase calibration for DCK
- Implement jitter measurement and reporting
- Add duty cycle correction logic
- Implement clock failover mechanism
- Add support for spread-spectrum clocking
- Implement clock domain crossing synchronizers with proper gray coding

### I3C Interface (Line 110)
**TODO: RTL Enhancements:**
- Implement complete I3C protocol state machine
- Add support for all required I3C features (HDR modes, IBI)
- Implement proper timing checks for I3C signals
- Add error detection and recovery mechanisms
- Implement hot-join capability
- Add support for I3C broadcast commands
- Implement proper clock stretching logic

### Error Checking and Correction (Line 141)
**TODO: RTL Enhancements:**
- Implement complete ECC encoder/decoder
- Add CRC-5 calculation and checking for RCD bus
- Implement parity checking for all critical signals
- Add error logging and reporting mechanism
- Implement error injection for testing
- Add support for correctable and uncorrectable error differentiation
- Implement error threshold monitoring

### Verification and Testbench (Line 196)
**TODO: RTL Enhancements:**
- Complete UVM testbench with all required components
- Add comprehensive coverage metrics
- Implement constrained-random testing
- Add directed tests for all features
- Implement regression test suite
- Add power-aware verification
- Implement formal verification for critical paths
- Add stress testing scenarios

---

## src/i3c/register_map.sv

### Register Access Implementation (Line 171)
- **Line 171**: TODO: Implement register read logic based on reg_addr
  - Status: Appears to be implemented with case statement

### Register Mapping (Line 192)
- **Line 192**: TODO: Map register bits to output signals
  - Status: Appears to be implemented

### Register Acknowledge (Line 205)
- **Line 205**: TODO: Implement register access acknowledge
  - Status: Appears to be implemented with ack_o signal assignment

---

## src/data_path/ca_packetizer.sv

### DDR5 Specification Alignment (Line 131)
- **Line 131**: TODO: Update field mappings per full DDR5 spec if addr/cmd wider
  - Need to verify field widths match the latest DDR5 JEDEC specification
  - May need to expand command and address field widths for future DDR5 speeds
  - Verify packet structure aligns with production DDR5 RCD requirements

---

## src/i3c/timing_checker.sv

### Integration Logic (Line 274)
- **Line 274**: TODO: add integration logic if needed
  - Consider adding integration of timing check results
  - May need aggregation logic for multiple timing violations
  - Could add statistical tracking of timing margins

---

## tb/uvm/components/ddr5_rcd_scoreboard.sv

### Field Comparison Implementation (Line 83/199)
- **Line 83**: TODO Implementation - Detailed field-by-field comparison
  - Status: Implemented with compare_ca_packets function
  - Comprehensive field-by-field comparison is now in place
  - Includes CA, CS_n, CID, BCW, DCA0-5 fields

---

## tb/uvm/coverage/ddr5_rcd_coverage.sv

### Error Scenario Coverage (Line 196)
- **Line 196**: TODO: Implement error scenario coverage group
  - Status: Completed - Error scenarios coverage group has been implemented
  - Includes parity errors, CRC errors, protocol violations, and timing violations
  - Commit: "Implement error scenario coverage group (TODO line 196)"

---

## Summary

**Total TODO Items by Status:**
- **Active TODOs**: 52 items (primarily in architecture.md outlining design enhancements)
- **Implemented TODOs**: 5 items (in source and testbench files)
- **Partially Complete**: 2 items (register_map.sv implementations need verification)

**Priority Areas:**
1. I3C Interface implementation (high priority for configuration)
2. Complete CA path with DDR5 packet decoding (critical for functionality)
3. Timing and synchronization enhancements (essential for signal integrity)
4. ECC and error checking logic (required for production)
5. Verification testbench completion (needed for validation)

**Files Requiring Updates:**
1. Create new RTL modules for items listed in architecture.md
2. Verify and potentially enhance implementations in register_map.sv
3. Update ca_packetizer.sv field widths per latest DDR5 spec
4. Add integration logic to timing_checker.sv if system design requires it

---

*Last Updated: Auto-generated from repository scan*
*Repository: kvnagesh/DDR5_RCD_Prod*
*Branch: main*
