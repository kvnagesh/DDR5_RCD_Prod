# DDR5 RCD (Registering Clock Driver) - AI Prompts

Prompts below are derived from all TODOs in the repository, rephrased as actionable instructions for generative AI models.

---

## architecture.md

### Data Path Architecture
- Implement SystemVerilog code for complete CA (Command/Address) path with DDR5 packet decoding capability.
- Design and integrate DCALCSR logic to calibrate DCK and CS_n signals for DDR5 alignment.
- Add configurable QCA gating logic to support advanced command/address flow control.
- Implement QCK control for dynamic CK (clock) gating per DDR5 requirements.
- Create an RTL controller for DRAM initialization sequencing.
- Design logic to support variable command latencies as set by MR13 configuration.
- Add RTL for BCW register updates and high-speed state management.

### Configuration Management
- Implement a SystemVerilog I3C slave interface for all RCD registers.
- Add a shadowing mechanism for critical configuration registers with synchronization.
- Develop a secure access control system and lock mechanism for protected registers.
- Write RTL/firmware for register value initialization on global reset.
- Implement read-back logic with error checking for register accesses.
- Design support for multi-beat register transfers on I3C bus.
- Add error detection/reporting logic for all register read/write activity.

### Timing and Synchronization
- Implement a full PLL initialization and lock detection circuit in SystemVerilog.
- Add automatic DCK phase calibration logic for dynamic clock alignment.
- Design a hardware module for on-chip jitter measurement and real-time reporting.
- Add duty cycle correction circuitry to clock distribution net.
- Program a robust clock failover controller to switch between redundant sources automatically.
- Integrate spread-spectrum clocking logic for EMI reduction.
- Add clock domain crossing synchronizers using gray-coded logic.

### I3C Interface
- Develop a SystemVerilog state machine for complete I3C protocol compliance.
- Add support for all HDR modes and In-Band Interrupt (IBI) handling per I3C spec.
- Implement timing constraint checks on all I3C bus signals.
- Add error detection, recovery, and bus arbitration logic.
- Implement hot-join handling and proper notification to host master.
- Support broadcast and dynamic address assignment commands in I3C interface.
- Design proper clock stretching mechanisms for variable-speed I3C operations.

### Error Checking and Correction
- Develop a parameterizable ECC encoder/decoder for all critical RCD data paths.
- Implement CRC-5 calculation circuits for the RCD bus protocol.
- Add RTL for parity checking on all bus signals with reporting.
- Create an error logging hardware module with register interface for debug.
- Integrate error injection capability to aid test bench scenarios.
- Add logic to distinguish between correctable and uncorrectable errors.
- Monitor error count thresholds and trigger system-level flags.

### Verification and Testbench
- Develop a UVM testbench in SystemVerilog to cover every RCD module.
- Add metrics and covergroups for comprehensive feature and scenario coverage.
- Implement constrained-random and directed traffic generators.
- Develop regression scripts for automated batch testing.
- Add test scenarios to verify power-down and power-aware operation.
- Specify formal properties for Logic Equivalence Checking on safety-critical blocks.
- Integrate stress-testing environments to validate max performance and timing.

---

## src/i3c/register_map.sv
- Write SystemVerilog logic to implement register read functionality based on reg_addr input.
- Map register bits to external outputs and write-back signals in register_map.sv.
- Program a robust register access acknowledge (ack_o) system covering all edge scenarios.

## src/data_path/ca_packetizer.sv
- Update field mapping logic to support wider address/command field widths as per updated DDR5 spec, ensuring future expandability.

## src/i3c/timing_checker.sv
- Add a SystemVerilog timing check integration logic to aggregate results from all submodules, with violation counters and statistics.

## tb/uvm/components/ddr5_rcd_scoreboard.sv
- Create a field-by-field comparison function for CA packets, including CA, CS_n, CID, BCW, and DCA fields, to be used in scoreboard checks.

## tb/uvm/coverage/ddr5_rcd_coverage.sv
- Implement UVM covergroups for parity errors, CRC errors, protocol violations, and timing violations, with coverage tracking and reporting.

---

*Last Updated: Prompts auto-generated for generative AI use, based on active repository TODOs.*
