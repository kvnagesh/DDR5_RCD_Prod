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

  //============================================================================
  // Covergroup: cg_error_scenarios
  // Description: Error scenario coverage for DDR5 protocol violations,
  //              timing violations, data corruption, and recovery cases
  // Implementation of TODO from line 196
  //============================================================================
  covergroup cg_error_scenarios;
    option.per_instance = 1;
    option.comment = "DDR5 RCD Error Scenario Coverage";

    // Protocol Violation Coverage
    protocol_violation_type: coverpoint trans.protocol_violation {
      bins invalid_cmd_sequence = {0};
      bins illegal_ca_pattern = {1};
      bins invalid_chipselect_combination = {2};
      bins reserved_cmd_used = {3};
      bins invalid_mode_register = {4};
      bins ca_parity_error = {5};
      bins crc_error = {6};
      bins invalid_state_transition = {7};
      bins no_error = {8};
    }

    // Command Timing Violation Coverage
    timing_violation_type: coverpoint trans.timing_violation {
      bins tCCD_violation = {0};     // CAS to CAS delay
      bins tRCD_violation = {1};     // RAS to CAS delay
      bins tRP_violation = {2};      // Row precharge time
      bins tRAS_violation = {3};     // Row active time
      bins tWR_violation = {4};      // Write recovery time
      bins tRTP_violation = {5};     // Read to precharge
      bins tWTR_violation = {6};     // Write to read delay
      bins tRRD_violation = {7};     // Row to row activation delay
      bins tFAW_violation = {8};     // Four bank activation window
      bins tREFI_violation = {9};    // Refresh interval
      bins setup_hold_violation = {10};
      bins no_timing_violation = {11};
    }

    // Data Corruption Coverage
    data_corruption_type: coverpoint trans.data_corruption {
      bins single_bit_error = {0};
      bins multi_bit_error = {1};
      bins dq_pin_stuck_at_0 = {2};
      bins dq_pin_stuck_at_1 = {3};
      bins dqs_corruption = {4};
      bins dm_mask_error = {5};
      bins burst_length_mismatch = {6};
      bins data_bus_inversion_error = {7};
      bins ecc_uncorrectable_error = {8};
      bins ecc_correctable_error = {9};
      bins no_data_corruption = {10};
    }

    // Error Recovery State Coverage
    recovery_state: coverpoint trans.recovery_state {
      bins error_detected = {0};
      bins alert_signaled = {1};
      bins recovery_initiated = {2};
      bins retry_in_progress = {3};
      bins error_logged = {4};
      bins recovery_complete = {5};
      bins recovery_failed = {6};
      bins normal_operation = {7};
    }

    // Error Severity Coverage
    error_severity: coverpoint trans.error_severity {
      bins no_error = {0};
      bins correctable = {1};
      bins uncorrectable_non_fatal = {2};
      bins uncorrectable_fatal = {3};
    }

    // Alert Signal Status
    alert_status: coverpoint trans.alert_n {
      bins alert_active = {0};
      bins alert_inactive = {1};
    }

    // Error Injection Control (for testing)
    error_injection_active: coverpoint trans.error_inject_en {
      bins injection_disabled = {0};
      bins injection_enabled = {1};
    }

    //==========================================================================
    // Cross Coverage: Protocol Violations with Recovery
    //==========================================================================
    protocol_recovery_cross: cross protocol_violation_type, recovery_state {
      // Ignore crosses where no error occurred
      ignore_bins no_error_state = binsof(protocol_violation_type.no_error);
    }

    //==========================================================================
    // Cross Coverage: Timing Violations with Severity
    //==========================================================================
    timing_severity_cross: cross timing_violation_type, error_severity {
      // Ignore crosses with no timing violations
      ignore_bins no_timing_error = binsof(timing_violation_type.no_timing_violation);
    }

    //==========================================================================
    // Cross Coverage: Data Corruption with Recovery State
    //==========================================================================
    corruption_recovery_cross: cross data_corruption_type, recovery_state {
      // Focus on actual corruption scenarios
      ignore_bins no_corruption = binsof(data_corruption_type.no_data_corruption);
    }

    //==========================================================================
    // Cross Coverage: Error Severity with Alert Status
    //==========================================================================
    severity_alert_cross: cross error_severity, alert_status {
      // Fatal errors should always trigger alert
      bins fatal_with_alert = binsof(error_severity.uncorrectable_fatal) &&
                              binsof(alert_status.alert_active);
      // Correctable errors may not trigger alert
      bins correctable_no_alert = binsof(error_severity.correctable) &&
                                  binsof(alert_status.alert_inactive);
    }

    //==========================================================================
    // Cross Coverage: Multiple Error Types Occurring Together
    //==========================================================================
    multi_error_cross: cross protocol_violation_type, timing_violation_type, 
                             data_corruption_type {
      // Only cover cases where at least one error type is present
      ignore_bins all_no_errors = binsof(protocol_violation_type.no_error) &&
                                  binsof(timing_violation_type.no_timing_violation) &&
                                  binsof(data_corruption_type.no_data_corruption);
    }

    //==========================================================================
    // Cross Coverage: Error Injection Testing
    //==========================================================================
    injection_error_cross: cross error_injection_active, error_severity {
      // Verify errors occur when injection is enabled
      bins injected_errors = binsof(error_injection_active.injection_enabled) &&
                             (!binsof(error_severity.no_error));
    }

    //==========================================================================
    // Cross Coverage: Recovery Success/Failure Analysis
    //==========================================================================
    recovery_outcome_cross: cross error_severity, recovery_state {
      // Track recovery completion for different error severities
      bins correctable_recovered = binsof(error_severity.correctable) &&
                                   binsof(recovery_state.recovery_complete);
      bins fatal_recovery_failed = binsof(error_severity.uncorrectable_fatal) &&
                                   binsof(recovery_state.recovery_failed);
    }

  endgroup

  // Transaction for coverage sampling
  uvm_sequence_item trans;
  //============================================================================
  // Constructor
  //============================================================================
  function new(string name="ddr5_rcd_coverage", uvm_component parent);
    super.new(name, parent);
    cg_main_transaction = new();
    cg_error_scenarios = new();
  endfunction
  //============================================================================
  // Coverage Write: Sample transaction in covergroup
  //============================================================================
  function void write(uvm_sequence_item t);
    trans = t;
    cg_main_transaction.sample();
    cg_error_scenarios.sample();
    `uvm_info(get_type_name(), $sformatf("Sampled coverage for transaction"), UVM_LOW)
  endfunction
endclass : ddr5_rcd_coverage
`endif // DDR5_RCD_COVERAGE_SV
