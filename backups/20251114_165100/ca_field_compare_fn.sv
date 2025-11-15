//==============================================================================
// File: ca_field_compare_fn.sv
// Description: SystemVerilog function library for field-by-field CA packet
//              comparison in DDR5 RCD verification. Supports comprehensive
//              validation of Command/Address fields for scoreboard and
//              automated checks.
// Author: DDR5 RCD Verification Team
// Date: 2025
//==============================================================================

`ifndef __CA_FIELD_COMPARE_FN_SV__
`define __CA_FIELD_COMPARE_FN_SV__

//==============================================================================
// Package: ca_field_compare_pkg
// Description: Contains field comparison functions and comparison result
//              structures for CA packet validation
//==============================================================================
package ca_field_compare_pkg;

  //============================================================================
  // Structure: ca_field_comparison_result_t
  // Description: Contains comparison results for each CA field
  // Fields:
  //   - ca_match: Command/Address field match flag
  //   - cs_n_match: Chip Select match flag
  //   - cid_match: CID field match flag
  //   - bcw_match: Burst Chop With match flag
  //   - dca_match: Discrete Command/Address match flag
  //   - all_match: All fields match flag
  //   - match_count: Number of matching fields
  //   - mismatch_fields: Bitmask indicating mismatched fields
  //============================================================================
  typedef struct packed {
    logic ca_match;
    logic cs_n_match;
    logic cid_match;
    logic bcw_match;
    logic dca_match;
    logic all_match;
    logic [4:0] match_count;  // 0-5 fields match
    logic [4:0] mismatch_fields;  // Bitmask for failed comparisons
  } ca_field_comparison_result_t;

  //============================================================================
  // Function: compare_ca_fields()
  // Description: Performs field-by-field comparison of two CA packets.
  //              Returns detailed comparison results for each field.
  // Parameters:
  //   - ca_ref: Reference CA field value (expected)
  //   - ca_dut: CA field value from DUT (actual)
  //   - cs_n_ref: Reference Chip Select value
  //   - cs_n_dut: Chip Select value from DUT
  //   - cid_ref: Reference CID value
  //   - cid_dut: CID value from DUT
  //   - bcw_ref: Reference BCW value
  //   - bcw_dut: BCW value from DUT
  //   - dca_ref: Reference DCA value
  //   - dca_dut: DCA value from DUT
  // Returns:
  //   - ca_field_comparison_result_t: Structure containing per-field
  //     comparison results and overall match status
  // Usage in Scoreboard:
  //   ca_field_comparison_result_t result;
  //   result = compare_ca_fields(ref_ca, dut_ca, ref_cs_n, dut_cs_n,
  //                              ref_cid, dut_cid, ref_bcw, dut_bcw,
  //                              ref_dca, dut_dca);
  //   assert (result.all_match) else $error("CA field mismatch");
  //============================================================================
  function automatic ca_field_comparison_result_t compare_ca_fields(
    input logic [9:0] ca_ref,
    input logic [9:0] ca_dut,
    input logic cs_n_ref,
    input logic cs_n_dut,
    input logic [2:0] cid_ref,
    input logic [2:0] cid_dut,
    input logic [5:0] bcw_ref,
    input logic [5:0] bcw_dut,
    input logic [7:0] dca_ref,
    input logic [7:0] dca_dut
  );
    ca_field_comparison_result_t result;

    // Initialize result
    result = '0;

    // Compare CA field (Command/Address)
    result.ca_match = (ca_ref == ca_dut);
    if (!result.ca_match) result.mismatch_fields[0] = 1'b1;

    // Compare CS_n field (Chip Select)
    result.cs_n_match = (cs_n_ref == cs_n_dut);
    if (!result.cs_n_match) result.mismatch_fields[1] = 1'b1;

    // Compare CID field (CID)
    result.cid_match = (cid_ref == cid_dut);
    if (!result.cid_match) result.mismatch_fields[2] = 1'b1;

    // Compare BCW field (Burst Chop With)
    result.bcw_match = (bcw_ref == bcw_dut);
    if (!result.bcw_match) result.mismatch_fields[3] = 1'b1;

    // Compare DCA field (Discrete Command/Address)
    result.dca_match = (dca_ref == dca_dut);
    if (!result.dca_match) result.mismatch_fields[4] = 1'b1;

    // Calculate overall match status and match count
    result.all_match = result.ca_match && result.cs_n_match &&
                      result.cid_match && result.bcw_match &&
                      result.dca_match;

    result.match_count = (result.ca_match   ? 5'h1 : 5'h0) +
                        (result.cs_n_match ? 5'h1 : 5'h0) +
                        (result.cid_match  ? 5'h1 : 5'h0) +
                        (result.bcw_match  ? 5'h1 : 5'h0) +
                        (result.dca_match  ? 5'h1 : 5'h0);

    return result;
  endfunction

  //============================================================================
  // Function: compare_ca_field()
  // Description: Simplified function for comparing individual CA fields.
  //              Returns true if fields match, false otherwise.
  // Parameters:
  //   - field_name: Name of field being compared (for debugging/logging)
  //   - ref_value: Reference value
  //   - dut_value: DUT value
  // Returns:
  //   - logic: true if match, false if mismatch
  // Usage:
  //   if (compare_ca_field("CA", ref_ca, dut_ca)) begin
  //     match_count++;
  //   end else begin
  //     $error("CA field mismatch: ref=%h, dut=%h", ref_ca, dut_ca);
  //   end
  //============================================================================
  function automatic logic compare_ca_field(
    input string field_name,
    input logic [31:0] ref_value,
    input logic [31:0] dut_value
  );
    logic match;
    match = (ref_value == dut_value);
    if (!match) begin
      $warning("CA Field Mismatch [%s]: Reference=0x%h, DUT=0x%h",
               field_name, ref_value, dut_value);
    end
    return match;
  endfunction

  //============================================================================
  // Function: get_comparison_report()
  // Description: Generates human-readable report of comparison results.
  //              Used for logging and debugging verification failures.
  // Parameters:
  //   - result: Comparison result structure
  //   - ca_ref, ca_dut: Reference and DUT CA values
  //   - cs_n_ref, cs_n_dut: Reference and DUT CS_n values
  //   - cid_ref, cid_dut: Reference and DUT CID values
  //   - bcw_ref, bcw_dut: Reference and DUT BCW values
  //   - dca_ref, dca_dut: Reference and DUT DCA values
  // Returns:
  //   - string: Formatted report string
  // Usage:
  //   string report = get_comparison_report(result, ca_ref, ca_dut, ...);
  //   $display("%s", report);
  //============================================================================
  function automatic string get_comparison_report(
    input ca_field_comparison_result_t result,
    input logic [9:0] ca_ref,
    input logic [9:0] ca_dut,
    input logic cs_n_ref,
    input logic cs_n_dut,
    input logic [2:0] cid_ref,
    input logic [2:0] cid_dut,
    input logic [5:0] bcw_ref,
    input logic [5:0] bcw_dut,
    input logic [7:0] dca_ref,
    input logic [7:0] dca_dut
  );
    string report;
    report = $sformatf(
      "\n" +
      "========== CA Field Comparison Report ==========\n" +
      "Overall Status: %s\n" +
      "Matching Fields: %0d/5\n" +
      "---\n" +
      "CA Field:        %s (Ref: 0x%03h, DUT: 0x%03h)\n" +
      "CS_n Field:      %s (Ref: 0x%01h, DUT: 0x%01h)\n" +
      "CID Field:       %s (Ref: 0x%01h, DUT: 0x%01h)\n" +
      "BCW Field:       %s (Ref: 0x%02h, DUT: 0x%02h)\n" +
      "DCA Field:       %s (Ref: 0x%02h, DUT: 0x%02h)\n" +
      "===============================================\n",
      result.all_match ? "PASS" : "FAIL",
      result.match_count,
      result.ca_match ? "MATCH" : "MISMATCH", ca_ref, ca_dut,
      result.cs_n_match ? "MATCH" : "MISMATCH", cs_n_ref, cs_n_dut,
      result.cid_match ? "MATCH" : "MISMATCH", cid_ref, cid_dut,
      result.bcw_match ? "MATCH" : "MISMATCH", bcw_ref, bcw_dut,
      result.dca_match ? "MATCH" : "MISMATCH", dca_ref, dca_dut
    );
    return report;
  endfunction

  //============================================================================
  // Function: is_field_mismatch()
  // Description: Checks if a specific field has a mismatch based on bitmask.
  // Parameters:
  //   - result: Comparison result structure
  //   - field_index: Field index (0=CA, 1=CS_n, 2=CID, 3=BCW, 4=DCA)
  // Returns:
  //   - logic: true if field mismatched, false if matched
  // Usage:
  //   if (is_field_mismatch(result, 3)) begin
  //     $error("BCW field mismatch detected");
  //   end
  //============================================================================
  function automatic logic is_field_mismatch(
    input ca_field_comparison_result_t result,
    input integer field_index
  );
    if (field_index < 0 || field_index > 4) return 1'b0;
    return result.mismatch_fields[field_index];
  endfunction

endpackage : ca_field_compare_pkg

`endif // __CA_FIELD_COMPARE_FN_SV__

//==============================================================================
// Usage Examples for Scoreboard Integration
//==============================================================================
// Example 1: Basic field comparison in scoreboard
// -----------
//  ca_field_comparison_result_t result;
//  result = compare_ca_fields(expected_ca, actual_ca,
//                             expected_cs_n, actual_cs_n,
//                             expected_cid, actual_cid,
//                             expected_bcw, actual_bcw,
//                             expected_dca, actual_dca);
//
//  if (!result.all_match) begin
//    $error("CA packet validation failed");
//    $display("%s", get_comparison_report(result, ...));
//  end
//
// Example 2: Selective field validation
// -----------
//  if (!result.ca_match) begin
//    $error("Command/Address field mismatch");
//  end
//  if (!result.bcw_match) begin
//    $warning("Burst Chop Width mismatch - check timing");
//  end
//
// Example 3: Match counter tracking
// -----------
//  if (result.match_count < 5) begin
//    $error("Partial match - %0d fields match, %0d fields mismatch",
//           result.match_count, 5 - result.match_count);
//  end
//
//==============================================================================
