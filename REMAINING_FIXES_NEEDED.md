# Remaining 18 Modules - Synthesis Fix Guide

## Issue Identification

All 18 remaining modules fail synthesis due to **Yosys limitation with SystemVerilog syntax**:

**Root Cause:** Yosys 0.33 cannot parse:
1. **2D packed arrays in port declarations** (e.g., `output logic [N-1:0][M-1:0] signal`)
2. **Parameterized port widths** parsed before parameter definitions

## Example Error

```systemverilog
// ca_distributor.sv:36 - FAILS
module ca_distributor #(
    parameter int CA_WIDTH = 7,
    parameter int NUM_SUBCHANNELS = 2
)(
    input  logic [CA_WIDTH-1:0] ca_in,  // This line causes error
    output logic [NUM_SUBCHANNELS-1:0][CA_WIDTH-1:0] ca_out  // 2D array - major issue
);
```

**Yosys Error:** `syntax error, unexpected '['`

## Failed Modules List

1. **ca_distributor** (CRITICAL - main datapath)
2. cdc_gray_sync  
3. crc5_calc
4. ecc_enc_dec
5. ecc_err_type_ctrl
6. ecc_logic
7. error_inject_ctrl
8. error_thresh_mon
9. i3c_fsm_hdr_ibi
10. i3c_slave_if
11. parity_check
12. qca_gate
13. reg_readback_chk
14. shadow_reg_sync
15. ssc_clk_mod
16. timing_check_agg
17-18. (2 additional modules from the 45 total)

## Solutions (In Order of Preference)

### Option 1: RTL Modification (Recommended)

**Approach:** Restructure port declarations to be Yosys-compatible

**For 2D Arrays:**
```systemverilog
// BEFORE (fails):
output logic [NUM_SUBCHANNELS-1:0][CA_WIDTH-1:0] ca_out

// AFTER (works):
output logic [(NUM_SUBCHANNELS*CA_WIDTH)-1:0] ca_out_flat
// Then inside module:
logic [NUM_SUBCHANNELS-1:0][CA_WIDTH-1:0] ca_out;
assign ca_out_flat = ca_out;  // Flatten for output
```

**For Parameterized Widths:**
```systemverilog
// BEFORE (fails in some cases):
module my_mod #(parameter WIDTH = 8)(
    input logic [WIDTH-1:0] data
);

// AFTER (always works):
module my_mod(
    input logic [7:0] data  // Use actual value
);
    localparam WIDTH = 8;
```

### Option 2: Synthesis Wrappers

Create wrapper modules with fixed-width ports:

```systemverilog
// ca_distributor_synth_wrapper.sv
module ca_distributor_synth_wrapper(
    input  logic [6:0] ca_in,
    output logic [13:0] ca_out_flat  // 2 channels * 7 bits
);
    ca_distributor #(
        .CA_WIDTH(7),
        .NUM_SUBCHANNELS(2)
    ) u_ca_dist (
        .ca_in(ca_in),
        .ca_out({ca_out_flat[13:7], ca_out_flat[6:0]})
    );
endmodule
```

### Option 3: Use Verilator Pre-processing

Verilator can handle these constructs and output Yosys-compatible Verilog:

```bash
verilator --lint-only -Wno-all rtl/ca_distributor.sv
verilator -E rtl/ca_distributor.sv > ca_distributor_preprocessed.v
yosys -p "read_verilog ca_distributor_preprocessed.v; ..."
```

### Option 4: Upgrade to Newer Yosys

Yosys development versions may have better SystemVerilog support:
```bash
# Build latest Yosys from source
git clone https://github.com/YosysHQ/yosys.git
cd yosys && make -j$(nproc) && sudo make install
```

## Recommended Action Plan

### Phase 1: Quick Wins (1-2 hours)
1. Try Verilator preprocessing on all 18 modules
2. Test if preprocessed versions synthesize
3. If successful, automate for all failing modules

### Phase 2: Wrapper Approach (2-4 hours)  
1. Create synthesis wrappers for critical modules (ca_distributor, ecc_*)
2. Use default parameter values from specifications
3. Synthesize wrappers instead of original modules

### Phase 3: RTL Refactoring (1-2 days)
1. Modify RTL files to use flattened arrays
2. Keep original files as *_original.sv
3. Create synthesis-specific versions
4. Update automation scripts

## Automation Script Template

```bash
#!/bin/bash
# fix_and_synthesize_remaining.sh

FAILED_MODULES="ca_distributor cdc_gray_sync crc5_calc..."

for module in $FAILED_MODULES; do
    echo "Processing $module..."
    
    # Try Verilator preprocessing
    verilator -E rtl/${module}.sv > rtl/${module}_prep.v 2>/dev/null
    
    if [ $? -eq 0 ]; then
        # Synthesize preprocessed version
        yosys -p "read_verilog rtl/${module}_prep.v; \
                 hierarchy -check -top $module; \
                 synth; \
                 write_verilog netlists/${module}_netlist.v"
    fi
done
```

## Critical Module Priority

**Must-fix for functional design:**
1. **ca_distributor** - Command/Address distribution (core datapath)
2. **ecc_enc_dec** - Error correction (data integrity)
3. **cdc_gray_sync** - Clock domain crossing (reliability)

**Nice-to-have:**
4. i3c_slave_if - I3C interface
5. All others - supporting functions

## Estimated Effort

- **Verilator approach:** 1-2 hours (if it works)
- **Wrapper approach:** 4-8 hours (reliable)
- **RTL modification:** 1-2 days (permanent solution)

## Current Status

- ✅ 17/45 modules synthesized (38%)
- ❌ 18/45 modules need fixes (40%)
- ❓ 10/45 modules status unknown (22%)

**Next Action:** Try Verilator preprocessing approach first as it's fastest.

