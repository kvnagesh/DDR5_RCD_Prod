# Yosys Upgrade Guide - Option 4 Implementation

## Current Situation

- **Current Version:** Yosys 0.33 (git sha1 2584903a060)
- **Limitation:** Cannot parse 2D packed arrays in SystemVerilog port declarations
- **Impact:** 18/45 modules fail synthesis

## Yosys Upgrade Process (Est. 30-45 minutes)

### Step 1: Install Build Dependencies (~5-10 min)
```bash
sudo apt-get update && sudo apt-get install -y \\
    build-essential clang bison flex \\
    libreadline-dev gawk tcl-dev libffi-dev git \\
    graphviz xdot pkg-config python3 \\
    libboost-system-dev libboost-python-dev \\
    libboost-filesystem-dev zlib1g-dev
```

### Step 2: Clone and Build Latest Yosys (~20-30 min)
```bash
cd ~
git clone https://github.com/YosysHQ/yosys.git
cd yosys

# Build with optimizations
make config-gcc
make -j$(nproc)

# Install (requires sudo in Codespaces)
sudo make install

# Verify
yosys -V
```

### Step 3: Test with Failed Modules
```bash
cd /workspaces/DDR5_RCD_Prod

# Test ca_distributor
yosys -p "read_verilog -sv rtl/ca_distributor.sv; \\
         hierarchy -check -top ca_distributor; \\
         synth; stat"
```

## Expected Improvements

**Latest Yosys** (as of Nov 2025) has improved:
- Better SystemVerilog 2D array support
- Enhanced parameter handling in ports
- More robust parsing of complex constructs

## Success Criteria

After upgrade, these should synthesize:
- ca_distributor (critical datapath)
- cdc_gray_sync
- ecc_* modules
- All remaining 18 modules

## Alternative if Upgrade Doesn't Work

If latest Yosys still has issues:

### Option A: sv2v Converter
```bash
# Install sv2v (SystemVerilog to Verilog converter)
curl -sSL https://github.com/zachjs/sv2v/releases/download/v0.0.11/sv2v-Linux.zip -o sv2v.zip
unzip sv2v.zip && chmod +x sv2v
sudo mv sv2v /usr/local/bin/

# Convert modules
sv2v rtl/ca_distributor.sv > rtl/ca_distributor_v.v
yosys -p "read_verilog rtl/ca_distributor_v.v; synth; ..."
```

### Option B: Synthesis Wrappers (Most Reliable)
Create fixed-width wrappers as documented in REMAINING_FIXES_NEEDED.md

## Recommendation

**For Codespaces:** Option A (sv2v) or Option B (wrappers) is faster than full Yosys rebuild

**For Local Machine:** Yosys upgrade is worthwhile for long-term benefit

## Quick sv2v Approach (5-10 minutes)

This is the fastest solution:

```bash
#!/bin/bash
# quick_fix_sv2v.sh

wget https://github.com/zachjs/sv2v/releases/download/v0.0.11/sv2v-Linux -O sv2v
chmod +x sv2v

FAILED=("ca_distributor" "cdc_gray_sync" "crc5_calc" ...)

for mod in "${FAILED[@]}"; do
    ./sv2v rtl/${mod}.sv > rtl/${mod}_converted.v
    
    yosys -p "read_verilog rtl/${mod}_converted.v; \\
             hierarchy -check -top $mod; \\
             synth; \\
             write_verilog netlists/${mod}_netlist.v; \\
             stat" > netlists/${mod}_synth.log 2>&1
done
```

