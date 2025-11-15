#!/bin/bash
# DDR5 RCD Complete RTL-to-GDSII Automation Script
# Execute this on local machine with Docker + OpenLane installed

set -e  # Exit on error

echo "=================================================="
echo "DDR5 RCD RTL-to-GDSII Production Flow"
echo "Production-Grade Open-Source EDA Demonstration"
echo "=================================================="
echo ""

# Configuration
DESIGN_NAME="ddr5_rcd_ca_datapath"
TOP_MODULE="ca_distributor"
CLOCK_PERIOD="0.625"  # 1600 MHz
DIE_SIZE="1000"        # 1mm x 1mm
UTIL="65"              # 65% utilization

echo "Step 1: Environment Check"
echo "----------------------------"
command -v yosys >/dev/null 2>&1 || { echo "ERROR: Yosys not found"; exit 1; }
command -v docker >/dev/null 2>&1 || { echo "ERROR: Docker not found"; exit 1; }
echo "✓ Yosys found: $(yosys -V | head -1)"
echo "✓ Docker found: $(docker --version)"
echo ""

echo "Step 2: RTL File Collection"
echo "----------------------------"
cat > ${DESIGN_NAME}_files.f << 'FILELIST'
rtl/ca_distributor.sv
rtl/src/data_path/ca_packetizer.sv
rtl/src/data_path/subchannel_controller.sv
rtl/clock_gate.sv
rtl/cdc_gray_sync.sv
rtl/src/data_path/signal_router.sv
rtl/reg_init_ctrl.sv
FILELIST

echo "Files to synthesize:"
cat ${DESIGN_NAME}_files.f
echo ""

echo "Step 3: Yosys Synthesis"
echo "----------------------------"
cat > ${DESIGN_NAME}_synth.ys << 'YOSYS'
# DDR5 RCD CA Datapath Synthesis Script

# Read all RTL files
read_verilog -sv -I rtl/ -I rtl/src -I rtl/src/data_path \\
    rtl/ca_distributor.sv \\
    rtl/src/data_path/ca_packetizer.sv \\
    rtl/src/data_path/subchannel_controller.sv \\
    rtl/clock_gate.sv \\
    rtl/cdc_gray_sync.sv

# Elaborate design
hierarchy -check -top ca_distributor

# High-level synthesis
proc
opt
fsm
opt
memory
opt

# Technology mapping
techmap
opt

# Synthesis
synth -top ca_distributor

# Optimization
abc -g AND
opt_clean

# Statistics
stat

# Write outputs
write_verilog -noattr ${DESIGN_NAME}_netlist.v
write_json ${DESIGN_NAME}_netlist.json

YOSYS

echo "Running Yosys synthesis..."
yosys ${DESIGN_NAME}_synth.ys 2>&1 | tee ${DESIGN_NAME}_synth.log
echo "✓ Synthesis complete"
echo ""

echo "Step 4: Synthesis Analysis"
echo "----------------------------"
echo "Gate count:"
grep "Number of cells:" ${DESIGN_NAME}_synth.log || echo "Check log file"
echo "Netlist size:"
ls -lh ${DESIGN_NAME}_netlist.v
echo ""

echo "Step 5: OpenLane Configuration"
echo "----------------------------"
mkdir -p openlane_tool/designs/${DESIGN_NAME}/src
cp ${DESIGN_NAME}_netlist.v openlane_tool/designs/${DESIGN_NAME}/src/

cat > openlane_tool/designs/${DESIGN_NAME}/config.tcl << CONF
# OpenLane Configuration for DDR5 RCD CA Datapath
# Production-grade configuration

set ::env(DESIGN_NAME) "${TOP_MODULE}"

# Source files
set ::env(VERILOG_FILES) "\$::env(DESIGN_DIR)/src/${DESIGN_NAME}_netlist.v"
set ::env(DESIGN_IS_CORE) 0

# Clocking - DDR5 1600MHz operation
set ::env(CLOCK_PERIOD) "${CLOCK_PERIOD}"
set ::env(CLOCK_PORT) "qck_clk"

# Floorplan
set ::env(DIE_AREA) "0 0 ${DIE_SIZE} ${DIE_SIZE}"
set ::env(FP_CORE_UTIL) ${UTIL}
set ::env(PL_TARGET_DENSITY) 0.70

# PDK Configuration
set ::env(PDK) "sky130A"
set ::env(STD_CELL_LIBRARY) "sky130_fd_sc_hd"

# CTS Configuration  
set ::env(CLOCK_TREE_SYNTH) 1
set ::env(CTS_TARGET_SKEW) 100
set ::env(CTS_TOLERANCE) 25

# Optimization
set ::env(SYNTH_STRATEGY) "DELAY 1"
set ::env(SYNTH_MAX_FANOUT) 6
set ::env(PL_RESIZER_TIMING_OPTIMIZATIONS) 1
set ::env(GLB_RESIZER_TIMING_OPTIMIZATIONS) 1

# Routing
set ::env(ROUTING_CORES) 4
set ::env(GLB_RT_MAXLAYER) 5

CONF

echo "✓ OpenLane configuration created"
echo ""

echo "Step 6: Execute OpenLane P&R"
echo "----------------------------"
echo "This will take 1-3 hours depending on design complexity"
echo ""
echo "Command to execute:"
echo "  cd openlane_tool"
echo "  make mount"
echo "  ./flow.tcl -design ${DESIGN_NAME} -tag prod_run_$(date +%Y%m%d_%H%M)"
echo ""

read -p "Execute OpenLane now? (y/n) " -n 1 -r
echo
if [[ $REPLY =~ ^[Yy]$ ]]
then
    cd openlane_tool
    echo "Mounting Docker container..."
    make mount <<'DOCKER'
./flow.tcl -design ${DESIGN_NAME} -tag prod_run_$(date +%Y%m%d_%H%M)
exit
DOCKER
    
    echo ""
    echo "=================================================="
    echo "OpenLane P&R Complete!"
    echo "=================================================="
    echo ""
    echo "Results location:"
    echo "  designs/${DESIGN_NAME}/runs/prod_run_*/"
    echo ""
    echo "Key outputs:"
    echo "  - GDSII: results/final/gds/${TOP_MODULE}.gds"
    echo "  - DEF: results/final/def/${TOP_MODULE}.def"
    echo "  - Timing: reports/final/timing.rpt"
    echo "  - Power: reports/final/power.rpt"
    echo "  - Area: reports/final/area.rpt"
    echo ""
else
    echo "Skipping P&R execution."
    echo "Run manually when ready."
fi

echo ""
echo "=================================================="
echo "DDR5 RCD Flow Complete!"
echo "=================================================="
echo ""
echo "Summary:"
echo "  ✓ RTL Files: Collected"
echo "  ✓ Synthesis: Complete (Yosys)"
echo "  ✓ Netlist: Generated"
echo "  ✓ OpenLane: Configured"
if [[ $REPLY =~ ^[Yy]$ ]]; then
    echo "  ✓ P&R: Complete"
    echo "  ✓ GDSII: Generated"
else
    echo "  ⏳ P&R: Ready to execute"
fi
echo ""

