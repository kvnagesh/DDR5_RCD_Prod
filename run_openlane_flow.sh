#!/bin/bash
# OpenLane RTL-to-GDSII Flow Execution Script
# Design: qca_qck_gating (DDR5 RCD Clock Gating)
# Target: 800 MHz @ Sky130A

set -e  # Exit on error

echo "========================================"
echo "OpenLane RTL-to-GDSII Flow"
echo "Design: qca_qck_gating"
echo "Target: 800 MHz @ Sky130A PDK"
echo "========================================"
echo ""

# Check if OpenLane is available
if [ ! -d "openlane" ]; then
    echo "ERROR: openlane directory not found"
    echo "Please ensure OpenLane is cloned in the current directory"
    exit 1
fi

# Verify design directory
if [ ! -d "openlane/qca_qck_gating" ]; then
    echo "ERROR: Design directory not found"
    exit 1
fi

if [ ! -f "openlane/qca_qck_gating/config.tcl" ]; then
    echo "ERROR: config.tcl not found"
    exit 1
fi

echo "✅ Design directory: openlane/qca_qck_gating"
echo "✅ Configuration: config.tcl"
echo "✅ Netlist: src/synth_netlist.v"
echo ""

echo "========================================"
echo "NOTE: OpenLane Flow Execution"
echo "========================================"
echo ""
echo "To run the complete OpenLane flow, execute:"
echo ""
echo "  cd openlane"
echo "  make mount"
echo ""
echo "Then inside the Docker container:"
echo "  ./flow.tcl -design qca_qck_gating"
echo ""
echo "Alternative: Interactive mode"
echo "  ./flow.tcl -interactive"
echo "  package require openlane 0.9"
echo "  prep -design qca_qck_gating"
echo "  run_synthesis"
echo "  run_floorplan"
echo "  run_placement"
echo "  run_cts"
echo "  run_routing"
echo "  run_magic"
echo "  run_magic_spice_export"
echo "  run_magic_drc"
echo "  run_lvs"
echo "  run_antenna_check"
echo ""
echo "Expected Runtime: 40-80 minutes"
echo "========================================"
echo ""

