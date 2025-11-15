#!/bin/bash
# Comprehensive Verilator syntax fix script

FILE="tb/uvm/ddr5_rcd_tb_top.sv"

echo "Applying all Verilator fixes..."

# 1. Comment out UVM macro calls
sed -i 's/^\([ \t]*\)`uvm_fatal/\/\/ \1`uvm_fatal/g' "$FILE"
sed -i 's/^\([ \t]*\)`uvm_warning/\/\/ \1`uvm_warning/g' "$FILE"
sed -i 's/^\([ \t]*\)`uvm_info/\/\/ \1`uvm_info/g' "$FILE"

# 2. Comment out modport clocking lines
sed -i 's/^\(.*modport.*clocking.*\)$/\/\/ \1/g' "$FILE"

# 3. Comment out UVM package import
sed -i 's/^\([ \t]*import uvm_pkg::.*\)$/\/\/ \1/' "$FILE"

# 4. Comment out UVM include
sed -i 's/^\([ \t]*`include.*uvm_macros.*\)$/\/\/ \1/' "$FILE"

# 5. Comment out ddr5_rcd_pkg import
sed -i 's/^\([ \t]*import ddr5_rcd_pkg::.*\)$/\/\/ \1/' "$FILE"

# 6. Comment out UVM class instantiations
sed -i 's/^\([ \t]*uvm_cmdline_processor.*\)$/\/\/ \1/' "$FILE"
sed -i 's/^\([ \t]*clp = uvm_cmdline_processor.*\)$/\/\/ \1/' "$FILE"

# 7. Comment out uvm_config_db calls
sed -i 's/^\(.*uvm_config_db.*\)$/\/\/ \1/' "$FILE"

echo "All fixes applied successfully!"
