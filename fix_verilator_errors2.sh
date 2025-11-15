#!/bin/bash
FILE="tb/uvm/ddr5_rcd_tb_top.sv"

# Comment out uvm_pkg import
sed -i 's/^\([ \t]*import uvm_pkg::.*\)$/\/\/ \1/' "$FILE"

# Comment out UVM include
sed -i 's/^\([ \t]*`include.*uvm_macros.*\)$/\/\/ \1/' "$FILE"

# Comment out UVM class instantiations
sed -i 's/^\([ \t]*uvm_cmdline_processor.*\)$/\/\/ \1/' "$FILE"
sed -i 's/^\([ \t]*clp = uvm_cmdline_processor.*\)$/\/\/ \1/' "$FILE"

echo "Fixed UVM imports and class instantiations"
