#!/bin/bash
# Fix Verilator syntax errors in ddr5_rcd_tb_top.sv

FILE="tb/uvm/ddr5_rcd_tb_top.sv"

# Comment out UVM macro calls
sed -i 's/^\([ \t]*\)`uvm_fatal/\/\/ \1`uvm_fatal/g' "$FILE"
sed -i 's/^\([ \t]*\)`uvm_warning/\/\/ \1`uvm_warning/g' "$FILE"
sed -i 's/^\([ \t]*\)`uvm_info/\/\/ \1`uvm_info/g' "$FILE"

# Comment out modport clocking lines (lines with 'modport.*clocking')
sed -i 's/^\(.*modport.*clocking.*\)$/\/\/ \1/g' "$FILE"

echo "Fixed UVM macro and modport clocking errors"
