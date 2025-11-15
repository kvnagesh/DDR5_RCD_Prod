#!/bin/bash
mkdir -p netlists

echo "Generating netlists for all working modules..."

SUCCESS_MODULES="
bcw_mgr
clock_gate
cmd_latency_ctrl
dcalcsr_calibrator
dck_phase_calib
dram_init_ctrl
duty_cycle_corr
error_log_reg
i3c_hotjoin_addr_clkstr
i3c_timing_arbitration
jitter_mon_report
pll_init_lock
qck_controller
reg_err_detect
reg_init_ctrl
register_map
sec_reg_lock
"

for module in $SUCCESS_MODULES; do
    echo "Synthesizing $module..."
    cat > netlists/${module}_synth.ys << EOF
read_verilog -sv rtl/${module}.sv
hierarchy -check -top $module
proc; opt; fsm; opt; memory; opt
techmap; opt
abc -g AND,OR,XOR; opt
clean
write_verilog netlists/${module}_netlist.v
write_json netlists/${module}.json
stat -top $module
EOF
    
    yosys netlists/${module}_synth.ys > netlists/${module}_synth.log 2>&1
    
    if [ $? -eq 0 ]; then
        echo "✅ $module synthesized successfully"
    else
        echo "❌ $module synthesis failed"
    fi
done

echo ""
echo "Synthesis complete. Netlists in ./netlists/"
ls -lh netlists/*.v | wc -l | xargs echo "Total netlists generated:"
