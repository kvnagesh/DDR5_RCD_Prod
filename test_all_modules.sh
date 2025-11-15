#!/bin/bash
echo "Testing synthesis for all RTL modules..."
echo "" > synthesis_results.txt

for file in rtl/*.sv; do
    module=$(basename $file .sv)
    echo "Testing $module..."
    
    cat > temp_synth.ys << EOF
read_verilog -sv $file
hierarchy -check -top $module
proc; opt
techmap; opt
abc -g AND,OR,XOR; opt
clean
stat
EOF
    
    if yosys temp_synth.ys > /dev/null 2>&1; then
        echo "✅ $module - SUCCESS" | tee -a synthesis_results.txt
    else
        echo "❌ $module - FAILED" | tee -a synthesis_results.txt
    fi
done

echo ""
echo "Summary:"
grep "SUCCESS" synthesis_results.txt | wc -l | xargs echo "Successful:"
grep "FAILED" synthesis_results.txt | wc -l | xargs echo "Failed:"
