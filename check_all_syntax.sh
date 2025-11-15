#!/bin/bash
echo "DDR5 RCD Design - Comprehensive Syntax Check"
echo "============================================="
echo ""

# Find all SystemVerilog files
find rtl/ -name '*.sv' > all_rtl_files.txt
file_count=$(wc -l < all_rtl_files.txt)
echo "Total RTL files found: $file_count"
echo ""

echo "Checking for common syntax issues..."
echo ""

# Check 1: Parameterized port declarations
echo "[1/6] Checking parameterized ports..."
grep -n "input.*\[.*PARAM" rtl/**/*.sv 2>/dev/null | head -5
echo ""

# Check 2: 2D unpacked arrays in ports  
echo "[2/6] Checking 2D arrays in ports..."
grep -n "logic.*\[.*\].*\[.*\]" rtl/**/*.sv 2>/dev/null | grep -E "(input|output)" | head -5
echo ""

# Check 3: Inline comments in sensitive locations
echo "[3/6] Checking inline comments..."
grep -n "//.*);" rtl/**/*.sv 2>/dev/null | head -5
echo ""

# Check 4: Always_comb/always_ff (Yosys compatibility)
echo "[4/6] Checking always_comb/always_ff..."
grep -n "always_comb\|always_ff" rtl/**/*.sv 2>/dev/null | wc -l
echo ""

# Check 5: Interface usage
echo "[5/6] Checking interface declarations..."
grep -n "^interface" rtl/**/*.sv 2>/dev/null | wc -l
echo ""

# Check 6: Assert statements
echo "[6/6] Checking assertions..."
grep -n "assert" rtl/**/*.sv 2>/dev/null | wc -l

