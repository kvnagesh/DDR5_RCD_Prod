#!/usr/bin/env python3
"""Automated RTL Syntax Fixer for Yosys Compatibility"""

import re
import os
import glob
from pathlib import Path

def fix_file(filepath):
    """Fix common Yosys compatibility issues in a single file"""
    with open(filepath, 'r') as f:
        content = f.read()
    
    original_content = content
    changes = []
    
    # Fix 1: Convert always_comb to always @(*)
    if 'always_comb' in content:
        content = re.sub(r'always_comb\s*begin', 'always @(*) begin', content)
        changes.append("always_comb -> always @(*)")
    
    # Fix 2: Convert always_ff to always @(posedge/negedge)
    if 'always_ff' in content:
        # This is more complex, skip for now
        changes.append("always_ff found (manual review needed)")
    
    # Fix 3: Remove inline comments from port declarations  
    lines = content.split('\n')
    fixed_lines = []
    for line in lines:
        # If line has port declaration with inline comment
        if re.search(r'(input|output|inout).*//.*[,)]', line):
            # Move comment to previous line
            line = re.sub(r'(\s*)//(.*)([,)])', r'\3  // \2', line)
            changes.append("moved inline comment")
        fixed_lines.append(line)
    content = '\n'.join(fixed_lines)
    
    # Fix 4: Expand simple parameters in port declarations
    # This is complex and file-specific, skip for automated fix
    
    # Only write if changes were made
    if content != original_content:
        backup_path = filepath + '.bak'
        # Create backup
        with open(backup_path, 'w') as f:
            f.write(original_content)
        # Write fixed file
        with open(filepath, 'w') as f:
            f.write(content)
        return True, changes
    
    return False, changes

def main():
    print("DDR5 RCD RTL Automated Syntax Fixer")
    print("="*50)
    print()
    
    rtl_files = glob.glob('rtl/**/*.sv', recursive=True)
    print(f"Found {len(rtl_files)} SystemVerilog files")
    print()
    
    fixed_count = 0
    for filepath in rtl_files:
        modified, changes = fix_file(filepath)
        if modified:
            fixed_count += 1
            print(f"✓ Fixed: {filepath}")
            for change in changes:
                print(f"  - {change}")
    
    print()
    print(f"Summary: Modified {fixed_count}/{len(rtl_files)} files")
    print(f"Backups created with .bak extension")
    print()
    print("Note: Some issues may require manual review")
    print("Check for:")
    print("  - Parameterized arrays")
    print("  - Complex 2D array declarations")
    print("  - SystemVerilog-specific constructs")

if __name__ == '__main__':
    main()
