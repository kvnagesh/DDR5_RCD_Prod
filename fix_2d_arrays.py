#!/usr/bin/env python3
import re
import sys

def fix_2d_port_arrays(content):
    # Pattern: logic [W-1:0] name[D]
    # Replace with: logic [D*W-1:0] name (flattened)
    # This is for port declarations only
    
    # Match patterns like: input logic [3:0] cfg_div_ratio[8]
    pattern = r'((?:input|output)\s+logic\s+)(\[\d+:\d+\])\s+(\w+)(\[\d+\])(\s*,?)'
    
    def replace_func(match):
        prefix = match.group(1)  # 'input logic '
        packed_dim = match.group(2)  # '[3:0]'
        name = match.group(3)  # 'cfg_div_ratio'
        unpacked_dim = match.group(4)  # '[8]'
        suffix = match.group(5)  # ',' or ''
        
        # Extract dimensions
        packed_match = re.search(r'\[(\d+):(\d+)\]', packed_dim)
        unpacked_match = re.search(r'\[(\d+)\]', unpacked_dim)
        
        if packed_match and unpacked_match:
            packed_high = int(packed_match.group(1))
            packed_low = int(packed_match.group(2))
            array_size = int(unpacked_match.group(1))
            
            # Calculate flattened width
            element_width = packed_high - packed_low + 1
            total_width = element_width * array_size
            
            # Create flattened declaration
            new_decl = f"{prefix}[{total_width-1}:0] {name}{suffix}"
            print(f"  Fixed: {name}{packed_dim}{unpacked_dim} -> [{total_width-1}:0] {name}", file=sys.stderr)
            return new_decl
        
        return match.group(0)
    
    return re.sub(pattern, replace_func, content)

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print("Usage: fix_2d_arrays.py input.sv output.sv")
        sys.exit(1)
    
    with open(sys.argv[1], 'r') as f:
        content = f.read()
    
    result = fix_2d_port_arrays(content)
    
    with open(sys.argv[2], 'w') as f:
        f.write(result)
    
    print(f"Fixed {sys.argv[1]} -> {sys.argv[2]}", file=sys.stderr)
