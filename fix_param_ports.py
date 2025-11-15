#!/usr/bin/env python3
import re
import sys

def expand_parameters(filename):
    with open(filename, 'r') as f:
        content = f.read()
    
    # Extract parameter values
    params = {}
    param_pattern = r'parameter\s+(?:int|logic)?\s*(\w+)\s*=\s*([\d\'hbdxo]+)'
    for match in re.finditer(param_pattern, content):
        params[match.group(1)] = match.group(2)
    
    print(f"Found parameters: {params}", file=sys.stderr)
    
    # Replace parameter usage in port declarations
    # Replace [PARAM-1:0] with actual values
    for param, value in params.items():
        # Handle [PARAM-1:0]
        content = re.sub(rf'\[{param}-1:0\]', f'[{int(value)-1}:0]', content)
        # Handle [PARAM:0]
        content = re.sub(rf'\[{param}:0\]', f'[{value}:0]', content)
        # Handle other array patterns
        content = re.sub(rf'\[{param}\]', f'[{value}]', content)
    
    return content

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print("Usage: fix_param_ports.py input.sv output.sv")
        sys.exit(1)
    
    result = expand_parameters(sys.argv[1])
    with open(sys.argv[2], 'w') as f:
        f.write(result)
    print(f"Fixed {sys.argv[1]} -> {sys.argv[2]}", file=sys.stderr)
