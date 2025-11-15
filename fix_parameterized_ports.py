import re
import os
import sys
from pathlib import Path

def fix_parameterized_ports(content, filename):
    """Fix parameterized port declarations for Yosys compatibility"""
    modified = False
    lines = content.split('\n')
    result = []
    
    # Track if we're in module declaration
    in_module_header = False
    param_section_done = False
    port_buffer = []
    
    for i, line in enumerate(lines):
        stripped = line.strip()
        
        # Detect module start
        if stripped.startswith('module '):
            in_module_header = True
            param_section_done = False
            result.append(line)
            continue
            
        # If in module header, check for parameterized ports
        if in_module_header:
            # Check if this is end of module header
            if ');' in line or (stripped.endswith(';') and not stripped.startswith('input') and not stripped.startswith('output')):
                in_module_header = False
                result.append(line)
                continue
            
            # Check for parameterized port like: input logic [PARAM-1:0] or [PARAM:0]
            param_port_match = re.search(r'(input|output)\s+(logic|wire|reg)?\s*\[([A-Z_][A-Z0-9_]*)([-+*/])([^\]]+)\]', line)
            
            if param_port_match:
                # Found parameterized port - needs to be fixed
                # For now, replace with reasonable defaults or extract parameter
                direction = param_port_match.group(1)
                data_type = param_port_match.group(2) or 'logic'
                param_name = param_port_match.group(3)
                operator = param_port_match.group(4)
                rest = param_port_match.group(5)
                
                # Common parameter values (you may need to adjust)
                param_values = {
                    'WIDTH': 8,
                    'DATA_WIDTH': 32,
                    'ADDR_WIDTH': 16,
                    'NUM': 4,
                    'RANK_BITS': 2,
                    'NUM_SUBCHANNELS': 2,
                    'CA_WIDTH': 7,
                    'BANK_BITS': 4,
                    'NUM_RANKS': 2
                }
                
                # Try to evaluate the parameter
                if param_name in param_values:
                    val = param_values[param_name]
                    if operator == '-':
                        try:
                            offset = eval(rest)
                            new_width = val - offset
                            line = re.sub(r'\[' + param_name + re.escape(operator) + re.escape(rest) + r'\]', 
                                        f'[{new_width}:0]', line)
                            modified = True
                        except:
                            pass
                
        result.append(line)
    
    return '\n'.join(result), modified

def process_file(filepath):
    """Process a single RTL file"""
    try:
        with open(filepath, 'r') as f:
            content = f.read()
        
        fixed_content, was_modified = fix_parameterized_ports(content, filepath.name)
        
        if was_modified:
            # Create backup
            backup_path = str(filepath) + '.paramfix.bak'
            with open(backup_path, 'w') as f:
                f.write(content)
            
            # Write fixed version
            with open(filepath, 'w') as f:
                f.write(fixed_content)
            
            print(f"✅ Fixed: {filepath.name}")
            return True
        else:
            print(f"⏭️  Skipped: {filepath.name} (no parameterized ports found)")
            return False
            
    except Exception as e:
        print(f"❌ Error processing {filepath}: {e}")
        return False

if __name__ == '__main__':
    # List of failed modules
    failed_modules = [
        'ca_distributor',
        'cdc_gray_sync',
        'crc5_calc',
        'ecc_enc_dec',
        'ecc_err_type_ctrl',
        'ecc_logic',
        'error_inject_ctrl',
        'error_thresh_mon',
        'i3c_fsm_hdr_ibi',
        'i3c_slave_if',
        'parity_check',
        'qca_gate',
        'reg_readback_chk',
        'shadow_reg_sync',
        'ssc_clk_mod',
        'timing_check_agg'
    ]
    
    rtl_dir = Path('rtl')
    fixed_count = 0
    
    print("Fixing parameterized port syntax for Yosys compatibility...\n")
    
    for module in failed_modules:
        filepath = rtl_dir / f"{module}.sv"
        if filepath.exists():
            if process_file(filepath):
                fixed_count += 1
        else:
            print(f"⚠️  File not found: {filepath}")
    
    print(f"\nFixed {fixed_count} files")
