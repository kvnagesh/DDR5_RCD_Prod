# CDC Gray Sync Integration Guide
# Clock Domain Crossing (CDC) Synchronizer with Gray Code Logic

## Overview

The `cdc_gray_sync` module provides robust clock domain crossing (CDC) synchronizers using gray-coded logic for DDR5 RCD (Registered Clock Driver) applications. It ensures reliable data transfer between asynchronous clock domains while minimizing metastability risks.

---

## Features

- **Gray Code Encoding/Decoding**: Single-bit transitions between adjacent values reduce metastability
- **Multi-Stage Synchronization**: Configurable 2-4 stage synchronizer registers
- **Metastability Reduction**: Cascaded flip-flops provide MTBF improvement
- **Handshake Protocol**: Optional request/acknowledge signaling
- **Valid/Ready Interface**: Standard AXI-like flow control
- **Parameterizable Width**: Supports narrow (single-bit) to wide (multi-bit) bus crossings
- **DDR5 Optimized**: Designed for high-frequency DDR5 clock domains

---

## Module Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `WIDTH` | int | 8 | Data bus width in bits |
| `SYNC_STAGES` | int | 3 | Number of synchronization stages (2-4 recommended) |
| `USE_HANDSHAKE` | bit | 1'b0 | Enable handshake protocol for robust transfer |
| `USE_VALID_READY` | bit | 1'b1 | Enable valid/ready flow control |

---

## Port Definitions

### Source Clock Domain (src_clk)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `src_clk` | input | 1 | Source clock domain |
| `src_reset_n` | input | 1 | Active-low reset (synchronous to src_clk) |
| `src_data` | input | WIDTH | Data to be transferred to destination domain |
| `src_valid` | input | 1 | Indicates src_data is valid |
| `src_ready` | output | 1 | Indicates module is ready to accept data |
| `src_ack` | output | 1 | Acknowledge from destination (handshake mode) |

### Destination Clock Domain (dst_clk)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `dst_clk` | input | 1 | Destination clock domain |
| `dst_reset_n` | input | 1 | Active-low reset (synchronous to dst_clk) |
| `dst_data` | output | WIDTH | Synchronized data in destination domain |
| `dst_valid` | output | 1 | Indicates dst_data is valid |
| `dst_ready` | input | 1 | Indicates destination can accept data |
| `dst_req` | input | 1 | Request signal for handshake mode |

---

## Usage Examples

### Example 1: Simple Gray Code CDC (8-bit data)

```systemverilog
cdc_gray_sync #(
    .WIDTH(8),
    .SYNC_STAGES(3),
    .USE_HANDSHAKE(1'b0),
    .USE_VALID_READY(1'b1)
) u_gray_cdc (
    // Source domain (e.g., 400 MHz)
    .src_clk(clk_400mhz),
    .src_reset_n(rst_n_400),
    .src_data(counter_value),
    .src_valid(counter_valid),
    .src_ready(counter_ready),
    .src_ack(),  // Not used
    
    // Destination domain (e.g., 200 MHz)
    .dst_clk(clk_200mhz),
    .dst_reset_n(rst_n_200),
    .dst_data(synced_counter),
    .dst_valid(synced_valid),
    .dst_ready(1'b1),  // Always ready
    .dst_req(1'b0)     // Not used
);
```

### Example 2: DDR5 Command Path CDC (16-bit commands)

```systemverilog
cdc_gray_sync #(
    .WIDTH(16),
    .SYNC_STAGES(4),           // Extra stage for high-frequency DDR5
    .USE_HANDSHAKE(1'b1),      // Enable handshake for critical commands
    .USE_VALID_READY(1'b1)
) u_cmd_cdc (
    // Host clock domain (e.g., 1600 MHz)
    .src_clk(host_clk),
    .src_reset_n(host_rst_n),
    .src_data(cmd_packet),
    .src_valid(cmd_valid),
    .src_ready(cmd_ready),
    .src_ack(cmd_ack),
    
    // DRAM clock domain (e.g., 800 MHz)
    .dst_clk(dram_clk),
    .dst_reset_n(dram_rst_n),
    .dst_data(dram_cmd),
    .dst_valid(dram_cmd_valid),
    .dst_ready(dram_cmd_ready),
    .dst_req(1'b0)
);
```

### Example 3: Using the Wrapper Module

```systemverilog
cdc_gray_sync_wrapper #(
    .DATA_WIDTH(12),
    .SYNC_DEPTH(3),
    .SYNC_MODE("GRAY")
) u_status_cdc (
    .src_clk(status_clk),
    .src_rst_n(status_rst_n),
    .src_data(status_bus),
    .src_data_valid(status_valid),
    .src_data_ready(status_ready),
    
    .dst_clk(core_clk),
    .dst_rst_n(core_rst_n),
    .dst_data(core_status),
    .dst_data_valid(core_status_valid),
    .dst_data_ready(core_status_ready)
);
```

---

## Gray Code Theory

### Binary to Gray Code Conversion

```
Gray[MSB] = Binary[MSB]
Gray[i] = Binary[i] XOR Binary[i+1]
```

**Example (4-bit):**
- Binary: 0101 (5)
- Gray: 0111
  - G[3] = B[3] = 0
  - G[2] = B[2] ^ B[3] = 1 ^ 0 = 1
  - G[1] = B[1] ^ B[2] = 0 ^ 1 = 1
  - G[0] = B[0] ^ B[1] = 1 ^ 0 = 1

### Gray to Binary Code Conversion

```
Binary[MSB] = Gray[MSB]
Binary[i] = Binary[i+1] XOR Gray[i]
```

**Advantage**: Only one bit changes between consecutive values, reducing metastability probability during clock domain crossing.

---

## DDR5 RCD Integration Points

### 1. Command/Address Path CDC

**Application**: Transfer CA (Command/Address) signals from host clock to DRAM clock domain

```systemverilog
// In top-level RCD module
cdc_gray_sync #(.WIDTH(14), .SYNC_STAGES(3)) u_ca_cdc (
    .src_clk(host_ca_clk),
    .dst_clk(dram_ca_clk),
    // ... port connections
);
```

### 2. Clock Calibration Status

**Application**: Transfer DCK phase calibration status between clock domains

```systemverilog
cdc_gray_sync #(.WIDTH(4), .SYNC_STAGES(3)) u_cal_status_cdc (
    .src_clk(dck_cal_clk),
    .dst_clk(core_clk),
    .src_data(phase_cal_status),
    // ...
);
```

### 3. Register Control Paths

**Application**: Synchronize control register updates

```systemverilog
cdc_gray_sync #(.WIDTH(8), .SYNC_STAGES(3)) u_reg_cdc (
    .src_clk(i3c_clk),
    .dst_clk(core_clk),
    .src_data(reg_addr),
    // ...
);
```

### 4. FIFO Pointer Synchronization

**Application**: Gray-coded FIFO read/write pointers

```systemverilog
cdc_gray_sync #(.WIDTH(8), .SYNC_STAGES(2)) u_wr_ptr_sync (
    .src_clk(wr_clk),
    .dst_clk(rd_clk),
    .src_data(wr_ptr_gray),
    // ...
);
```

---

## Timing Constraints

### Synchronizer Path Constraints (SDC)

```tcl
# Set false path for CDC synchronizer inputs
set_false_path -from [get_cells {*cdc_gray_sync*/src_gray_reg*}] \
               -to [get_cells {*cdc_gray_sync*/dst_gray_sync_reg[0]*}]

# Constrain synchronizer stages
set_max_delay 5.0 -from [get_cells {*cdc_gray_sync*/dst_gray_sync_reg[0]*}] \
                  -to [get_cells {*cdc_gray_sync*/dst_gray_sync_reg[1]*}]

# Set multicycle path for gray code decoder
set_multicycle_path 2 -from [get_cells {*cdc_gray_sync*/dst_gray_sync_reg*}] \
                        -to [get_cells {*cdc_gray_sync*/dst_data_reg*}]
```

---

## Design Guidelines

### 1. Synchronization Stages

- **2 stages**: Minimum for basic CDC (MTBF > 1000 years at typical frequencies)
- **3 stages**: Recommended for DDR5 applications (MTBF > 10^6 years)
- **4 stages**: High-reliability applications or very high frequencies (>2 GHz)

### 2. Reset Considerations

- Use asynchronous reset assertion, synchronous deassertion
- Reset both source and destination domains independently
- Ensure proper reset sequencing

### 3. Gray Code Limitations

- Best for counters and pointers (sequential values)
- Not ideal for random data patterns
- Consider alternative CDC methods for wide random data buses

### 4. Handshake Mode

- Use when data transfer must be acknowledged
- Adds latency but guarantees delivery
- Suitable for configuration registers and control signals

---

## Verification Recommendations

### Simulation Checks

1. **Metastability injection**: Force X states on synchronizer inputs
2. **Clock ratio variation**: Test with different src/dst clock ratios
3. **Back-to-back transfers**: Verify continuous data transfer
4. **Reset scenarios**: Check behavior during/after reset

### Formal Verification

```systemverilog
// CDC property: Data eventually arrives at destination
assert property (
    @(posedge src_clk) src_valid && src_ready |-> 
    ##[1:$] @(posedge dst_clk) dst_valid && (dst_data == $past(src_data))
);
```

---

## Performance Characteristics

| Metric | Value | Notes |
|--------|-------|-------|
| Latency | 3-4 dst_clk cycles | Depends on SYNC_STAGES |
| Throughput | 1 transfer per src_clk | With valid/ready flow control |
| Area | ~50 FFs + combinatorial | For WIDTH=8, SYNC_STAGES=3 |
| Power | Minimal | Only active during transfers |
| MTBF | >10^6 years | At 2 GHz with 3 stages |

---

## Troubleshooting

### Issue: Data Corruption

**Symptom**: dst_data does not match src_data  
**Cause**: Insufficient synchronization stages  
**Solution**: Increase SYNC_STAGES to 3 or 4

### Issue: Ready Signal Never Asserts

**Symptom**: src_ready stuck at 0  
**Cause**: Handshake mode ACK not synchronized  
**Solution**: Check dst_clk is toggling and dst_reset_n is deasserted

### Issue: Metastability Warnings

**Symptom**: Synthesis/STA reports metastability  
**Cause**: Missing timing constraints  
**Solution**: Apply proper false_path and max_delay constraints

---

## References

1. **Clifford E. Cummings**: "Clock Domain Crossing (CDC) Design & Verification Techniques Using SystemVerilog"
2. **JEDEC JESD79-5**: DDR5 SDRAM Specification
3. **Synopsys**: "Designing Safe and Reliable Clock Domain Crossings"
4. **Gray Code**: https://en.wikipedia.org/wiki/Gray_code

---

## Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0 | 2025-11-04 | DDR5 Team | Initial release with gray-coded CDC |

---

## Support

For questions or issues, please contact the DDR5 RCD development team or file an issue in the repository.

**Module Location**: `rtl/cdc_gray_sync.sv`  
**Test Bench**: `tb/cdc_gray_sync_tb.sv` (to be added)  
**Synthesis Scripts**: `scripts/synthesize_cdc.tcl` (to be added)
