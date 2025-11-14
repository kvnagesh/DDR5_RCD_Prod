# OpenLane Flow Setup for DDR5 RCD Design

## Configuration Created
Location: `/workspaces/DDR5_RCD_Prod/openlane/config.json`

## Design Parameters
- **Design Name**: ddr5_rcd
- **Clock Period**: 1.25ns (800 MHz target)
- **Die Area**: 3000 x 3000 µm²
- **Target Density**: 55%
- **Core Utilization**: 45%

## OpenLane Flow Stages

### 1. Synthesis (Yosys)
- Logic synthesis from RTL
- Technology mapping
- Optimization

### 2. Floorplanning
- Die/core area definition
- I/O placement
- Power grid generation

### 3. Placement
- Global placement
- Detailed placement
- Optimization

### 4. CTS (Clock Tree Synthesis)
- Clock distribution network
- Skew optimization

### 5. Routing
- Global routing
- Detailed routing

### 6. Physical Verification
- DRC (Design Rule Check)
- LVS (Layout vs Schematic)

### 7. GDSII Generation
- Final layout output

## Requirements for Full Flow
- Docker (for OpenLane container)
- PDK (Sky130 or GF180MCU)
- 8-16GB RAM minimum
- 4-8 hours runtime for complex designs

## Next Steps
1. Install Docker
2. Pull OpenLane Docker image
3. Setup PDK
4. Run: `make mount`
5. Inside container: `./flow.tcl -design ddr5_rcd`
