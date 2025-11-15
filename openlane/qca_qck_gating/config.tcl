# OpenLane Configuration for DDR5 RCD QCA/QCK Clock Gating Module
# Design: qca_qck_gating
# Target: Sky130A PDK
# Frequency: 800 MHz (1.25ns period)

set ::env(DESIGN_NAME) "qca_qck_gating"

# Verilog Files
set ::env(VERILOG_FILES) [glob $::env(DESIGN_DIR)/src/*.v]

# Clock Configuration - 800 MHz DDR5
set ::env(CLOCK_PORT) "qca_clk"
set ::env(CLOCK_PERIOD) "1.25"  ; # 800 MHz

# Die Area - Sized for ~540 gates with headroom
set ::env(DIE_AREA) "0 0 300 300"  ; # 300µm x 300µm

# Floorplan Configuration
set ::env(FP_CORE_UTIL) 50         ; # 50% utilization for timing closure
set ::env(PL_TARGET_DENSITY) 0.60  ; # Target density for placement
set ::env(FP_PDN_VPITCH) 25
set ::env(FP_PDN_HPITCH) 25

# PDK Configuration
set ::env(PDK) "sky130A"
set ::env(STD_CELL_LIBRARY) "sky130_fd_sc_hd"  ; # High-density cells

# Synthesis Strategy - Already done with Yosys
set ::env(SYNTH_STRATEGY) "DELAY 0"  ; # Prioritize timing
set ::env(SYNTH_BUFFERING) 1
set ::env(SYNTH_SIZING) 1

# Placement Configuration  
set ::env(PL_RESIZER_DESIGN_OPTIMIZATIONS) 1
set ::env(PL_RESIZER_TIMING_OPTIMIZATIONS) 1
set ::env(PL_RESIZER_BUFFER_INPUT_PORTS) 1
set ::env(PL_RESIZER_BUFFER_OUTPUT_PORTS) 1

# CTS (Clock Tree Synthesis) Configuration
set ::env(CTS_TARGET_SKEW) 50      ; # Target 50ps skew
set ::env(CTS_TOLERANCE) 25        ; # 25ps tolerance
set ::env(CTS_CLK_BUFFER_LIST) "sky130_fd_sc_hd__clkbuf_4 sky130_fd_sc_hd__clkbuf_8"

# Routing Configuration
set ::env(ROUTING_CORES) 4
set ::env(GLB_RESIZER_TIMING_OPTIMIZATIONS) 1

# DRC/LVS
set ::env(RUN_KLAYOUT_XOR) 0       ; # Skip XOR check initially
set ::env(RUN_KLAYOUT_DRC) 1       ; # Run DRC
set ::env(RUN_MAGIC_DRC) 1

# Power Analysis
set ::env(RUN_CVC) 0               ; # Skip circuit validity check initially

# Timing Analysis
set ::env(STA_WRITE_LIB) 1
set ::env(RUN_SPEF_EXTRACTION) 1

# Output
set ::env(GENERATE_FINAL_SUMMARY_REPORT) 1

