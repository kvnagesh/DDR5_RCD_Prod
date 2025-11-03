# DDR5_RCD_Prod
Production-grade SystemVerilog implementation for DDR5 RCD (Registering Clock Driver) Buffer Chip - RDIMM/MRDIMM up to 12800 MT/s

## RTL Files

The following SystemVerilog modules are located in the `rtl/` directory:

- **ca_distributor.sv** - CA (Command/Address) distributor module for routing signals from host to DRAM devices
- **clock_gate.sv** - Clock gating cell with latch-based and flip-flop-based implementations for power management
- **ecc_logic.sv** - ECC (Error Correction Code) datapath implementing SECDED (stub/test interface)
- **i3c_slave_if.sv** - I3C slave interface for RCD configuration and control (stub/test interface)
