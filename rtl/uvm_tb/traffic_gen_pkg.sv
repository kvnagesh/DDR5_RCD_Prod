//!
// traffic_gen_pkg.sv - Constrained-Random and Directed Traffic Generator Package
// Part of DDR5 RCD Verification Testbench
//
// This package provides comprehensive traffic generation capabilities for DDR5 RCD interfaces
// including command/address, data, and control signals with parameterized reusability.
//

package traffic_gen_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  //=============================================================================
  // Configuration and Parameters
  //=============================================================================
  
  // Traffic generation modes
  typedef enum {
    TRAFFIC_MODE_DIRECTED,
    TRAFFIC_MODE_RANDOM,
    TRAFFIC_MODE_CONSTRAINED_RANDOM,
    TRAFFIC_MODE_BURST,
    TRAFFIC_MODE_STRESS
  } traffic_mode_t;

  // Command types for RCD
  typedef enum {
    CMD_ACT,      // Activate
    CMD_READ,     // Read
    CMD_WRITE,    // Write
    CMD_PRECHARGE,// Precharge
    CMD_REFRESH,  // Refresh
    CMD_MRS,      // Mode Register Set
    CMD_PDE,      // Power-Down Entry
    CMD_PDX,      // Power-Down Exit
    CMD_SRE,      // Self-Refresh Entry
    CMD_SRX       // Self-Refresh Exit
  } ddr5_cmd_t;

  //=============================================================================
  // Traffic Sequence Items
  //=============================================================================

  // Basic command/address transaction
  class ca_transaction extends uvm_object;
    `uvm_object_utils(ca_transaction)
    
    rand logic [16:0] address;      // Row/Col address
    rand logic [2:0]  bank_group;   // Bank group
    rand logic [1:0]  bank;         // Bank address
    rand ddr5_cmd_t   command;      // Command type
    rand logic [3:0]  chip_select;  // Chip select
    logic [127:0]     timestamp;
    
    constraint addr_valid {
      address inside {[0 : (1 << 17)-1]};
      bank_group inside {[0:7]};
      bank inside {[0:3]};
    }
    
    constraint cmd_distribution {
      command dist {
        CMD_READ    := 30,
        CMD_WRITE   := 30,
        CMD_ACT     := 15,
        CMD_PRECHARGE := 15,
        CMD_REFRESH := 5,
        CMD_MRS     := 3,
        CMD_PDE     := 1,
        CMD_SRE     := 1
      };
    }

    function new(string name = "");
      super.new(name);
    endfunction

    function string convert2string();
      return $sformatf("CA_TXN: cmd=%s, addr=0x%05x, bank=%d, bg=%d, cs=0x%x",
        command.name(), address, bank, bank_group, chip_select);
    endfunction
  endclass

  // Data transaction
  class data_transaction extends uvm_object;
    `uvm_object_utils(data_transaction)
    
    rand logic [127:0] data_payload;
    rand logic [15:0]  data_mask;
    rand logic         read_write;  // 0=read, 1=write
    logic [63:0]      burst_length;
    
    constraint data_mask_valid {
      data_mask != 0;  // At least some bytes enabled
    }
    
    constraint burst_len {
      burst_length inside {[4:16]};
    }

    function new(string name = "");
      super.new(name);
    endfunction

    function string convert2string();
      return $sformatf("DATA_TXN: rw=%s, mask=0x%04x, data=0x%032x",
        read_write ? "WRITE" : "READ", data_mask, data_payload);
    endfunction
  endclass

  //=============================================================================
  // Sequence Generators
  //=============================================================================

  // Random command/address sequence
  class random_ca_sequence extends uvm_sequence #(ca_transaction);
    `uvm_object_utils(random_ca_sequence)
    
    rand int unsigned num_transactions = 100;
    constraint num_trans_valid { num_transactions inside {[10:1000]}; }
    
    function new(string name = "");
      super.new(name);
    endfunction

    task body();
      ca_transaction item;
      `uvm_info(get_type_name(), $sformatf("Starting random CA sequence with %0d transactions",
        num_transactions), UVM_MEDIUM)
      
      repeat(num_transactions) begin
        item = ca_transaction::type_id::create(.name("ca_item"), .contxt(get_full_name()));
        if (!item.randomize()) begin
          `uvm_error(get_type_name(), "Failed to randomize CA transaction")
        end
        item.timestamp = $time();
        start_item(item);
        finish_item(item);
      end
    endtask
  endclass

  // Burst traffic sequence (memory access patterns)
  class burst_traffic_sequence extends uvm_sequence #(ca_transaction);
    `uvm_object_utils(burst_traffic_sequence)
    
    rand int unsigned burst_count = 50;
    rand int unsigned burst_size = 8;
    constraint burst_valid {
      burst_count inside {[10:100]};
      burst_size inside {[4:32]};
    }
    
    function new(string name = "");
      super.new(name);
    endfunction

    task body();
      ca_transaction item;
      logic [16:0] base_address;
      
      `uvm_info(get_type_name(), $sformatf("Starting burst sequence: %0d bursts of %0d txns",
        burst_count, burst_size), UVM_MEDIUM)
      
      repeat(burst_count) begin
        base_address = $urandom() & 17'hFFFF;
        repeat(burst_size) begin
          item = ca_transaction::type_id::create(.name("burst_item"), .contxt(get_full_name()));
          if (!item.randomize() with {
            address == (base_address + $urandom_range(0, burst_size-1));
            command dist {
              CMD_READ  := 50,
              CMD_WRITE := 50
            };
          }) begin
            `uvm_error(get_type_name(), "Failed to randomize burst item")
          end
          item.timestamp = $time();
          start_item(item);
          finish_item(item);
        end
      end
    endtask
  endclass

  // Stress pattern sequence - maximize traffic and race conditions
  class stress_pattern_sequence extends uvm_sequence #(ca_transaction);
    `uvm_object_utils(stress_pattern_sequence)
    
    rand int unsigned duration_cycles = 10000;
    constraint dur_valid { duration_cycles inside {[1000:100000]}; }
    
    function new(string name = "");
      super.new(name);
    endfunction

    task body();
      ca_transaction item;
      int txn_count = 0;
      
      `uvm_info(get_type_name(), "Starting stress pattern generation", UVM_MEDIUM)
      
      while (txn_count < duration_cycles) begin
        item = ca_transaction::type_id::create(.name("stress_item"), .contxt(get_full_name()));
        if (!item.randomize() with {
          command dist {
            CMD_READ      := 35,
            CMD_WRITE     := 35,
            CMD_ACT       := 15,
            CMD_PRECHARGE := 10,
            CMD_REFRESH   := 5
          };
        }) begin
          `uvm_error(get_type_name(), "Failed to randomize stress item")
        end
        item.timestamp = $time();
        start_item(item);
        finish_item(item);
        txn_count++;
      end
      
      `uvm_info(get_type_name(), $sformatf("Completed %0d stress transactions", txn_count), UVM_MEDIUM)
    endtask
  endclass

  // Power-aware traffic sequence
  class power_aware_sequence extends uvm_sequence #(ca_transaction);
    `uvm_object_utils(power_aware_sequence)
    
    rand int unsigned idle_periods = 10;
    rand int unsigned idle_duration = 100;
    constraint power_valid {
      idle_periods inside {[5:50]};
      idle_duration inside {[10:1000]};
    }
    
    function new(string name = "");
      super.new(name);
    endfunction

    task body();
      ca_transaction item;
      int period;
      
      `uvm_info(get_type_name(), "Starting power-aware sequence", UVM_MEDIUM)
      
      repeat(idle_periods) begin
        // Activity burst
        repeat(20) begin
          item = ca_transaction::type_id::create(.name("pwr_item"), .contxt(get_full_name()));
          if (!item.randomize()) begin
            `uvm_error(get_type_name(), "Failed to randomize power-aware item")
          end
          item.timestamp = $time();
          start_item(item);
          finish_item(item);
        end
        
        // Idle period for power-down
        period = idle_duration * $urandom_range(1, 10);
        #(period);
        
        // Power-down command
        item = ca_transaction::type_id::create(.name("pwr_item"), .contxt(get_full_name()));
        item.randomize() with {command == CMD_PDE;};
        item.timestamp = $time();
        start_item(item);
        finish_item(item);
      end
    endtask
  endclass

  //=============================================================================
  // Traffic Generator Base Class
  //=============================================================================

  class traffic_generator extends uvm_component;
    `uvm_component_utils(traffic_generator)
    
    traffic_mode_t mode;
    uvm_sequence_library lib;
    uvm_sequencer #(ca_transaction) sequencer;
    
    int unsigned seed;
    bit enable_logging = 1;
    
    function new(string name, uvm_component parent);
      super.new(name, parent);
      mode = TRAFFIC_MODE_RANDOM;
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      lib = new(get_name());
    endfunction

    task run_phase(uvm_phase phase);
      uvm_sequence base_seq;
      
      `uvm_info(get_type_name(), $sformatf("Running traffic generator in mode: %s",
        mode.name()), UVM_MEDIUM)
      
      case(mode)
        TRAFFIC_MODE_RANDOM: begin
          base_seq = random_ca_sequence::type_id::create("random_seq");
          base_seq.start(sequencer);
        end
        
        TRAFFIC_MODE_BURST: begin
          base_seq = burst_traffic_sequence::type_id::create("burst_seq");
          base_seq.start(sequencer);
        end
        
        TRAFFIC_MODE_STRESS: begin
          base_seq = stress_pattern_sequence::type_id::create("stress_seq");
          base_seq.start(sequencer);
        end
        
        TRAFFIC_MODE_DIRECTED: begin
          `uvm_info(get_type_name(), "Directed traffic mode - handled by specific test", UVM_MEDIUM)
        end
        
        default: begin
          `uvm_warning(get_type_name(), $sformatf("Unknown traffic mode: %s", mode.name()))
        end
      endcase
    endtask
  endclass

endpackage : traffic_gen_pkg
