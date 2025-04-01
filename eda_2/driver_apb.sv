`ifndef __INPUT_DRIVER_APB
`define __INPUT_DRIVER_APB

class driver_apb extends uvm_driver #(tranzactie_apb);
  
  `uvm_component_utils(driver_apb)
  
  virtual interfata_apb interfata_driverului_pentru_apb;
  
  function new(string name = "driver_apb", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual interfata_apb)::get(this, "", "interfata_apb", interfata_driverului_pentru_apb)) begin
      `uvm_fatal("DRIVER_APB", "Nu s-a putut accesa interfata_apb")
    end
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    forever begin
      `uvm_info("DRIVER_APB", "Se asteapta o tranzactie de la sequencer", UVM_LOW)
      seq_item_port.get_next_item(req);
      `uvm_info("DRIVER_APB", "S-a primit o tranzactie de la sequencer", UVM_LOW)
      trimiterea_tranzactiei(req);
      `uvm_info("DRIVER_APB", "Tranzactia a fost transmisa pe interfata", UVM_LOW)
      seq_item_port.item_done();
    end
  endtask
  
  task trimiterea_tranzactiei(tranzactie_apb informatia_de_transmis);
    $timeformat(-9, 2, " ns", 20);
    @(posedge interfata_driverului_pentru_apb.clk_i);
    interfata_driverului_pentru_apb.paddr = informatia_de_transmis.address;
    interfata_driverului_pentru_apb.pwdata = informatia_de_transmis.data;
    interfata_driverului_pentru_apb.pwrite = informatia_de_transmis.write;
    
    `ifdef DEBUG
    $display("DRIVER_APB, dupa transmisie; [T=%0t]", $realtime);
    `endif;
  endtask
  
endclass
`endif
