`ifndef __INPUT_DRIVER_I2C
`define __INPUT_DRIVER_I2C

class driver_i2c extends uvm_driver #(tranzactie_i2c);
  
  `uvm_component_utils(driver_i2c)
  
  virtual interfata_i2c interfata_driverului_pentru_i2c;
  
  function new(string name = "driver_i2c", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual interfata_i2c)::get(this, "", "interfata_i2c", interfata_driverului_pentru_i2c)) begin
      `uvm_fatal("DRIVER_I2C", "Nu s-a putut accesa interfata_i2c")
    end
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    forever begin
      `uvm_info("DRIVER_I2C", "Se asteapta o tranzactie de la sequencer", UVM_LOW)
      seq_item_port.get_next_item(req);
      `uvm_info("DRIVER_I2C", "S-a primit o tranzactie de la sequencer", UVM_LOW)
      trimiterea_tranzactiei(req);
      `uvm_info("DRIVER_I2C", "Tranzactia a fost transmisa pe interfata", UVM_LOW)
      seq_item_port.item_done();
    end
  endtask
  
  task trimiterea_tranzactiei(tranzactie_i2c informatia_de_transmis);
    $timeformat(-9, 2, " ns", 20);
    @(posedge interfata_driverului_pentru_i2c.clk_i);
    interfata_driverului_pentru_i2c.sda_i = informatia_de_transmis.data;
    interfata_driverului_pentru_i2c.scl_i = informatia_de_transmis.clock;
    
    `ifdef DEBUG
    $display("DRIVER_I2C, dupa transmisie; [T=%0t]", $realtime);
    `endif;
  endtask
  
endclass
`endif
