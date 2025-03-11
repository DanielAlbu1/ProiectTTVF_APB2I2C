`ifndef __senzor_driver
`define __senzor_driver

//driverul va prelua date de tip "tranzactie", pe care le va trimite DUT-ului, conform protocolul de comunicatie de pe interfata
class driver_agent_senzor extends uvm_driver #(tranzactie_senzor);
  
  //driverul se adauga in baza de date UVM
  `uvm_component_utils (driver_agent_senzor)
  
  //este declarata interfata pe care driverul va trimite datele
  virtual sensor_interface_dut interfata_driverului_pentru_senzor;
  
  //constructorul clasei
  function new(string name = "driver_agent_senzor", uvm_component parent = null);
    //este apelat constructorul clasei parinte
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    //este apelata mai intai functia build_phase din clasa parinte
    super.build_phase(phase);
    if (!uvm_config_db#(virtual sensor_interface_dut)::get(this, "", "sensor_interface_dut", interfata_driverului_pentru_senzor))begin
      `uvm_fatal("DRIVER_AGENT_SENZOR", "Nu s-a putut accesa interfata_senzorului")
    end
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    forever begin
      `uvm_info("DRIVER_AGENT_SENZOR", $sformatf("Se asteapta o tranzactie de la sequencer"), UVM_LOW)
      seq_item_port.get_next_item(req);
      `uvm_info("DRIVER_AGENT_SENZOR", $sformatf("S-a primit o tranzactie de la sequencer"), UVM_LOW)
      trimiterea_tranzactiei(req);
      `uvm_info("DRIVER_AGENT_SENZOR", $sformatf("Tranzactia a fost transmisa pe interfata"), UVM_LOW)
      seq_item_port.item_done();
    end
  endtask
  
  task trimiterea_tranzactiei(tranzactie_senzor informatia_de_transmis);
    $timeformat(-9, 2, " ns", 20);//cand se va afisa in consola timpul, folosind directiva %t timpul va fi afisat in nanosecunde (-9), cu 2 zecimale, iar dupa valoare se va afisa abrevierea " ns"
    
	//wait ready
    $display("%0t DRIVER_AGENT_SENZOR: wait ready", $time());
    wait(interfata_driverului_pentru_senzor.ready_o)
    $display("%0t DRIVER_AGENT_SENZOR: READY arrived", $time());
    @(posedge interfata_driverului_pentru_senzor.clk_i);
    interfata_driverului_pentru_senzor.valid_i = 'b1;
  //  @(posedge interfata_driverului_pentru_senzor.clk_i);//transmiterea datelor se sincronizeaza cu ceasul de sistem
    interfata_driverului_pentru_senzor.temperature_i = informatia_de_transmis.temperature;
    interfata_driverului_pentru_senzor.humidity_i = informatia_de_transmis.humidity;
    interfata_driverului_pentru_senzor.luminous_intensity_i = informatia_de_transmis.luminous_intensity;
	 @(posedge interfata_driverului_pentru_senzor.clk_i);
    interfata_driverului_pentru_senzor.valid_i = 'b0;
    
    `ifdef DEBUG
    $display("DRIVER_AGENT_SENZOR, dupa transmisie; [T=%0t]", $realtime);
    `endif;
  endtask
  
endclass
`endif