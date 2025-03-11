//componenta nu a fost adaptata acestui mediu de verificare
`ifndef __input_driver_agent_buton
`define __input_driver_agent_buton

//driverul va prelua date de tip "tranzactie", pe care le va trimite DUT-ului, conform protocolul de comunicatie de pe interfata
class driver_agent_buton extends uvm_driver #(tranzactie_agent_buton);
  
  //driverul se adauga in baza de date UVM
  `uvm_component_utils (driver_agent_buton)
  
  //este declarata interfata pe care driverul va trimite datele
  virtual button_interface_dut interfata_driverului_pentru_buton;
  
  //constructorul clasei
  function new(string name = "driver_agent_buton", uvm_component parent = null);
    //este apelat constructorul clasei parinte
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    //este apelata mai intai functia build_phase din clasa parinte
    super.build_phase(phase);
    if (!uvm_config_db#(virtual button_interface_dut)::get(this, "", "button_interface_dut", interfata_driverului_pentru_buton))begin
      `uvm_fatal("DRIVER_AGENT_Buton", "Nu s-a putut accesa button_interface_dut")
    end
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    forever begin
      `uvm_info("DRIVER_AGENT_Buton", $sformatf("Se asteapta o tranzactie de la sequencer"), UVM_LOW)
      seq_item_port.get_next_item(req);
      `uvm_info("DRIVER_AGENT_Buton", $sformatf("S-a primit o tranzactie de la sequencer"), UVM_LOW)
      trimiterea_tranzactiei(req);
      `uvm_info("DRIVER_AGENT_Buton", $sformatf("Tranzactia a fost transmisa pe interfata"), UVM_LOW)
      seq_item_port.item_done();
    end
  endtask
   
  task trimiterea_tranzactiei(tranzactie_agent_buton informatia_de_transmis);
    $timeformat(-9, 2, " ns", 20);//cand se va afisa in consola timpul, folosind directiva %t timpul va fi afisat in nanosecunde (-9), cu 2 zecimale, iar dupa valoare se va afisa abrevierea " ns"
    @(posedge interfata_driverului_pentru_buton.clk_i);//transmiterea datelor se sincronizeaza cu ceasul de sistem
    interfata_driverului_pentru_buton.enable_i = informatia_de_transmis.enable;
    
    
    `ifdef DEBUG
    $display("DRIVER_AGENT_Buton, dupa transmisie; [T=%0t]", $realtime);
    `endif;
  endtask
  
endclass
`endif