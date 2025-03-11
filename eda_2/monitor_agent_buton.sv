//componenta nu a fost adaptata acestui mediu de verificare
`ifndef __output_monitor_agent_buton
`define __output_monitor_agent_buton
`include "tranzactie_agent_buton.sv"

//`include "tranzactie_semafoare.sv"

class monitor_agent_buton extends uvm_monitor;
  
  //monitorul se adauga in baza de date UVM
  `uvm_component_utils (monitor_agent_buton) 
  
  //se declara colectorul de coverage care va inregistra valorile semnalelor de pe interfata citite de monitor
  coverage_agent_buton colector_coverage_buton_inst;
  
  //este creat portul prin care monitorul trimite spre exterior (la noi, informatia este accesata de scoreboard), prin intermediul agentului, tranzactiile extrase din traficul de pe interfata
  uvm_analysis_port #(tranzactie_agent_buton) port_date_monitor_buton;
  
  //declaratia interfetei de unde monitorul isi colecteaza datele
  virtual button_interface_dut interfata_monitor_buton;
  
  tranzactie_agent_buton starea_preluata_a_butonului, aux_tr_buton;
  
  
  //constructorul clasei
  function new(string name = "monitor_agent_buton", uvm_component parent = null);
    
    //prima data se apeleaza constructorul clasei parinte
    super.new(name, parent);
    
    //se creeaza portul prin care monitorul trimite in exterior, prin intermediul agentului, datele pe care le-a cules din traficul de pe interfata
    port_date_monitor_buton = new("port_date_monitor_buton",this);
    
    //se creeaza colectorul de coverage (la creare, se apeleaza constructorul colectorului de coverage)
    colector_coverage_buton_inst = coverage_agent_buton::type_id::create ("colector_coverage_buton_inst", this);
    
    
    //se creeaza obiectul (tranzactia) in care se vor retine datele colectate de pe interfata la fiecare tact de ceas
    starea_preluata_a_butonului = tranzactie_agent_buton::type_id::create("date_noi");
    
    aux_tr_buton = tranzactie_agent_buton::type_id::create("datee_noi");
  endfunction
  
  
  //se preia din baza de date interfata la care se va conecta monitorul pentru a citi date, si se "leaga" la interfata pe care deja monitorul o contine
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
      if (!uvm_config_db#(virtual button_interface_dut)::get(this, "", "button_interface_dut", interfata_monitor_buton))
        `uvm_fatal("MONITOR_AGENT_Buton", "Nu s-a putut accesa interfata montorului")
  endfunction
        
  
  
  virtual function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    
    //in faza UVM "connect", se face conexiunea intre pointerul catre monitor din instanta colectorului de coverage a acestui monitor si monitorul insusi 
	colector_coverage_buton_inst.p_monitor = this;
    
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    
    forever begin
      
      //preluarea datelor de pe interfata se face la fiecare front negativ de ceas
      @(negedge interfata_monitor_buton.clk_i);
            
      
      //preiau datele de pe interfata de iesire a DUT-ului (button_interface_dut)
      starea_preluata_a_butonului.enable = interfata_monitor_buton.enable_i;
      
      aux_tr_buton = starea_preluata_a_butonului.copy();
      
       //tranzactia cuprinzand datele culese de pe interfata se pune la dispozitie pe portul monitorului, daca modulul nu este in reset
     port_date_monitor_buton.write(aux_tr_buton); 
      
      //se inregistreaza valorile de pe cele doua semnale de iesire
      colector_coverage_buton_inst.buton_cg.sample();
      
    end//forever begin
  endtask
  
endclass: monitor_agent_buton

`endif