`ifndef __monitor_agent_actuator
`define __monitor_agent_actuator
//`include "tranzactie_semafoare.sv"

class monitor_agent_actuator extends uvm_monitor;
  
  //monitorul se adauga in baza de date UVM
  `uvm_component_utils (monitor_agent_actuator) 
  
  //se declara colectorul de coverage care va inregistra valorile semnalelor de pe interfata citite de monitor
  coverage_agent_actuator coverage_actuator_inst; //colector_coverage_semafoare;
  
  //este creat portul prin care monitorul trimite spre exterior (la noi, informatia este accesata de scoreboard), prin intermediul agentului, tranzactiile extrase din traficul de pe interfata
  uvm_analysis_port #(tranzactie_agent_actuator) port_date_monitor_actuator;
  
  //declaratia interfetei de unde monitorul isi colecteaza datele
  virtual actuator_interface_dut interfata_monitor_actuator;
  
  tranzactie_agent_actuator starea_preluata_a_actuatorului, aux_tr_actuator;
  
  //constructorul clasei
  function new(string name = "monitor_agent_actuator", uvm_component parent = null);
    
    //prima data se apeleaza constructorul clasei parinte
    super.new(name, parent);
    
    //se creeaza portul prin care monitorul trimite in exterior, prin intermediul agentului, datele pe care le-a cules din traficul de pe interfata
    port_date_monitor_actuator = new("port_date_monitor_actuator",this);
    
    //se creeaza colectorul de coverage (la creare, se apeleaza constructorul colectorului de coverage)
   coverage_actuator_inst = coverage_agent_actuator::type_id::create ("coverage_actuator_inst", this);
    
    
    //se creeaza obiectul (tranzactia) in care se vor retine datele colectate de pe interfata la fiecare tact de ceas
    starea_preluata_a_actuatorului = tranzactie_agent_actuator::type_id::create("date_noi");
    
    aux_tr_actuator = tranzactie_agent_actuator::type_id::create("datee_noi"); // folosim acest obiect de fiecare data cand transmitem datele pe portul de write pentru a nu lucra cu valoarea pointerului starea_preluata_a_actuatorului care se poate schimba pana cand aceasta este citita de catre scoreboard
  endfunction
  
  
  //se preia din baza de date interfata la care se va conecta monitorul pentru a citi date, si se "leaga" la interfata pe care deja monitorul o contine
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    if (!uvm_config_db#(virtual actuator_interface_dut)::get(this, "", "actuator_interface_dut", interfata_monitor_actuator))
      `uvm_fatal("MONITOR_AGENT_ACTUATOR", "Nu s-a putut accesa interfata monitorului")
  endfunction
        
  
  
  virtual function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    
    //in faza UVM "connect", se face conexiunea intre pointerul catre monitor din instanta colectorului de coverage a acestui monitor si monitorul insusi 
	coverage_actuator_inst.p_monitor = this;
    
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    
    forever begin
      
      //preluarea datelor de pe interfata se face la fiecare front negativ de ceas
      @(negedge interfata_monitor_actuator.clk_i);
      
      //intarzii citirea datelor cu un tact, sa nu citesc iesirile DUT-ului inainte ca acesta sa nu primeasca valori pe intrari
     // repeat(2)@(negedge interfata_monitor_actuator.clk);
      
      
      //preiau datele de pe interfata de iesire a DUT-ului (interfata_semafoare)
    starea_preluata_a_actuatorului.Heat_i =  interfata_monitor_actuator.heat_o;
      starea_preluata_a_actuatorului.AC_i =  interfata_monitor_actuator.AC_o;
      starea_preluata_a_actuatorului.Blinds_i =  interfata_monitor_actuator.blinds_o;
      starea_preluata_a_actuatorului.Dehumidifier_i =  interfata_monitor_actuator.dehumidifier_o;
      
     
      aux_tr_actuator = starea_preluata_a_actuatorului.copy();//se inregistreaza valorile de pe cele doua semnale de iesire
      coverage_actuator_inst.actuator_cg.sample();
      
      //tranzactia cuprinzand datele culese de pe interfata se pune la dispozitie pe portul monitorului, daca modulul nu este in reset
      port_date_monitor_actuator.write( aux_tr_actuator); 
    //  `uvm_info("MONITOR_AGENT_SEMAFOARE", $sformatf("S-a receptionat tranzactia cu informatiile:"), UVM_NONE)
      //starea_preluata_a_semafoarelor.afiseaza_informatia_tranzactiei();
    end//forever begin
  endtask
endclass: monitor_agent_actuator

`endif