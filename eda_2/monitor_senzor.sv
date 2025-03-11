`ifndef __senzor_monitor
`define __senzor_monitor
//`include "tranzactie_semafoare.sv"

class monitor_senzor extends uvm_monitor;
  
  //monitorul se adauga in baza de date UVM
  `uvm_component_utils (monitor_senzor) 
  
  //se declara colectorul de coverage care va inregistra valorile semnalelor de pe interfata citite de monitor
  coverage_senzor colector_coverage_senzor; 
  
  //este creat portul prin care monitorul trimite spre exterior (la noi, informatia este accesata de scoreboard), prin intermediul agentului, tranzactiile extrase din traficul de pe interfata
  uvm_analysis_port #(tranzactie_senzor) port_date_monitor_senzor;
  
  //declaratia interfetei de unde monitorul isi colecteaza datele
  //virtual interfata_senzor interfata_monitor_senzor;
  virtual sensor_interface_dut interfata_monitor_senzor;
  
  tranzactie_senzor starea_preluata_a_senzorului, aux_tr_senzor;
  
  //constructorul clasei
  function new(string name = "monitor_senzor", uvm_component parent = null);
    
    //prima data se apeleaza constructorul clasei parinte
    super.new(name, parent);
    
    
    
    //se creeaza portul prin care monitorul trimite in exterior, prin intermediul agentului, datele pe care le-a cules din traficul de pe interfata
    port_date_monitor_senzor = new("port_date_monitor_senzor",this);
    
    //se creeaza colectorul de coverage (la creare, se apeleaza constructorul colectorului de coverage)
    
    colector_coverage_senzor = coverage_senzor::type_id::create ("colector_coverage_senzor", this);
    
    
    //se creeaza obiectul (tranzactia) in care se vor retine datele colectate de pe interfata la fiecare tact de ceas
    starea_preluata_a_senzorului = tranzactie_senzor::type_id::create("date_noi");
    
    aux_tr_senzor = tranzactie_senzor::type_id::create("datee_noi");
  endfunction
  
  
  //se preia din baza de date interfata la care se va conecta monitorul pentru a citi date, si se "leaga" la interfata pe care deja monitorul o contine
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    if (!uvm_config_db#(virtual sensor_interface_dut)::get(this, "", "sensor_interface_dut", interfata_monitor_senzor))
        `uvm_fatal("MONITOR_SENZOR", "Nu s-a putut accesa interfata monitorului")
  endfunction
        
  
  
  virtual function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    
    //in faza UVM "connect", se face conexiunea intre pointerul catre monitor din instanta colectorului de coverage a acestui monitor si monitorul insusi 
	colector_coverage_senzor.p_monitor = this;
    
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    
    forever begin
      
      
        
      
      //!!!!sa astept ca datele sa fie valide
      wait(interfata_monitor_senzor.valid_i); 
      //vreau sa citesc semnalul valid_i doar pe fronturile descrescatoare de ceas
      @(negedge interfata_monitor_senzor.clk_i); 
      //preiau datele de pe interfata de iesire a DUT-ului (interfata_semafoare)
      starea_preluata_a_senzorului.temperature = interfata_monitor_senzor.temperature_i;
      starea_preluata_a_senzorului.humidity = interfata_monitor_senzor.humidity_i;
	  starea_preluata_a_senzorului.luminous_intensity = interfata_monitor_senzor.luminous_intensity_i;

      aux_tr_senzor = starea_preluata_a_senzorului.copy();//nu vreau sa folosesc pointerul starea_preluata_a_senzorului pentru a trimite datele, deoarece continutul acestuia se schimba, iar scoreboardul va citi alte date 
      
       //tranzactia cuprinzand datele culese de pe interfata se pune la dispozitie pe portul monitorului, daca modulul nu este in reset
      port_date_monitor_senzor.write(aux_tr_senzor); 
      `uvm_info("MONITOR_SENZOR", $sformatf("S-a receptionat tranzactia cu informatiile:"), UVM_NONE)
      aux_tr_senzor.afiseaza_informatia_tranzactiei();
	  
      //se inregistreaza valorile de pe cele doua semnale de iesire
      colector_coverage_senzor.stari_senzor_cg.sample();
      
	  @(negedge interfata_monitor_senzor.clk_i); //acest wait il adaug deoarece uneori o tranzactie este interpretata a fi doua tranzactii identice back to back (validul este citit ca fiind 1 pe doua fronturi consecutive de ceas); in implementarea curenta nu se poate sa vina doua tranzactii back to back
      
      
    end//forever begin
  endtask
  
  
endclass: monitor_senzor

`endif