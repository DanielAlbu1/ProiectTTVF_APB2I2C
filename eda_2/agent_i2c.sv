`ifndef __agent_i2c
`define __agent_i2c

//se includ dependentele folosite de agent
typedef class monitor_i2c;//aceasta este o pre-definire a tipului de data monitor_agent_semafoare folosita pentru a evita erorile aparute in urma faptului ca monitorul importa colectorul de coverage, si colectorul de coverage importa monitorul; explicatia in engleza: this is a forward type definition used to solve cross dependency between monitor and coverage class
`include "tranzactie_i2c.sv"
`include "driver_i2c.sv"
`include "monitor_i2c.sv"


class agent_i2c extends uvm_agent;
  
  `uvm_component_utils (agent_i2c)//se adauga agentul la baza de date a acestui proiect; de acolo, acelasi agent se va prelua ulterior spre a putea fi folosit
  
  
  //se instantiaza componentele de baza ale agentului: driverul, monitorul si sequencer-ul; driverul si monitorul sunt create de catre noi, pe cand sequencerul se ia direct din biblioteca UVM
  driver_i2c driver_i2c_inst0;
  
  monitor_i2c  monitor_i2c_inst0;
  
  uvm_sequencer #(tranzactie_i2c) sequencer_agent_i2c_inst0;
  
  
  //se declara portul de comunicare al agentului cu scoreboardul/mediul de referinta; prin acest port agentul trimite spre verificare datele preluate de la monitor; a se observa ca intre monitor si agent (practic in interiorul agentului) comunicarea se face la nivel de tranzactie
  uvm_analysis_port #(tranzactie_i2c) de_la_monitor_i2c; //de_la_monitor_agent_semafoare;
  
  
  //se declara un camp in care spunem daca agentul este activ sau pasiv; un agent activ contine in plus, fata de agentul pasiv, driver si sequencer
  local int is_active = 1;  //0 inseamna agent pasiv; 1 inseamna agent activ
  
  
  //se declara constructorul clasei; acesta este un cod standard pentru toate componentele
  function new (string name = "agent_i2c", uvm_component parent = null);
      super.new (name, parent);
    de_la_monitor_i2c = new("de_la_monitor_i2c", this);
  endfunction 
  
  
  //rularea unui mediu de verificare cuprinde mai multe faze; in faza "build", se "asambleaza" agentul, tinandu-se cont daca acesta este activ sau pasiv
  virtual function void build_phase (uvm_phase phase);
    
    //se apeleaza functia build_phase din clasa parinte (uvm_agent)
    super.build_phase(phase);
    
    //atat agentii activi, cat si agentii pasivi au nevoie de un monitor 
    monitor_i2c_inst0 = monitor_senzor::type_id::create ("monitor_i2c_inst0", this);
    // daca agentul este activ, i se adauga atat sequencerul (componenta care aduce datele in agent) cat si driverul (componenta care preia datele de la sequencer si le transmite DUT-ului adaptandu-le protocolului de comunicatie al acestuia)
    if (is_active==1) begin
      sequencer_agent_i2c_inst0 = uvm_sequencer#(tranzactie_i2c)::type_id::create ("sequencer_agent_i2c_inst0", this);
      driver_i2c_inst0 = driver_i2c::type_id::create ("driver_i2c_inst0", this);
    end

  endfunction
  
  
  //rularea unui mediu de verificare cuprinde mai multe faze; in faza "connect", se realizeaza conexiunile intre componente; in cazul agentului, se realizeaza conexiunile intre sub-componentele agentului
  virtual function void connect_phase (uvm_phase phase);
    
    //se apeleaza functia connect_phase din clasa parinte (uvm_agent)
    super.connect_phase(phase);
    
    //se conecteaza portul agentului cu portul de comunicatie al monitorului din agent (monitorul nu poate trimite date in exterior decat prin intermediul agentului din care face parte)
    de_la_monitor_i2c = monitor_i2c_inst0.port_date_monitor_senzor;
    
	// driverul primeste date de la sequencer, pentru a le transmite DUT-ului; daca agentul este activ, trebuie realizata si conexiunea intre sequencer si driver 
    if (is_active==1)begin
      driver_i2c_inst0.seq_item_port.connect (sequencer_agent_i2c_inst0.seq_item_export);
    end
    
  endfunction
  
endclass

`endif