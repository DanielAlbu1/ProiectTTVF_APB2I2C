`ifndef __tx_line_agent_buton
`define __tx_line_agent_buton

typedef class monitor_agent_buton;

//se includ dependentele folosite de agent
`include "tranzactie_agent_buton.sv"
`include "coverage_agent_buton.sv"
`include "driver_agent_buton.sv"
`include "monitor_agent_buton.sv"

class agent_buton extends uvm_agent;
  
  `uvm_component_utils (agent_buton)//se adauga agentul la baza de date a acestui proiect; de acolo, acelasi agent se va prelua ulterior spre a putea fi folosit
  
  
  //se instantiaza componentele de baza ale agentului: driverul, monitorul si sequencer-ul; driverul si monitorul sunt create de noi, pe cand sequencerul se ia direct din biblioteca UVM
  driver_agent_buton driver_agent_buton_inst0;
  
  monitor_agent_buton  monitor_agent_buton_inst0;
  
  uvm_sequencer #(tranzactie_agent_buton) sequencer_agent_buton_inst0;
  
  
  //se declara portul de comunicare al agentului cu scoreboardul/mediul de referinta; prin acest port agentul trimite spre verificare datele preluate de la monitor; a se observa ca intre monitor si agent (practic in interiorul agentului) comunicarea se face la nivel de tranzactie
  uvm_analysis_port #(tranzactie_agent_buton) de_la_monitor_agent_buton;
  
  
  //se declara un camp in care spunem daca agentul este activ sau pasiv; un agent activ contine in plus, fata de agentul pasiv, driver si sequencer
  local int is_active = 1;
  
  
  //se declara constructorul clasei; acesta este un cod standard pentru toate componentele
  function new (string name = "agent_buton", uvm_component parent = null);
      super.new (name, parent);
    de_la_monitor_agent_buton = new("de_la_monitor_agent_buton", this);
  endfunction 
  
  
  //rularea unui mediu de verificare cuprinde mai multe faze; in faza "build", se "asambleaza" agentul, tinandu-se cont daca acesta este activ sau pasiv
  virtual function void build_phase (uvm_phase phase);
    
    //se apeleaza functia build_phase din clasa parinte (uvm_agent)
    super.build_phase(phase);
    
    //atat agentii activi, cat si agentii pasivi au nevoie de un monitor 
    monitor_agent_buton_inst0 = monitor_agent_buton::type_id::create ("monitor_agent_buton_inst0", this);
    // daca agentul este activ, i se adauga atat sequencerul (componenta care aduce datele in agent) cat si driverul (componenta care preia datele de la sequencer si le transmite DUT-ului adaptandu-le protocolului de comunicatie al acestuia)
    if (is_active==1) begin
      sequencer_agent_buton_inst0 = uvm_sequencer#(tranzactie_agent_buton)::type_id::create ("sequencer_agent_buton_inst0", this);
      driver_agent_buton_inst0 = driver_agent_buton::type_id::create ("driver_agent_buton_inst0", this);
    end

  endfunction
  
  
  //rularea unui mediu de verificare cuprinde mai multe faze; in faza "connect", se realizeaza conexiunile intre componente; in cazul agentului, se realizeaza conexiunile intre sub-componentele agentului
  virtual function void connect_phase (uvm_phase phase);
    
    //se apeleaza functia connect_phase din clasa parinte (uvm_agent)
    super.connect_phase(phase);
    
    //se conecteaza portul agentului cu portul de comunicatie al monitorului din agent (monitorul nu poate trimite date in exterior decat prin intermediul agentului din care face parte)
    de_la_monitor_agent_buton = monitor_agent_buton_inst0.port_date_monitor_buton;
    
	// driverul primeste date de la sequencer, pentru a le transmite DUT-ului; daca agentul este activ, trebuie realizata si conexiunea intre sequencer si driver 
    if (is_active==1)begin
      driver_agent_buton_inst0.seq_item_port.connect (sequencer_agent_buton_inst0.seq_item_export);
    end
    
  endfunction
  
endclass

`endif