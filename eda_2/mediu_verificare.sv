`ifndef __verification_environment
`define __verification_environment

typedef scoreboard;//aceasta este o pre-definire a tipului de data scoreboard folosita pentru a evita erorile aparute in urma faptului ca scoreboardul importa colectorul de coverage "coverage_valori_citite_senzor_ref", si colectorul de coverage importa scoreboardul; explicatia in engleza: this is a forward type definition used to solve cross dependency between scoreboard and coverage class
`include "agent_senzor.sv"
`include "agent_actuator.sv"
`include "agent_buton.sv"
`include "coverage_valori_citite_senzor_ref.sv"
`include "scoreboard.sv"

class mediu_verificare extends uvm_env;
  
  //se adauga mediul de verificare in baza de date
  `uvm_component_utils(mediu_verificare)
  
  
  //se declara interfetele de pe care se vor prelua date
  virtual actuator_interface_dut interfata_monitor_actuator;
  virtual button_interface_dut interfata_monitor_buton;
  virtual sensor_interface_dut interfata_monitor_senzor;
  
  //se declara agentii
  agent_buton agent_buton_din_mediu;//agentul activ care furnizeaza stimuli si monitorizeaza interfata de intrare
  
  agent_senzor agent_senzor_din_mediu;//agentul activ care furnizeaza stimuli si monitorizeaza interfata de intrare
  
  agent_actuator agent_actuator_din_mediu;//agentul pasiv care monitorizeaza traficul de pe interfata de iesire a DUT-ului pe care se trimit valorile semafoarelor (daca sunt aprinse rosu sau verde)
  
  
  //se declara componentele de tip scoreboard (una singura in cazul nostru)
  scoreboard IO_scorboard;
  
  
  //constructorul clasei
  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  
  //se creaza componentele mediului de verificare
  virtual function void build_phase (uvm_phase phase);
    
    //se apeleaza functia build_phase din clasa parinte
    super.build_phase(phase);
    agent_buton_din_mediu = agent_buton::type_id::create("agent_buton_din_mediu", this);
    agent_senzor_din_mediu = agent_senzor::type_id::create("agent_senzor_din_mediu", this);
    agent_actuator_din_mediu = agent_actuator::type_id::create("agent_actuator_din_mediu", this);
    IO_scorboard = scoreboard::type_id::create("IO_scorboard", this);
    
    
  endfunction
  

  //se creaza conexiunile intre componente
  function void connect_phase(uvm_phase phase);
    `uvm_info("MEDIU DE VERIFICARE", "A inceput faza de realizare a conexiunilor", UVM_NONE);
    // se preiau interfetele din baza de date; daca nu se pot prelua interfetele, se va da eroare
    assert(uvm_resource_db#(virtual actuator_interface_dut)::read_by_name(
      get_full_name(), "actuator_interface_dut", interfata_monitor_actuator)) else `uvm_error("MEDIU DE VERIFICARE", "Nu s-a putut prelua din baza de date UVM actuator_interface_dut");
    
    assert(uvm_resource_db#(virtual button_interface_dut)::read_by_name(
      get_full_name(), "button_interface_dut", interfata_monitor_buton)) else `uvm_error("MEDIU DE VERIFICARE", "Nu s-a putut prelua din baza de date UVM button_interface_dut");
    
    assert(uvm_resource_db#(virtual sensor_interface_dut)::read_by_name(
      get_full_name(), "sensor_interface_dut", interfata_monitor_senzor)) else `uvm_error("MEDIU DE VERIFICARE", "Nu s-a putut prelua din baza de date UVM sensor_interface_dut");
    
	//conectarea scoreboardului la porturile de date ale agentilor
    
agent_buton_din_mediu.de_la_monitor_agent_buton.connect(IO_scorboard.port_pentru_datele_de_laButon);
    
agent_senzor_din_mediu.de_la_monitor_senzor.connect(IO_scorboard.port_pentru_datele_de_laSenzor);
    
agent_actuator_din_mediu.de_la_monitor_agent_actuator.connect(IO_scorboard.port_pentru_datele_de_laActuator);

    `uvm_info("MEDIU DE VERIFICARE", "Faza de realizare a conexiunilor s-a terminat", UVM_HIGH);
  endfunction: connect_phase
  
  task run_phase(uvm_phase phase);
    //phase.raise_objection(this);
    `uvm_info("MEDIU DE VERIFICARE", "Faza de rulare a activitatii mediului de verificare (RUN PHASE) a inceput.", UVM_NONE);
    begin
      //AICI SE POATE SCRIE UN COD DE INITIALIZARE A TRAFICULUI PE INTERFETE DACA ESTE NEVOIE
    end
    //phase.drop_objection(this);
  endtask
  
endclass


`endif