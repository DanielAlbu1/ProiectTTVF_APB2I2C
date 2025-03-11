`ifndef __input_coverage_collector_agent_actuator
`define __input_coverage_collector_agent_actuator

 import uvm_pkg::*; 
 `include "uvm_macros.svh"

//aceasta clasa este folosita pentru a se vedea cate combinatii de intrari au fost trimise DUT-ului; aceasta clasa este doar de model, si probabil va fi modificata, deoarece in general nu ne intereseaza sa obtinem in simulare toate combinatiile posibile de intrari ale unui DUT
class coverage_agent_actuator extends uvm_component;
  
  //componenta se adauga in baza de date
  `uvm_component_utils(coverage_agent_actuator)
  
  //se declara pointerul catre monitorul care da datele asupra carora se vor face masuratorile de coverage
  monitor_agent_actuator p_monitor;
  
  covergroup actuator_cg;
    option.per_instance = 1;
    coverpoint p_monitor.starea_preluata_a_actuatorului.Heat_i;
    coverpoint p_monitor.starea_preluata_a_actuatorului.AC_i;
    coverpoint p_monitor.starea_preluata_a_actuatorului.Blinds_i;
    coverpoint p_monitor.starea_preluata_a_actuatorului.Dehumidifier_i;
  
    //se presupune ca este de interes sa se vada ce combinatii au aparut intre cele 6 intrari posibile
   /* cross p_monitor.starea_preluata_a_actuatorului.Heat_i,
     p_monitor.starea_preluata_a_actuatorului.AC_i,
     p_monitor.starea_preluata_a_actuatorului.Blinds_i,
     p_monitor.starea_preluata_a_actuatorului.Dehumidifier_i;*/
  endgroup
  
  //se creaza grupul de coverage; ATENTIE! Fara functia de mai jos, grupul de coverage nu va putea esantiona niciodata date deoarece pana acum el a fost doar declarat, nu si creat
  function new(string name, uvm_component parent);
    super.new(name, parent);
    $cast(p_monitor, parent);
    actuator_cg = new();
  endfunction
  
  //o alta modalitate de a incheia declaratia unei clase este sa se scrie "endclass: numele_clasei"; acest lucru este util mai ales cand se declara mai multe clase in acelasi fisier; totusi, se recomanda ca fiecare fisier sa nu contina mai mult de o declaratie a unei clase
endclass: coverage_agent_actuator


`endif