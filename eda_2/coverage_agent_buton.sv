`ifndef __input_coverage_collector_agent_buton
`define __input_coverage_collector_agent_buton

//aceasta clasa este folosita pentru a se vedea cate combinatii de intrari au fost trimise DUT-ului; aceasta clasa este doar de model, si probabil va fi modificata, deoarece in general nu ne intereseaza sa obtinem in simulare toate combinatiile posibile de intrari ale unui DUT
class coverage_agent_buton extends uvm_component;
  
  //componenta se adauga in baza de date
  `uvm_component_utils(coverage_agent_buton)
  
  //se declara pointerul catre monitorul care da datele asupra carora se vor face masuratorile de coverage
  monitor_agent_buton p_monitor;
  
  covergroup buton_cg;
    option.per_instance = 1;
    coverpoint p_monitor.starea_preluata_a_butonului.enable;

    
    //se presupune ca este de interes sa se vada ce combinatii au aparut intre cele 6 intrari posibile

  endgroup
  
  //se creaza grupul de coverage; ATENTIE! Fara functia de mai jos, grupul de coverage nu va putea esantiona niciodata date deoarece pana acum el a fost doar declarat, nu si creat
  function new(string name, uvm_component parent);
    super.new(name, parent);
    $cast(p_monitor, parent);
    buton_cg = new();
  endfunction
  
  //o alta modalitate de a incheia declaratia unei clase este sa se scrie "endclass: numele_clasei"; acest lucru este util mai ales cand se declara mai multe clase in acelasi fisier; totusi, se recomanda ca fiecare fisier sa nu contina mai mult de o declaratie a unei clase
endclass: coverage_agent_buton


`endif