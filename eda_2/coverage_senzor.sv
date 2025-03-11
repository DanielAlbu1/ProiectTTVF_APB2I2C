`ifndef __senzor_coverage_collector
`define __senzor_coverage_collector

//aceasta clasa este folosita pentru a se vedea cate combinatii de intrari au fost trimise DUT-ului; aceasta clasa este doar de model, si probabil va fi modificata, deoarece in general nu ne intereseaza sa obtinem in simulare toate combinatiile posibile de intrari ale unui DUT
class coverage_senzor extends uvm_component;
  
  //componenta se adauga in baza de date
  `uvm_component_utils(coverage_senzor)
  
  //se declara pointerul catre monitorul care da datele asupra carora se vor face masuratorile de coverage
  monitor_senzor p_monitor;
  
  covergroup stari_senzor_cg;
    option.per_instance = 1;
    coverpoint p_monitor.starea_preluata_a_senzorului.temperature{
        bins se_porneste_centrala = {[0:21]};
        bins val_limita_temperatura = {22};
      	bins se_opreste_centrala = {[23:40]};
    }
    coverpoint p_monitor.starea_preluata_a_senzorului.humidity{
        bins dezumidificatorul_este_oprit = {[0:34]};
        bins valoare_limita_oprire = {35};
        bins valoare_limita_pornire = {50};
        bins porneste_dezumidificatorul ={[51:100]};
    }
    coverpoint p_monitor.starea_preluata_a_senzorului.luminous_intensity{
        bins se_deschid_draperiile = {[0:199]};
        bins valoare_limita_deschidere = {200};
        bins valoare_limita_inchidere = {700};
        bins se_inchid_draperiile = {[701:900]};
    }
  endgroup
  
  //se creeaza grupul de coverage; ATENTIE! Fara functia de mai jos, grupul de coverage nu va putea esantiona niciodata date deoarece pana acum el a fost doar declarat, nu si creat
  function new(string name, uvm_component parent);
    super.new(name, parent);
    $cast(p_monitor, parent);//with the use of $cast, type check will occur during runtime
    stari_senzor_cg = new();
  endfunction
  
endclass


`endif