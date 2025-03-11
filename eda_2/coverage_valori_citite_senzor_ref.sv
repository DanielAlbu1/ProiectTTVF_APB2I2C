//aceasta componenta de coverage inregistreaza date venite din modelul de referinta implementat in scoreboard
//se inregistreaza in ce stari a intrat tronsonul de linie de interes
`ifndef __fsm_coverage_collector
`define __fsm_coverage_collector
class coverage_valori_citite_senzor_ref extends uvm_component;
  
  //componenta se adauga in baza de date
  `uvm_component_utils(coverage_valori_citite_senzor_ref)
  
  //se declara pointerul catre scoreboardul care da datele asupra carora se vor face masuratorile de coverage
  scoreboard p_scoreboard;
  
  
  
  covergroup date_procesate_cg;
    option.per_instance = 1;
    stare_modul: coverpoint p_scoreboard.enable;
    val_temperatura: coverpoint p_scoreboard.tranzactie_venita_de_la_senzor.temperature{
      option.weight = 0;//nu sunt interesat sa inregistrez valorile acestui cover_point de sine statator (valorile sunt colectate de colectorul din monitorul agentului), ci ma intereseaza sa folosesc datele din acest coverpoint doar cand calculez cross-coverage
      bins intervale_valori[5] = {[0:40]};//am impartit intervalul de valori posibile pe care valoarea senzorului le poate avea in 5 intervale succesive de marimi egale (aici probabil: 0:7, 8:15, 16:23, 24:31, 32:40); daca este atinsa macar o valoare din fiecare interval, se considera ca s-au atins toate valorile dorite
    }
    val_umiditate: coverpoint p_scoreboard.tranzactie_venita_de_la_senzor.humidity{
      option.weight = 0;//nu sunt interesat sa inregistrez valorile acestui cover_point de sine statator (valorile sunt colectate de colectorul din monitorul agentului), ci ma intereseaza sa folosesc datele din acest coverpoint doar cand calculez cross-coverage
      bins intervale_valori[5] = {[0:100]};//am impartit intervalul de valori posibile pe care valoarea senzorului le poate avea in 5 intervale succesive de marimi egale (aici probabil: 0:20, 21:40, 41:60, 61:80, 81:100); daca este atinsa macar o valoare din fiecare interval, se considera ca s-au atins toate valorile dorite
    }
    val_intensitate_luminoasa: coverpoint p_scoreboard.tranzactie_venita_de_la_senzor.luminous_intensity{
      option.weight = 0;//nu sunt interesat sa inregistrez valorile acestui cover_point de sine statator (valorile sunt colectate de colectorul din monitorul agentului), ci ma intereseaza sa folosesc datele din acest coverpoint doar cand calculez cross-coverage
      bins intervale_valori[5] = {[0:900]};//am impartit intervalul de valori posibile pe care valoarea senzorului le poate avea in 5 intervale succesive de marimi egale (aici probabil: 0:179, 180:359, 360:539, 540:719, 720:900); daca este atinsa macar o valoare din fiecare interval, se considera ca s-au atins toate valorile dorite
    }
    
    //ma intereseaza sa vad, in mare, cate valori de la senzor s-au procesat de catre DUT (DUT-ul citeste valorile doar cand semnalul enable are valoarea 1)
    temperature_cross: cross stare_modul, val_temperatura{
      ignore_bins ignore_disabled_module_values = temperature_cross with (stare_modul == 0);//nu ma intereseaza sa inregistrez valorile senzorului cand acestea nu sunt citite de DUT
  }
    umiditate_cross: cross stare_modul, val_umiditate{
       ignore_bins ignore_disabled_module_values = umiditate_cross with (stare_modul == 0);//nu ma intereseaza sa inregistrez valorile senzorului cand acestea nu sunt citite de DUT
    }
    luminozitate_cross: cross stare_modul, val_intensitate_luminoasa{
       ignore_bins ignore_disabled_module_values = luminozitate_cross with (stare_modul == 0);//nu ma intereseaza sa inregistrez valorile senzorului cand acestea nu sunt citite de DUT
    }
  endgroup
  
  //se creeaza grupul de coverage; ATENTIE! Fara functia de mai jos, grupul de coverage nu va putea esantiona niciodata date deoarece pana acum el a fost doar declarat, nu si creat
  function new(string name, uvm_component parent);
    super.new(name, parent);
    $cast(p_scoreboard, parent);
    date_procesate_cg = new();
  endfunction
  
endclass

`endif