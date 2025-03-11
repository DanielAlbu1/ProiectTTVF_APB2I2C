`ifndef __ambient_scoreboard
`define __ambient_scoreboard

//se declara prefixele pe care le vor avea elementele folosite pentru a prelua datele de la agentul de intrari, respectiv de la agentul de semafoare
`uvm_analysis_imp_decl(_actuator)
`uvm_analysis_imp_decl(_senzor)
`uvm_analysis_imp_decl(_buton)

class scoreboard extends uvm_scoreboard;
  
  //se adauga componenta in baza de date UVM
  `uvm_component_utils(scoreboard)
  
  //se declara porturile prin intermediul carora scoreboardul primeste datele de la agenti, aceste date reflectand functionalitatea DUT-ului
  //a se observa ca prefixele declarate mai sus intra in componenta tipului de data al porturilor
  //pentru fiecare port declarat, se spune carui tip de scoreboard ii apartine (in situatia de fata avem doar o clasa care defineste scoreboardul cu numele "scoreboard") portul, si ce tip de date vor fi vehiculate pe portul respectiv
  uvm_analysis_imp_actuator #(tranzactie_agent_actuator, scoreboard) port_pentru_datele_de_laActuator;
  uvm_analysis_imp_senzor #(tranzactie_senzor, scoreboard) port_pentru_datele_de_laSenzor;
  uvm_analysis_imp_buton #(tranzactie_agent_buton, scoreboard) port_pentru_datele_de_laButon;
  
  //se declara colectorul de coverage folosit pentru a se inregistra ce valori a generat senzorul atunci cand DUT-ul era pornit (enable = 1)
  coverage_valori_citite_senzor_ref colector_coverage_scoreboard;
  
  //pentru a inregistra coverage-ul dorit avem nevoie sa stim atat ce valori au venit de la senzori
  tranzactie_senzor tranzactie_venita_de_la_senzor;
  //se declara structura care va retine datele prezise de modelul de referinta; aceste date vor fi comparate cu datele de la iesirea DUT-ului
  tranzactie_agent_actuator tranzactie_prezisa_de_referinta, tranzactie_initiala_actuator, tranzactie_calculata_de_ref, tranzactie_de_la_dut;// tranzactie_initiala_actuator repezinta o tranzactie care nu se modifica niciodata, avand valorile implicite ale actuatorilor dupa reset; 
  
  //lista in care se retin tranzactiile pentru actuatori calculate de referinta; folosim o lista deoarece referinta calculeaza mai repede in ce stare se afla actuatorii decat DUT-ul, si aceste calcule trebuie retinute pana cand se culeg datele si de la DUT
  tranzactie_agent_actuator lista_tranzactii_ref [$];
  
  bit enable;
  
   //constructorul clasei
  function new(string name="scoreboard", uvm_component parent=null);
    //se apeleaza mai intai constructorul clasei parinte
    super.new(name, parent);
    //crearea porturilor
    port_pentru_datele_de_laActuator = new("pentru_datele_de_laActuator", this);
    port_pentru_datele_de_laSenzor = new("pentru_datele_de_laSenzor", this);
    port_pentru_datele_de_laButon = new("pentru_datele_de_laButon", this);
    
    //se creeaza tranzactia prezisa  de referinta:
    tranzactie_prezisa_de_referinta = new();
    
    //se creeaza tranzactia necesare pentru coverage:
    tranzactie_venita_de_la_senzor = new();
	
	tranzactie_initiala_actuator = new();
	
	lista_tranzactii_ref.push_back(tranzactie_initiala_actuator);
    
    tranzactie_calculata_de_ref = new();
	tranzactie_de_la_dut  = new();
    
    //se creeaza colectorul de coverage (la creare, se apeleaza constructorul colectorului de coverage)
    colector_coverage_scoreboard = coverage_valori_citite_senzor_ref::type_id::create("colector_coverage_scoreboard", this);
    
  endfunction
  
  
  virtual function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
    
    //in faza UVM "connect", se face conexiunea intre pointerul catre monitor din instanta colectorului de coverage a acestui monitor si monitorul insusi 
    ///colector_coverage_fsm_actuator_inteligenta.p_scoreboard = this;
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction
  
  function tranzactie_agent_actuator compute_result(tranzactie_senzor aux_tr_senzor);
  tranzactie_venita_de_la_senzor = aux_tr_senzor.copy();
  tranzactie_prezisa_de_referinta = new();
  if (enable ==1) begin
	if (tranzactie_venita_de_la_senzor.temperature <= 22)
      tranzactie_prezisa_de_referinta.Heat_i = 1;
    else
      tranzactie_prezisa_de_referinta.Heat_i = 0;
    
    if (tranzactie_venita_de_la_senzor.temperature > 25)
      tranzactie_prezisa_de_referinta.AC_i = 1;
    else
      if (tranzactie_venita_de_la_senzor.temperature <= 22)
      	tranzactie_prezisa_de_referinta.AC_i = 0;
		else
			tranzactie_prezisa_de_referinta.AC_i = lista_tranzactii_ref[lista_tranzactii_ref.size()-1].AC_i;;
    
    if (tranzactie_venita_de_la_senzor.humidity > 50)
      tranzactie_prezisa_de_referinta.Dehumidifier_i = 1;
    else
      if (tranzactie_venita_de_la_senzor.humidity <= 35)
      	tranzactie_prezisa_de_referinta.Dehumidifier_i = 0;
		else
		tranzactie_prezisa_de_referinta.Dehumidifier_i = lista_tranzactii_ref[lista_tranzactii_ref.size()-1].Dehumidifier_i;
    
    if (tranzactie_venita_de_la_senzor.luminous_intensity > 700)
      tranzactie_prezisa_de_referinta.Blinds_i = 1; // jaluzelele sunt inchise, trecerea luminii este oprita
    else
      if (tranzactie_venita_de_la_senzor.luminous_intensity <= 200 )
      	tranzactie_prezisa_de_referinta.Blinds_i = 0; // jaluzelele sunt deschise, trecerea luminii este permisa
		else
		tranzactie_prezisa_de_referinta.Blinds_i = lista_tranzactii_ref[lista_tranzactii_ref.size()-1].Blinds_i;
      end// if (enable == 1)
        else//altfel (daca dispozitivul este oprit ,enable-ul fiind pe 0 pun actuatorii intr-o stare initiala
      begin
        tranzactie_prezisa_de_referinta.Blinds_i = 0;
        tranzactie_prezisa_de_referinta.Heat_i = 0;
        tranzactie_prezisa_de_referinta.AC_i = 0;
        tranzactie_prezisa_de_referinta.Dehumidifier_i = 0;
      end
	  `ifdef DEBUG
       `uvm_info("SCOREBOARD", $sformatf("s-a evaluat noua tranzactie cu informatiile"), UVM_LOW)
       tranzactie_venita_de_la_senzor.afiseaza_informatia_tranzactiei();
       `uvm_info("SCOREBOARD", $sformatf("tranzactia prezisa ar fi"), UVM_LOW)
       tranzactie_prezisa_de_referinta.afiseaza_informatia_tranzactiei();
     `endif
	  return tranzactie_prezisa_de_referinta;
  endfunction
  
  
  
  //fiecare port de analiza UVM are atasata o functie write; prefixul declarat la inceputul acestui fisier pentru fiecare port se ataseaza automat functiei write, obtinand denumirile de mai jos
  //functiile write ale fiecarui port de date sunt apelate de componentele care pun date pe respectivul port (a se vedea fisierele unde sunt declarati agentii); aici, respectivele functii sunt implementate, pentru ca scoreboardul sa stie cum sa reactioneze atunci cand primeste date pe fiecare din porturi
  function void write_senzor(input tranzactie_senzor tranzactie_noua_senzor);  
    `uvm_info("SCOREBOARD", $sformatf("S-a primit de la agentul senzor tranzactia cu informatia:\n"), UVM_LOW)
    tranzactie_noua_senzor.afiseaza_informatia_tranzactiei();
   // if ((enable == 1 && posedge_for_enable_detected == 0) || negedge_for_enable_detected == 1) // se accepta doar datele primite in starea START, nu si un starea OFF; de asemenea, deoarece datele se citesc cu un tact intarziere de monitorul agentului, se accepta si citirea pe negedge de enable 
    $display($sformatf("cand s-au primit date de la senzori, enable a fost %d",enable));
    
	    tranzactie_venita_de_la_senzor = new();
        tranzactie_venita_de_la_senzor = tranzactie_noua_senzor.copy();
		tranzactie_calculata_de_ref = compute_result(tranzactie_venita_de_la_senzor);
		lista_tranzactii_ref.push_back(tranzactie_calculata_de_ref);
		`ifdef DEBUG
		$display("lista_tranzactii_ref: ");
	foreach (lista_tranzactii_ref[i])	
    lista_tranzactii_ref[i].afiseaza_informatia_tranzactiei();
      
      `endif
      
  endfunction : write_senzor
  
  function void write_buton(input tranzactie_agent_buton tranzactie_noua_buton);  
    `uvm_info("SCOREBOARD", $sformatf("S-a primit de la agentul buton tranzactia cu informatia:\n"), UVM_LOW)
    tranzactie_noua_buton.afiseaza_informatia_tranzactiei_agent_buton();
    `ifdef DEBUG
      $display("tranzactia prezisa de referinta este");
      tranzactie_prezisa_de_referinta.afiseaza_informatia_tranzactiei();
    `endif
    
   enable = tranzactie_noua_buton.enable;
   if (enable == 0) begin //daca enable s-a pus pe 0, valorile actuatorilor sunt cele implicite
   lista_tranzactii_ref.push_back(tranzactie_initiala_actuator);
   
   end
  endfunction : write_buton
  
  //deoarece pe portul "port_pentru_datele_de_laActuator" se primesc datele de la iesirea DUT-ului; inseamna ca atunci cand ajung date pe acest port deja am primit si datele de la diferitii agenti activi care stimuleaza intrarile DUT-ului; 
  function void write_actuator(input tranzactie_agent_actuator tranzactie_noua_actuator);
    
    //tot timpul creem un nou obiect (declarat la inceputul fisierului) inainte de a trimite datele la comparator. Altfel, daca am lucra cu pointerul tranzactie_noua_actuator, valoarea de la adresa acestora ar putea fi schimbata la urmatoarea tranzactie si astfel s-ar pierde datele de la tranzactia precedenta, comparatia fiind viciata
	tranzactie_de_la_dut = new();
	tranzactie_de_la_dut = tranzactie_noua_actuator.copy();
	
    
	  fork
      verifica_corespondenta_datelor(tranzactie_de_la_dut);
    join_none
    
      
  endfunction : write_actuator
  
          
  function verifica_corespondenta_datelor(tranzactie_agent_actuator tranzactie_noua_actuatorr);
  int gasit = 0;
  $display("1. am ajuns la checking");
     foreach (lista_tranzactii_ref[i])
     if (tranzactie_noua_actuatorr.compare(lista_tranzactii_ref[i]) ==1)//atentie! se foloseste numele "compare" pentru a apela functia do_compare declarata in clasa "tranzactie_semafoare";.
	 gasit = 1;
	 
	 if (gasit == 0)
      begin
        `uvm_error("SCOREBOARD", $sformatf(" datele generate de modelul de referinta nu se potrivesc cu datele venite de la DUT.\n") )
        $display("Datele de la DUT:\n");
        tranzactie_noua_actuatorr.afiseaza_informatia_tranzactiei(); 
        
      end
	  `ifdef DEBUG
    else
	begin
      `uvm_info("SCOREBOARD", $sformatf("DUT-ul a functionat la fel cu mediul de verificare, fiind evaluata tranzactia" ), UVM_LOW)
	  tranzactie_noua_actuatorr.afiseaza_informatia_tranzactiei();
    end
	`endif
	while (lista_tranzactii_ref.size()>2) //alegem un numar (in acest caz 2) care reprezinta maximul de tranzctii procesate de referinta pana cand se preia si raspunsul DUT-ului
		lista_tranzactii_ref.pop_front();
  endfunction
endclass
`endif