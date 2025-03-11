class test_functionalitati_senzori extends test_de_baza_ambient;
  `uvm_component_utils(test_functionalitati_senzori)
  
  
  //se declara constructorul testului
  function new(string name = "test_functionalitati_senzori", uvm_component parent=null);
    super.new(name, parent);
  endfunction
  
   function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    
    //se activeaza un martor ("obiectie") ca am inceput o activitate; pana cand nu se termina activitatea, simulatorul va sti ca nu trebuie sa intrerupe faza "run" din rularea testului; de aceea trebuie sa avem grija ca la sfarsitul acestei functii sa dezactivam martorul de activitate
    phase.raise_objection(this);
    
    //se aserteaza semnalele de reset din interfete
    apply_reset();
    `uvm_info("test_functionalitati_senzori", "real execution begins", UVM_NONE);
    
    //in bulca fork join se pot porni in paralel secventele mediului de verificare
    fork
      begin
     `ifdef DEBUG
        $display("va incepe sa ruleze secventa: buton_intrari_seq pentru agentul activ agent_buton");
      `endif; 
     	buton_intrari_seq.start(mediu_de_verificare_ambient.agent_buton_din_mediu.sequencer_agent_buton_inst0);
      `ifdef DEBUG
        $display("s-a terminat de rulat secventa pentru agentul activ agent_buton");
      `endif;
      end
      
      begin 
      `ifdef DEBUG
        $display("va incepe sa ruleze secventa: senzor_rand_seq pentru agentul activ agent_senzor");
      `endif;
        senzor_rand_seq.start(mediu_de_verificare_ambient.agent_senzor_din_mediu.sequencer_agent_senzor_inst0);
      `ifdef DEBUG
        $display("s-a terminat de rulat secventa pentru agentul activ agent_senzor");
      `endif;
    
      end
    join
    //dupa ce s-au terminat secventele care trimit stimuli DUT-ului, toate semnalele de intrare se pun in 0
    @(posedge vif_sensor_dut.clk_i);
    vif_sensor_dut.temperature_i <= 0;
    vif_sensor_dut.humidity_i <= 0;
    vif_sensor_dut.luminous_intensity_i <= 0;
    vif_sensor_dut.valid_i <= 0;
 //   vif_sensor_dut.ready_o <= 0;
    vif_button_dut.enable_i <= 0;
    #100//se mai asteapta 100 de unitati de timp inainte sa se dezactiveze martorul de activitate, actiune care va permite simulatorului sa incheie activitatea
	//se dezactiveaza martorul 
    phase.drop_objection(this);
    endtask
  
  
  //in aceasta faza, care se desfasoara dupa faza de run in care se intampla actiunea propriu-zisa in mediul de verificare, afisam valorile de coverage
  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
  	endfunction 
endclass