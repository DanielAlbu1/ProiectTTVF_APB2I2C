`ifndef __input_sequence_val_lim
`define __input_sequence_val_lim

//se declara o clasa care genereaza o secventa de date
class secventa_senzor_val_limita extends uvm_sequence #(tranzactie_senzor);
  
  //noul tip de data (secventa) se adauga la baza de date UVM
  `uvm_object_utils(secventa_senzor_val_limita)
  
  //se declara dimensiunea sirului
  int numarul_de_tranzactii =3;
  
  //se constrange dimensiunea sirului de tranzactii intr-un interval ales de noi
 /* constraint marimea_sirului_c{
    //constrangerile declarate cu cuvantul cheie "soft" se pot suprascrie ulterior
    soft numarul_de_tranzactii inside {[`10:`10+5]};
  }*/
  
  function new(string name="secventa_senzor");
    super.new(name);
  endfunction
    
  function void post_randomize();
    $display("SECVENTA_SENZOR: Marimea sirului de tranzactii=%0d", numarul_de_tranzactii);
   endfunction
  
  virtual task body();
    
    //`ifdef DEBUG
    //	$display("phase_shift= ", phase_shift);
    //`endif;
    `uvm_info("SECVENTA_SENZOR", $sformatf("A inceput secventa cu dimensiunea de %-2d elemente", numarul_de_tranzactii), UVM_NONE)
    
    for (int i=0; i< numarul_de_tranzactii; i++) begin
      
      //se creaza o tranzactie folosindu-se cuvantul cheie "req"
      req = tranzactie_senzor::type_id::create("req");
      
      //se incepe crearea tranzactiei
      start_item(req);
      //se genereaza valori petru cazurile limita 
      								//val minime
      assert (req.randomize() with {i == 0 -> temperature == 0; 
              						i == 0 -> humidity == 0;
              						i == 0 -> luminous_intensity == 0;
              						//val limita
              						i == 1 -> temperature == 22;
              						i == 1 -> humidity == 35;
              						i == 1 -> luminous_intensity == 200;
              						i == 2 -> temperature == 25;
              						i == 2 -> humidity == 50;
              						i == 2 -> luminous_intensity == 700;
              						//val maxime
              						i == 3 -> temperature == 40;
              						i == 3 -> humidity == 100;
                                    i == 3 -> luminous_intensity == 900;});
      								
      `ifdef DEBUG
      `uvm_info("SECVENTA_SENZOR", $sformatf("La timpul %0t s-a generat elementul %0d cu informatiile:\n ", $time, i), UVM_LOW)
        req.afiseaza_informatia_tranzactiei();
      `endif;
      
      //s-a terminat crearea tranzactiei; aceasta poate pleca catre sequencer
      finish_item(req);
    end
    `uvm_info("SECVENTA_SENZOR", $sformatf("S-au generat toate cele %0d tranzactii", numarul_de_tranzactii), UVM_LOW)
  endtask
endclass
`endif