`ifndef __input_sequence_intrari
`define __input_sequence_intrari

//se declara o clasa care genereaza o secventa de date
class secventa_buton_intrari extends uvm_sequence #(tranzactie_agent_buton);
  
  //noul tip de data (secventa) se adauga la baza de date UVM
  `uvm_object_utils(secventa_buton_intrari)
  
  //se declara dimensiunea sirului
  rand int numarul_de_tranzactii;
  
  //se constrange dimensiunea sirului de tranzactii intr-un interval ales de noi
  constraint marimea_sirului_c{
    //constrangerile declarate cu cuvantul cheie "soft" se pot suprascrie ulterior
    soft numarul_de_tranzactii inside {[10:10+5]};
  }
  
  function new(string name="secventa_intrari");
    super.new(name);
  endfunction
    
  function void post_randomize();
    $display("SECVENTA_INTRARI: Marimea sirului de tranzactii=%0d", numarul_de_tranzactii);
   endfunction
  
  virtual task body();
    
    //`ifdef DEBUG
    //	$display("phase_shift= ", phase_shift);
    //`endif;
    `uvm_info("SECVENTA_INTRARI", $sformatf("A inceput secventa cu dimensiunea de %-2d elemente", numarul_de_tranzactii), UVM_NONE)
    
    for (int i=0; i< numarul_de_tranzactii; i++) begin
      
      //se creaza o tranzactie folosindu-se cuvantul cheie "req"
      req = tranzactie_agent_buton::type_id::create("req");
      
      //se incepe crearea tranzactiei
      start_item(req);
      //se aleatorizeaza continutul tranzactiei (in acest caz cererile venite de la trenuri), admitand ca la un moment dat, minim 0 trenuri si maxim 2 trenuri sa ceara accesul pe tronsonul de linie interesant
      assert (req.randomize() with { enable inside {[0:1]};});
      `ifdef DEBUG
      `uvm_info("SECVENTA_INTRARI", $sformatf("La timpul %0t s-a generat elementul %0d cu informatiile:\n ", $time, i), UVM_LOW)
        req.afiseaza_informatia_tranzactiei_agent_buton();
      `endif;
      
      //s-a terminat crearea tranzactiei; aceasta poate pleca catre sequencer
      finish_item(req);
    end
    `uvm_info("SECVENTA_INTRARI", $sformatf("S-au generat toate cele %0d tranzactii", numarul_de_tranzactii), UVM_LOW)
  endtask
endclass
`endif