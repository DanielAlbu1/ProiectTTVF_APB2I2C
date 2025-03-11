`ifndef __input_sequence_apasari_frecvente
`define __input_sequence_apasari_frecvente

//se declara o clasa care genereaza o secventa de date
class secventa_apasari_buton_frecvente extends uvm_sequence #(tranzactie_agent_buton);
  
  //noul tip de data (secventa) se adauga la baza de date UVM
  `uvm_object_utils(secventa_apasari_buton_frecvente)
  
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
    
    for (int i=0; i< numarul_de_tranzactii-1; i++) begin//ultima tranzactie o generam in afara buclei for, pentru a lasa modulul sa functioneze (enable =1) si astfel sa va permite trimiterea tuturor tranzactiilor de temperatura
      
      //se creaza o tranzactie folosindu-se cuvantul cheie "req"
      req = tranzactie_agent_buton::type_id::create("req");
      
      //se incepe crearea tranzactiei
      start_item(req);
      //se aleatorizeaza continutul tranzactiei (in acest se da enable la modul), astfel incat butonul sa stea apasat 80% din timp si sa stea neapasat 20% din timp
      assert (req.randomize() with{enable dist { 0:= 2, 1:= 8}; });
       //assert (req.randomize() with { i%2==0 -> enable == 1; i%2 ==1 -> enable == 0;});
      
      `ifdef DEBUG
      `uvm_info("SECVENTA_INTRARI", $sformatf("La timpul %0t s-a generat elementul %0d cu informatiile:\n ", $time, i), UVM_LOW)
        req.afiseaza_informatia_tranzactiei_agent_buton();
      `endif;
      
      //s-a terminat crearea tranzactiei; aceasta poate pleca catre sequencer
      finish_item(req);
    end
    //ultima tranzactie lasa semnalul enable in 1, pana cand se termina de rulat structura fork_join din test
    req = tranzactie_agent_buton::type_id::create("req");
    start_item(req);
    req.enable = 1;
    finish_item(req);
    `uvm_info("SECVENTA_INTRARI", $sformatf("S-au generat toate cele %0d tranzactii", numarul_de_tranzactii), UVM_LOW)
  endtask
endclass
`endif