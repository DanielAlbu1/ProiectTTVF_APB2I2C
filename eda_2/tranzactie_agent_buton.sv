`ifndef __transaction_agent_buton
`define __transaction_agent_buton

//o tranzactie este formata din totalitatea datelor transmise la un moment dat pe o interfata
class tranzactie_agent_buton extends uvm_sequence_item;
  
  //componenta tranzactie se adauga in baza de date
  `uvm_object_utils(tranzactie_agent_buton)
  
  rand bit enable;

  
  //constructorul clasei; această funcție este apelată când se creează un obiect al clasei "tranzactie"
  function new(string name = "element_secventa");//numele dat este ales aleatoriu, si nu mai este folosit in alta parte
    super.new(name);
  	enable = 0;

  endfunction
  
  //functie de afisare a unei tranzactii
  function void afiseaza_informatia_tranzactiei_agent_buton();
  
    $display("TRANZACTIE_AGENT_BUTON: Valoarea enable este: %0h",enable);

  endfunction
  
  function tranzactie_agent_buton copy();
	copy = new();
	copy.enable = this.enable;
	return copy;
  endfunction

  
endclass


`endif