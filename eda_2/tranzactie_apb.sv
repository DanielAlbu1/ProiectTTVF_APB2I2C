
`ifndef __tranzactie_apb
`define __tranzactie_apb

//o tranzactie este formata din totalitatea datelor transmise la un moment dat pe o interfata
class tranzactie_apb extends uvm_sequence_item;
  
  //componenta tranzactie se adauga in baza de date
  `uvm_object_utils(tranzactie_apb)
  
    rand bit        psel;      // Select
    rand bit        penable;   // Enable
    rand bit        pwrite;    // Write
    rand logic [2:0] paddr;    // Address
    rand logic [7:0] pwdata;   // Write data
    rand logic [7:0] prdata;   // Read data
    rand bit        pready;    // Ready signal
  
  //constructorul clasei; această funcție este apelată când se creează un obiect al clasei "tranzactie"
  function new(string name = "tranzactie_apb");//numele dat este ales aleatoriu, si nu mai este folosit in alta parte
    super.new(name);  
    psel = 0;      
    penable = 0;   
    pwrite = 0;    
    paddr = 0;    
    pwdata = 0;   
    prdata = 0;   
    pready = 0;    
  endfunction
  
  //functie de afisare a unei tranzactii
  function void afiseaza_informatia_tranzactiei();
    $display(psel,penable,pwrite,paddr,pwdata,prdata,pready);
  endfunction
  
  function tranzactie_senzor copy();
	copy = new();
    copy.psel = this.psel;      
    copy.penable = this.penable;   
    copy.pwrite = this.pwrite;    
    copy.paddr = this.paddr;    
    copy.pwdata = this.pwdata;   
    copy.prdata = this.prdata;   
    copy.pready = this.pready;   
	return copy;
  endfunction

endclass
`endif