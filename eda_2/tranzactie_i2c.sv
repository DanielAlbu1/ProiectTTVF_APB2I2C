`ifndef __tranzactie_i2c
`define __tranzactie_i2c

//o tranzactie este formata din totalitatea datelor transmise la un moment dat pe o interfata
class tranzactie_i2c extends uvm_sequence_item;
  
  //componenta tranzactie se adauga in baza de date
  `uvm_object_utils(tranzactie_i2c)

  rand bit        start_condition; // Start condition detected
  rand bit        stop_condition;  // Stop condition detected
  rand logic [7:0] data;           // Data being transmitted or received
  rand bit        rw;              // Read/Write bit
  rand bit        ack;             // ACK/NACK response
 
  

  //constructorul clasei; această funcție este apelată când se creează un obiect al clasei "tranzactie"
  function new(string name = "tranzactie_i2c");//numele dat este ales aleatoriu, si nu mai este folosit in alta parte
    super.new(name);
  	start_condition = 0; 
    stop_condition = 0;  
    data = 0;           
    rw = 0;              
    ack = 0;  
  endfunction
  
  //functie de afisare a unei tranzactii
  function void afiseaza_informatia_tranzactiei();
    $display("Start: %0b, Stop: %0b, Data: %0h, RW: %0b, ACK: %0b",start_condition, stop_condition, data, rw, ack); 
     
  endfunction
  
  //functie pentru "deep copy"
  function tranzactie_i2c copy();
	copy = new();
	copy.start_condition = this.start_condition;
	copy.stop_condition = this.stop_condition;
	copy.data = this.data;
	copy.rw = this.rw;
  copy.ack = this.ack;
	return copy;
  endfunction

  
endclass


`endif