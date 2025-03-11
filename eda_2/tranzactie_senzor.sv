`ifndef __sensor_transaction
`define __sensor_transaction

//o tranzactie este formata din totalitatea datelor transmise la un moment dat pe o interfata
class tranzactie_senzor extends uvm_sequence_item;
  
  //componenta tranzactie se adauga in baza de date
  `uvm_object_utils(tranzactie_senzor)
  
  rand bit[5:0] temperature;
  rand bit[6:0] humidity;
  rand bit[9:0] luminous_intensity;
  
  //constructorul clasei; această funcție este apelată când se creează un obiect al clasei "tranzactie"
  function new(string name = "element_secventaa");//numele dat este ales aleatoriu, si nu mai este folosit in alta parte
    super.new(name);  
    temperature = 23;
  	humidity = 0;
  	luminous_intensity = 0;
  endfunction
  
  //functie de afisare a unei tranzactii
  function void afiseaza_informatia_tranzactiei();
    $display("Valoarea temperaturii: %0h, Valoarea umiditatii: %0h, Valoarea intensitatii luminii: %0h", temperature, humidity, luminous_intensity);
  endfunction
  
  function tranzactie_senzor copy();
	copy = new();
	copy.temperature = this.temperature;
	copy.humidity = this.humidity;
	copy.luminous_intensity = this.luminous_intensity;
	return copy;
  endfunction

endclass
`endif