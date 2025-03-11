`ifndef __transaction
`define __transaction

//o tranzactie este formata din totalitatea datelor transmise la un moment dat pe o interfata
class tranzactie_agent_actuator extends uvm_sequence_item;
  
  //componenta tranzactie se adauga in baza de date
  `uvm_object_utils(tranzactie_agent_actuator)

  rand bit Heat_i;
  rand bit AC_i;
  rand bit Blinds_i;
  rand bit Dehumidifier_i;
 
  

  //constructorul clasei; această funcție este apelată când se creează un obiect al clasei "tranzactie"
  function new(string name = "element_secventa");//numele dat este ales aleatoriu, si nu mai este folosit in alta parte
    super.new(name);
  	Heat_i = 0;
  	AC_i = 0;
  	Blinds_i = 0;
  	Dehumidifier_i = 0;
  endfunction
  
  //functie de afisare a unei tranzactii
  function void afiseaza_informatia_tranzactiei();
    $display("Val Caldurii: %0h, Valoarea AC: %0h, Blinds: %0h, Dehumidifier: %0h",Heat_i,AC_i,Blinds_i,Dehumidifier_i); 
     
  endfunction
  
  //functie prin care se compara 2 tranzactii
  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    //primele 4 linii le putem considera cod standard, pe care nu il modificam
    bit res;
	tranzactie_agent_actuator _obj;
	$cast(_obj, rhs);
	res = super.do_compare(_obj, comparer) &
	      Heat_i == _obj.Heat_i &
    	  AC_i == _obj.AC_i &
    	  Blinds_i == _obj.Blinds_i &
    	  Dehumidifier_i == _obj.Dehumidifier_i;
    `uvm_info(get_name(), $sformatf("In tranzactie_agent_actuator::do_compare(), rezultatul comparatiei este %0b", res), UVM_LOW)
	return res;
  endfunction
  
  //functie pentru "deep copy"
  function tranzactie_agent_actuator copy();
	copy = new();
	copy.Heat_i = this.Heat_i;
	copy.AC_i = this.AC_i;
	copy.Blinds_i = this.Blinds_i;
	copy.Dehumidifier_i = this.Dehumidifier_i;
	return copy;
  endfunction

  
endclass


`endif