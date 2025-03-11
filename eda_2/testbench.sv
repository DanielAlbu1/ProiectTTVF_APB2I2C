`include "uvm_macros.svh"
import uvm_pkg::*;

`define PERIOADA_CEASULUI 10


`ifndef 10//numarul minim de tranzactii care se vor genera pe interfata de intrare
  `define 10 10
`endif

//`define DEBUG      //parametru folosit pentru a activa mesaje pe care noi le stabilim ca ar fi necesare doar la debug

//stabilirea semnificatiei unitatilor de timp din simulator
`timescale 1ns/1ns

//includerea fisierelor la care modulul de top trebuie sa aiba acces

`include "actuator_interface.sv"
`include "button_interface.sv"
`include "sensor_interface_dut.sv"
`include "test_de_baza_ambient.sv"
`include "test_valori_limita.sv"
`include "test_mentinerea_temperaturii.sv"
`include "test_mentinerea_umiditatii.sv"
`include "test_val_intens_luminoasa.sv"
`include "test_functionalitati_senzori.sv"
`include "test_verificare_apasari_multiple_buton.sv"
`include "test_verificare_apasari_rapide_buton.sv"
`include "test_total_ambient.sv"
`include "test_apasari_buton_frecvente.sv"


// Code your testbench here
// or browse Examples
module top();
  logic clk;
  parameter DATA_WIDTH = 6;
	wire reset_n;
	wire enable;
	wire valid;
	wire [DATA_WIDTH-1:0] temperature;
	wire [DATA_WIDTH  :0] humidity;
	wire [DATA_WIDTH+3:0] luminous;
	wire heat;
	wire AC;
	wire dehumidifier;
	wire blinds;
	wire ready;
  
  //sunt create instantele interfetelor (in acest proiect sunt 2 agenti, deci vor fi 2 interfete); se leaga semnalele interfetelor de semnalele din modulul de top
  sensor_interface_dut intf_sensor();
  assign intf_sensor.clk_i                = clk;
  assign reset_n = intf_sensor.reset_n;
  assign valid = intf_sensor.valid_i;
  assign intf_sensor.ready_o              = ready;
  assign luminous = intf_sensor.luminous_intensity_i;
  assign temperature = intf_sensor.temperature_i;
  assign humidity = intf_sensor.humidity_i;
                              
  
  button_interface_dut intf_button();
   assign intf_button.clk_i = clk;
   assign enable = intf_button.enable_i;
                                 
  actuator_interface_dut intf_actuator();
  assign intf_actuator.clk_i = clk;
  assign intf_actuator.heat_o = heat;
  assign intf_actuator.AC_o = AC;
  assign intf_actuator.dehumidifier_o = dehumidifier;
  assign intf_actuator.blinds_o = blinds;
  
  
  initial begin
    //cele 2 linii de mai jos permit vizualizarea formelor de unda (pentru a vizualiza formele de unda trebuie bifata si optiunea "Open EPWave after run" din sectiunea "Tools & Simulators" aflata in stanga paginii)
    $dumpfile("dump.vcd");
    $dumpvars;
    //se genereaza ceasul
	clk = 1;
	forever #(`PERIOADA_CEASULUI/2)  clk <= ~clk;
	end
  
   initial
  	begin
      //se salveaza instantele interfetelor in baza de date UVM
      uvm_config_db#(virtual sensor_interface_dut)::set(null, "*", "sensor_interface_dut", intf_sensor);
      uvm_config_db#(virtual button_interface_dut)::set(null, "*", "button_interface_dut", intf_button);
      uvm_config_db#(virtual actuator_interface_dut)::set(null, "*", "actuator_interface_dut", intf_actuator);

      //se ruleaza testul dorit
      run_test("test_total_ambient");
  	end
  
//  initial //in simulatorul gratuit nu se pot afisa mai mult de 5000 de linii de mesaje
//    begin
//      #2000
//      $finish();
//    end

  // se instantiaza DUT-ul, facandu-se legaturile intre semnalele din modulul de top si semnalele acestuia
  ambient DUT(
	.clk_i                 (clk         ),
	.reset_n               (reset_n     ),
	.enable_i              (enable      ),
	.temperature_i         (temperature ),
	.humidity_i            (humidity    ),
	.luminous_intensity_i  (luminous    ),
	.valid_i			   (valid       ),
	.heat_o		           (heat        ),
    .AC_o                  (AC          ),
	.dehumidifier_o        (dehumidifier),
	.blinds_o              (blinds      ),
	.ready_o               (ready       )
);


endmodule