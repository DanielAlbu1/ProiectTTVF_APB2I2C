`ifndef __actuator_intf
`define __actuator_intf

 import uvm_pkg::*; 
 `include "uvm_macros.svh"

interface actuator_interface_dut;
  logic clk_i; 
  logic reset_n;
  logic heat_o;
  logic AC_o;
  logic dehumidifier_o;
  logic blinds_o;

  //  import uvm_pkg::*;
  
    //asertii pe interfata
   property temperature_control;
     @(posedge clk_i) disable iff (reset_n!==0)//daca avem reset, nu se executa asertia
     (AC_o + heat_o <=1);//nu pot fi pornite simultan caldura si aerul conditionat
  endproperty
  
  asertia_temperature_control: assert property (temperature_control) 
    else `uvm_error("ACTUATOR_INTERFACE", $sformatf("asertia asertia_temperature_control a picat, elementul de incalzire avand valoarea %0d si elementul de racire avand valoarea %0d", heat_o, AC_o));
    TEMPERATURE_CONTROL: cover property (temperature_control);//ne asiguram ca proprietatea a fost accesata macar o data
      
      
      
      
endinterface


`endif