`ifndef __sensor_intf
`define __sensor_intf

interface sensor_interface_dut;
  logic  clk_i; 
  logic  reset_n;
  logic [9:0] luminous_intensity_i;
  logic [5:0] temperature_i;
  logic [6:0] humidity_i;
  logic  valid_i;
  logic  ready_o;
  
 import uvm_pkg::*;
      
      

          
          
   property temperature_interval;
     @(posedge clk_i) disable iff (reset_n==1)//daca avem reset, nu se executa asertia
          temperature_i >= 0 && temperature_i <= 40;//intervalul temperaturii este [0,40]
  endproperty
  
     asertia_temperature_interval: assert property (temperature_interval) 
       else `uvm_error("SENSOR_INTERFACE", $sformatf("asertia asertia_temperature_interval a picat, elementul de temperatura avand valoarea %0d", temperature_i));
       TEMPERATURE_INTERVAL: cover property (temperature_interval);//ne asiguram ca proprietatea a fost accesata macar o data
      
              
              
              
              
   property humidity_interval;
     @(posedge clk_i) disable iff (reset_n==1)//daca avem reset, nu se executa asertia
        humidity_i >= 0 && humidity_i <= 100;//intervalul umiditatii este [0,100]
  endproperty
  
     asertia_humidity_interval: assert property (humidity_interval) 
       else `uvm_error("SENSOR_INTERFACE", $sformatf("asertia asertia_humidity_interval a picat, elementul de umiditate avand valoarea %0d", humidity_i));
       HUMIDITY_INTERVAL: cover property (humidity_interval);//ne asiguram ca proprietatea a fost accesata macar o data
      
                  
                  
    property luminous_intensity_interval;
      @(posedge clk_i) disable iff (reset_n==1)//daca avem reset, nu se executa asertia
         luminous_intensity_i >= 0 && luminous_intensity_i <= 900;//intervalul temperaturii este [0,900]
  endproperty
  
      asertia_luminous_intensity_interval: assert property (luminous_intensity_interval) 
        else `uvm_error("SENSOR_INTERFACE", $sformatf("asertia asertia_luminous_intensity_interval a picat, elementul de intensitate luminoasa avand valoarea %0d", luminous_intensity_i));
        LUMINOUS_INTENSITY_INTERVAL: cover property (luminous_intensity_interval);//ne asiguram ca proprietatea a fost accesata macar o data
      
endinterface


`endif