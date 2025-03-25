`timescale 1ns/1ps

module testbench();
logic clk;

reg reset_n;      // Active low reset
reg psel;          // APB select
reg penable;       // APB enable
reg pwrite;        // APB write signal
reg paddr;         // APB address bus
reg pwdata;        // APB write data bus
reg prdata;        // APB read data bus
reg pready;        // APB ready signal
reg scl;           // I2C clock line
reg sda;            // I2C data line

initial begin 
    clk =0;
forever clk <= ##5 ~clk;
end


module translator (
.clk_i(clk),         // Clock input
.reset_n(reset_n),       // Active low reset
.psel(psel),          // APB select
.penable(penable),       // APB enable
.pwrite(pwrite),        // APB write signal
.paddr(paddr),         // APB address bus
.pwdata(pwdata),        // APB write data bus
.prdata(prdata),        // APB read data bus
.pready(pready),        // APB ready signal
.scl(scl),           // I2C clock line
.sda(sda)            // I2C data line

initial begin
   write_reg(0, 8'h32);
end

task write_reg(bit [7:0] addr, bit [7:0] data);
    paddr = addr;
    pwdata = data;
endtask

endmodule 