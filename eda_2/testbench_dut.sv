`timescale 1ns/1ps
`include "design.sv"
module testbench();
    logic clk;
    reg reset_n;      // Active low reset
    reg psel;         // APB select
    reg penable;      // APB enable
    reg pwrite;       // APB write signal
    reg [7:0] paddr;  // APB address bus
    reg [7:0] pwdata; // APB write data bus
    wire [7:0] prdata; // APB read data bus
    wire pready;      // APB ready signal
    wire scl;         // I2C clock line
    wire sda;         // I2C data line

    // Clock Generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period
    end

    // DUT Instantiation
    translator dut (
        .clk(clk),
        .reset_n(reset_n),
        .psel(psel),
        .penable(penable),
        .pwrite(pwrite),
        .paddr(paddr),
        .preg_wdata(pwdata),
        .preg_rdata(prdata),
        .pready(pready),
        .scl(scl),
        .sda(sda)
    );

    // Test Stimulus
    initial begin
        // Apply reset
        reset_n = 0;
        psel = 0;
        penable = 0;
        pwrite = 0;
        paddr = 0;
        pwdata = 0;
        #20;
        reset_n = 1;  // De-assert reset

        // Perform APB write transactions
        write_reg(8'h00, 8'h32);
        write_reg(8'h01, 8'h13);
        write_reg(8'h02, 8'h62);

        // Perform APB read transaction
        read_reg(8'h00);
        read_reg(8'h01);
        read_reg(8'h02);

        #100;
        $finish;
    end

    task test_test_transfer_citire();
        psel = 0;
        penable = 0;
        pwrite = 0;
        paddr = 0;
        pwdata = 0;
        #20;
        reset_n = 1;  // De-assert reset

        // Perform APB write transactions
        write_reg(8'h00, 8'h32);
        write_reg(8'h01, 8'h13);
        write_reg(8'h02, 8'h62);

        // Perform APB read transaction
        read_reg(8'h00);
        read_reg(8'h01);
        read_reg(8'h02);


    endtask

    // APB Write Task
    task write_reg(input [7:0] addr, input [7:0] data);
        begin
            @(posedge clk);
            psel = 1;
            pwrite = 1;
            paddr = addr;
            pwdata = data;
            penable = 0;
            @(posedge clk);
            penable = 1;
            @(posedge clk);
            while (!pready) @(posedge clk);
            psel = 0;
            penable = 0;
            pwrite = 0;
        end
    endtask

    // APB Read Task
    task read_reg(input [7:0] addr);
        begin
            @(posedge clk);
            psel = 1;
            pwrite = 0;
            paddr = addr;
            penable = 0;
            @(posedge clk);
            penable = 1;
            @(posedge clk);
            while (!pready) @(posedge clk);
            $display("Read from Address %h: Data = %h", addr, prdata);
            psel = 0;
            penable = 0;
        end
    endtask

endmodule
