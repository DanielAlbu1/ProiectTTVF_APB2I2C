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
    logic sda_tb;

    assign sda = (sda_tb === 1'b0) ? 1'b0 : 1'bz;

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
    initial begin
        i2c_slave_ack(1);
    end
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
        write_reg(8'h00, 8'b1010_1010); // adress
        write_reg(8'h02, 8'b0000_0110); // control register
        write_reg(8'h00, 8'b0101_1000); // data
        write_reg(8'h02, 8'b0000_0000); // control register

        #300;
        $finish;
    end

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
            @(posedge clk iff pready === 1);
            psel = 0;
            penable = 0;
            pwrite = 'bz;
            
            paddr = 'bz;
            pwdata = 'bz;
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
            @(posedge clk iff pready === 1);
            $display("Read from Address %h: Data = %h", addr, prdata);
            psel = 0;
            penable = 0;
            pwrite = 'bz;
            paddr = 'bz;
        end
    endtask
   // Add task for acknowledge response from i2c slave
   task i2c_slave_ack(integer counter);
    integer i;          
    sda_tb <= 1'bz;
    while(counter) begin
        // Wait for 8 bits of data to be sent by the DUT
        for (i = 7; i >= 0; i = i - 1) begin
            // Wait for rising edge of SCL (data is stable on rising edge)
            @(posedge scl);

            // Wait for falling edge of SCL (completes the bit transfer)
            @(negedge scl);
        end

        // Drive the ACK bit (pull SDA low) during the 9th clock cycle
        //@(negedge scl);
        sda_tb <= 0; // ACK (Slave pulls SDA low)

        // Wait for the rising edge of SCL to latch ACK
        @(posedge scl);

        // Release SDA after ACK
        @(negedge scl);
        sda_tb <= 1'bz; // Release control of the SDA line
        counter = counter - 1;
    end
endtask
endmodule
