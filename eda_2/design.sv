//---------------------------------------------------------------------------------------
// Universitatea Transilvania din Brasov
// Proiect     : Translator APB-I2C
// Autor       : Pavel Codrut
// Data        : 24.03.2025
//---------------------------------------------------------------------------------------
// Descriere   : Implementarea translatorului
//---------------------------------------------------------------------------------------
import uvm_pkg::*;
// create module
module translator (
    input                  clk,         // Clock input
    input                  reset_n,       // Active low reset
    input                  psel,          // APB select
    input                  penable,       // APB enable
    input                  pwrite,        // APB write signal
    input  [2:0]           paddr,         // APB address bus
    input  reg [7:0]      preg_wdata,        // APB write data bus
    output reg [7:0]       preg_rdata,        // APB read data bus
    output reg             pready,        // APB ready signal
    output reg             scl,           // I2C clock line
    inout  reg             sda            // I2C data line
);

    // Internal registers
    reg [7:0] reg_wdata;                      // Write data register
    reg [7:0] reg_rdata;                      // Read data register
    reg [7:0] reg_ctrl;                       // Control register

    // I2C State Machine Control
    reg [3:0] state;                      // State machine for I2C
    reg [2:0] bit_cnt;                    // Bit counter for byte transfer
    reg [7:0] temp_data;                  // Temp register for data transmission

    // State definitions for I2C FSM
    localparam IDLE = 4'd0,
               START = 4'd1,
               ADDR = 4'd2,
               DATA = 4'd3,
               STOP = 4'd4;

    // Control Register Bits
    wire error = reg_ctrl[0];                 // Error bit (ACK/NACK)
    wire start = reg_ctrl[1];                 // Start bit
    wire rw = reg_ctrl[2];                    // Read/Write bit
    wire reserved = reg_ctrl[7:3];            // Reserved bits

    // I2C-related signals
    reg ack;                              // Acknowledge from I2C slave

    // SCL and SDA initial states
    initial begin
        scl = 1'b1; // Clock line idle high
    end

    assign sda = (state == DATA && rw == 1) ? 1'bz : temp_data[7]; // SDA for reads or writes

    always @(posedge clk or negedge reset_n) begin
    if (~reset_n)
        preg_rdata <= 0;
    else if(psel && !penable && !pwrite) begin// primul tact al tranzactiei de citire 
        case(paddr)
        0: preg_rdata <= reg_wdata;
        1: preg_rdata <= reg_rdata;
        2: preg_rdata <= reg_ctrl;
        default: preg_rdata<= 0;
        endcase
    end
    end

    always @(posedge clk or negedge reset_n) begin
    if (~reset_n)begin
        reg_wdata <=0;
        reg_rdata <= 0;
        reg_ctrl <=0;
    end
    else if(psel && !penable && pwrite) begin // primul tact al tranzactiei de scriere 
        case(paddr)
        0: reg_wdata <= preg_wdata;
        1: reg_rdata <= preg_wdata;
        2: reg_ctrl <= preg_wdata;
        endcase
    end
    end
//    always @(posedge clk or negedge reset_n)
//    if (~reset_n)
//        pslverr <= 0;
//    else
//    if (pslverr ==1)
//    pslverr <=0;
//    else if(psel && !penable && paddr>2) // primul tact al tranzactiei
//        pslverr <=1;

    // APB Interface Handling
    // always @(posedge clk or negedge reset_n) begin
    //     if (!reset_n) begin
    //         reg_wdata <= 8'b0;
    //         reg_rdata <= 8'b0;
    //         reg_ctrl <= 8'b0;
    //         preg_rdata <= 8'b0;
    //         pready <= 1'b0;
    //     end else if (psel && penable) begin
    //         case (paddr)
    //             3'b000: begin // reg_wdata register
    //                 if (pwrite) reg_wdata <= preg_wdata;
    //                 pready <= 1'b1;
    //             end
    //             3'b001: begin // reg_rdata register
    //                 preg_rdata <= reg_rdata;
    //                 pready <= 1'b1;
    //             end
    //             3'b010: begin // reg_ctrl register
    //                 if (pwrite) reg_ctrl <= preg_wdata;
    //                 preg_rdata <= reg_ctrl;
    //                 pready <= 1'b1;
    //             end
    //             default: pready <= 1'b0;
    //         endcase
    //     end else begin
    //         pready <= 1'b0;
    //     end
    // end

    // // I2C State Machine
    // always @(posedge clk or negedge reset_n) begin
    //     if (!reset_n) begin
    //         state <= IDLE;
    //         scl <= 1'b1;
    //         temp_data <= 8'b0;
    //         ack <= 1'b1;
    //         bit_cnt <= 3'b0;
    //     end else begin
    //         case (state)
    //             IDLE: begin
    //                 if (start) begin
    //                     state <= START;
    //                     scl <= 1'b1;
    //                     temp_data <= {reg_wdata, rw}; // Prepare address + read/write bit
    //                     bit_cnt <= 3'd7;
    //                 end
    //             end

    //             START: begin
    //                 sda <= 1'b0; // Start condition
    //                 scl <= 1'b1;
    //                 state <= ADDR;
    //             end

    //             ADDR: begin
    //                 scl <= 1'b0; // Clock low
    //                 sda <= temp_data[bit_cnt]; // Send bit
    //                 bit_cnt <= bit_cnt - 1;
    //                 if (bit_cnt == 0) begin
    //                     state <= DATA;
    //                     bit_cnt <= 3'd7; // Reset bit counter
    //                 end
    //             end

    //             DATA: begin
    //                 if (rw == 0) begin // Write
    //                     scl <= 1'b1; // Clock high
    //                     sda <= temp_data[bit_cnt]; // Send data bit
    //                     bit_cnt <= bit_cnt - 1;
    //                     if (bit_cnt == 0) begin
    //                         ack <= sda; // Capture ACK/NACK
    //                         reg_ctrl[0] <= sda; // Update error bit
    //                         if (ack) state <= STOP; // Stop if NACK
    //                         else state <= ADDR; // Continue if ACK
    //                     end
    //                 end else begin // Read
    //                     scl <= 1'b1; // Clock high
    //                     reg_rdata[bit_cnt] <= sda; // Capture data bit
    //                     bit_cnt <= bit_cnt - 1;
    //                     if (bit_cnt == 0) begin
    //                         ack <= sda; // Capture ACK
    //                         if (ack) state <= STOP; // Stop if NACK
    //                         else state <= ADDR; // Continue if ACK
    //                     end
    //                 end
    //             end

    //             STOP: begin
    //                 sda <= 1'b1; // Stop condition
    //                 scl <= 1'b1;
    //                 state <= IDLE;
    //             end

    //             default: state <= IDLE;
    //         endcase
    //     end
    // end

endmodule