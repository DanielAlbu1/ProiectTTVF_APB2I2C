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
    input                  clk_i,         // Clock input
    input                  reset_n,       // Active low reset
    input                  psel,          // APB select
    input                  penable,       // APB enable
    input                  pwrite,        // APB write signal
    input  [2:0]           paddr,         // APB address bus
    input  [7:0]           pwdata,        // APB write data bus
    output reg [7:0]       prdata,        // APB read data bus
    output reg             pready,        // APB ready signal
    output reg             scl,           // I2C clock line
    inout                  sda            // I2C data line
);

    // Internal registers
    reg [7:0] wdata;                      // Write data register
    reg [7:0] rdata;                      // Read data register
    reg [7:0] ctrl;                       // Control register

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
    wire error = ctrl[0];                 // Error bit (ACK/NACK)
    wire start = ctrl[1];                 // Start bit
    wire rw = ctrl[2];                    // Read/Write bit
    wire reserved = ctrl[7:3];            // Reserved bits

    // I2C-related signals
    reg ack;                              // Acknowledge from I2C slave

    // SCL and SDA initial states
    initial begin
        scl = 1'b1; // Clock line idle high
    end

    assign sda = (state == DATA && rw == 1) ? 1'bz : temp_data[7]; // SDA for reads or writes

    // APB Interface Handling
    always @(posedge clk_i or negedge reset_n) begin
        if (!reset_n) begin
            wdata <= 8'b0;
            rdata <= 8'b0;
            ctrl <= 8'b0;
            prdata <= 8'b0;
            pready <= 1'b0;
        end else if (psel && penable) begin
            case (paddr)
                3'b000: begin // wdata register
                    if (pwrite) wdata <= pwdata;
                    pready <= 1'b1;
                end
                3'b001: begin // rdata register
                    prdata <= rdata;
                    pready <= 1'b1;
                end
                3'b010: begin // ctrl register
                    if (pwrite) ctrl <= pwdata;
                    prdata <= ctrl;
                    pready <= 1'b1;
                end
                default: pready <= 1'b0;
            endcase
        end else begin
            pready <= 1'b0;
        end
    end

    // I2C State Machine
    always @(posedge clk_i or negedge reset_n) begin
        if (!reset_n) begin
            state <= IDLE;
            scl <= 1'b1;
            temp_data <= 8'b0;
            ack <= 1'b1;
            bit_cnt <= 3'b0;
        end else begin
            case (state)
                IDLE: begin
                    if (start) begin
                        state <= START;
                        scl <= 1'b1;
                        temp_data <= {wdata, rw}; // Prepare address + read/write bit
                        bit_cnt <= 3'd7;
                    end
                end

                START: begin
                    sda <= 1'b0; // Start condition
                    scl <= 1'b1;
                    state <= ADDR;
                end

                ADDR: begin
                    scl <= 1'b0; // Clock low
                    sda <= temp_data[bit_cnt]; // Send bit
                    bit_cnt <= bit_cnt - 1;
                    if (bit_cnt == 0) begin
                        state <= DATA;
                        bit_cnt <= 3'd7; // Reset bit counter
                    end
                end

                DATA: begin
                    if (rw == 0) begin // Write
                        scl <= 1'b1; // Clock high
                        sda <= temp_data[bit_cnt]; // Send data bit
                        bit_cnt <= bit_cnt - 1;
                        if (bit_cnt == 0) begin
                            ack <= sda; // Capture ACK/NACK
                            ctrl[0] <= sda; // Update error bit
                            if (ack) state <= STOP; // Stop if NACK
                            else state <= ADDR; // Continue if ACK
                        end
                    end else begin // Read
                        scl <= 1'b1; // Clock high
                        rdata[bit_cnt] <= sda; // Capture data bit
                        bit_cnt <= bit_cnt - 1;
                        if (bit_cnt == 0) begin
                            ack <= sda; // Capture ACK
                            if (ack) state <= STOP; // Stop if NACK
                            else state <= ADDR; // Continue if ACK
                        end
                    end
                end

                STOP: begin
                    sda <= 1'b1; // Stop condition
                    scl <= 1'b1;
                    state <= IDLE;
                end

                default: state <= IDLE;
            endcase
        end
    end

endmodule