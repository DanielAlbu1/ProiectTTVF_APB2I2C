//---------------------------------------------------------------------------------------
// Universitatea Transilvania din Brasov
// Proiect     : Translator APB-I2C
// Autor       : Pavel Codrut
// Data        : 24.03.2025
//---------------------------------------------------------------------------------------
// Descriere   : Implementarea translatorului
//---------------------------------------------------------------------------------------
import uvm_pkg::*;

module translator (
    input                  clk,         // Clock input
    input                  reset_n,     // Active low reset
    input                  psel,        // APB select
    input                  penable,     // APB enable
    input                  pwrite,      // APB write signal
    input  [2:0]           paddr,       // APB address bus
    input  [7:0]           preg_wdata,  // APB write data bus
    output reg [7:0]       preg_rdata,  // APB read data bus
    output reg             pready,      // APB ready signal
    output                 scl,         // I2C clock line
    inout                  sda          // I2C data line
);

    // Internal registers
    reg [7:0] reg_wdata;                // Write data register
    reg [7:0] reg_rdata;                // Read data register
    reg [7:0] reg_ctrl;                 // Control register

    // I2C State Machine Control
    reg [3:0] state;                    // State machine for I2C
    reg [2:0] bit_cnt;                  // Bit counter for byte transfer
    reg [7:0] temp_data;                // Temporary register for data transmission
    reg scl_enable;                     // Enable signal to toggle SCL
    reg scl_state;                      // Internal SCL signal state
    reg sda_out;                        // Internal SDA signal for output
    reg ack;                            // Acknowledge from I2C slave

    // State definitions for I2C FSM
    localparam IDLE  = 4'd0,
               START = 4'd1,
               ADDR  = 4'd2,
               DATA  = 4'd3,
               STOP  = 4'd4;

    // Control Register Bits
    wire error = reg_ctrl[0];           // Error bit (ACK/NACK)
    wire start = reg_ctrl[1];           // Start bit
    wire rw    = reg_ctrl[2];           // Read/Write bit

    // Assignments for SDA and SCL
    assign sda = (sda_out) ? 1'bz : 1'b0; // SDA output control
    assign scl = scl_state;               // SCL driven by synchronized state

    // APB Read Logic
    always @(posedge clk or negedge reset_n) begin
        if (~reset_n)
            preg_rdata <= 8'd0;
        else if (psel && !penable && !pwrite) begin
            case (paddr)
                3'h0: preg_rdata <= reg_wdata;
                3'h1: preg_rdata <= reg_rdata;
                3'h2: preg_rdata <= reg_ctrl;
                default: preg_rdata <= 8'd0;
            endcase
        end
    end

    // APB Write Logic
    always @(posedge clk or negedge reset_n) begin
        if (~reset_n) begin
            reg_wdata <= 8'd0;
            reg_rdata <= 8'd0;
            reg_ctrl  <= 8'd0;
        end else if (psel && !penable && pwrite) begin
            case (paddr)
                3'h0: reg_wdata <= preg_wdata;
                3'h1: reg_rdata <= preg_wdata;
                3'h2: reg_ctrl  <= preg_wdata;
            endcase
        end
    end

    // APB Ready Signal
    always @(posedge clk or negedge reset_n) begin
        if (~reset_n)
            pready <= 1'b0;
        else if (pready == 1'b1)
            pready <= 1'b0;
        else if (psel && penable)
            pready <= 1'b1;
    end

    // SCL Clock Generation
    always @(posedge clk or negedge reset_n) begin
        if (~reset_n) begin
            scl_state <= 1'b1; // SCL idle high on reset
        end else if (scl_enable) begin
            scl_state <= ~scl_state; // Toggle SCL when enabled
        end else begin
            scl_state <= 1'b1; // Keep SCL high when disabled (idle state)
        end
    end

    // I2C State Machine
    always @(posedge clk or negedge reset_n) begin
        if (~reset_n) begin
            state <= IDLE;
            sda_out <= 1'b1; // SDA idle high
            bit_cnt <= 3'd0;
            reg_ctrl[0] <= 1'b0; // Clear error bit
            scl_enable <= 1'b0; // Disable SCL toggling initially
        end else begin
            case (state)
                IDLE: begin
                    if (start) begin
                        state <= ADDR;
                        sda_out <= 1'b0; // Start condition
                        scl_enable <= 1'b1; // Enable SCL toggling
                        temp_data <= {reg_wdata[6:0], rw}; // Load address + R/W
                        bit_cnt <= 3'd7;
                    end
                end

                ADDR: begin
                    if (scl_state) begin // Shift bits on SCL high
                        if (bit_cnt == 0) begin
                            sda_out <= 1'b1; // Release SDA for ACK
                            @(posedge scl);
                            if (sda === 1'b0) begin // Check ACK
                                ack <= 1'b1;
                                state <= DATA;
                                bit_cnt <= 3'd7;
                                temp_data <= reg_wdata;
                            end else begin
                                reg_ctrl[0] <= 1'b1; // Set error bit on NACK
                                state <= STOP;
                            end
                        end else begin
                            bit_cnt <= bit_cnt - 1;
                            temp_data <= {temp_data[6:0], 1'b0};
                            sda_out <= temp_data[7];
                        end
                    end
                end

                DATA: begin
                    if (rw == 1'b1) begin // Write operation
                        if (scl_state) begin
                            if (bit_cnt == 0) begin
                                sda_out <= 1'b1; // Release SDA for ACK
                                @(posedge scl);
                                if (sda === 1'b0) begin // Check ACK
                                    ack <= 1'b1;
                                    if (~start) begin
                                        state <= STOP; // Stop if start cleared
                                        scl_enable <= 1'b0; // Disable SCL toggling
                                    end else begin
                                        bit_cnt <= 3'd7; // Restart bit counter
                                    end
                                end else begin
                                    reg_ctrl[0] <= 1'b1; // Set error bit on NACK
                                    state <= STOP;
                                    scl_enable <= 1'b0; // Disable SCL toggling
                                end
                            end else begin
                                bit_cnt <= bit_cnt - 1;
                                temp_data <= {temp_data[6:0], 1'b0};
                                sda_out <= temp_data[7];
                            end
                        end
                    end else begin // Read operation
                        if (scl_state) begin
                            reg_rdata <= {reg_rdata[6:0], sda}; // Shift in data
                            if (bit_cnt == 0) begin
                                sda_out <= 1'b0; // Send ACK
                                if (~start) begin
                                    state <= STOP;
                                    scl_enable <= 1'b0; // Disable SCL toggling
                                end else begin
                                    bit_cnt <= 3'd7; // Restart bit counter
                                end
                            end else begin
                                bit_cnt <= bit_cnt - 1;
                            end
                        end
                    end
                end

                STOP: begin
                        sda_out <= 1'b0; // Generate stop condition
                        scl_state <= 1'b1; // Set SCL high
                        #10ns;
                        sda_out <= 1'b1; // Release SDA
                        #5ns;
                        state <= IDLE;
                        scl_enable <= 1'b0; // Disable SCL toggling
        
                end

            endcase
        end
    end

endmodule
