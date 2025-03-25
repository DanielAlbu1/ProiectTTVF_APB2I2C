interface apb_if (
    input logic clk_i,       // Clock signal
    input logic reset_n      // Reset signal (active low)
);

    // APB signals
    logic psel;              // APB select
    logic penable;           // APB enable
    logic pwrite;            // APB write signal
    logic [2:0] paddr;       // APB address bus
    logic [7:0] pwdata;      // APB write data bus
    logic [7:0] prdata;      // APB read data bus
    logic pready;            // Ready signal

    // Clocking blocks
    clocking cb @(posedge clk_i);
        input psel;
        input penable;
        input pwrite;
        input [2:0] paddr;
        input [7:0] pwdata;
        input [7:0] prdata;
        input pready;
    endclocking

endinterface