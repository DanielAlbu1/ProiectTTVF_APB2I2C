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


    // ------------------------------------------------------------
    // ASSERTIONS / CHECKERS
    // ------------------------------------------------------------

    // 1. idle_state: paddr should change only when psel is HIGH (start of transfer); outside of a trasnaction, addr is z
    property idle_state_check;
        @(posedge clk_i)
        $rose(psel) |-> $changed(paddr);
    endproperty
    assert property (idle_state_check);

    // 2. setup_state: penable should be high in the second cycle of transaction
    property setup_state_check;
        @(posedge clk_i)
        psel && !penable |=> penable;
    endproperty
    assert property (setup_state_check);

    // 3. signal_stability_check: signals are stable during valid transfer
    property signal_stability_check;
        @(posedge clk_i)
        disable iff (!reset_n)
        (psel && !penable && !pready |->
            $stable(paddr) && $stable(pwrite) && $stable(pwdata));
    endproperty
    assert property (signal_stability_check);

    // 4. prdata_in_write_transfer: prdata should not change during write
    property prdata_in_write_transfer_check;
        @(posedge clk_i)
        disable iff (!reset_n)
        (psel && penable && !pwrite |-> $stable(prdata));
    endproperty
    assert property (prdata_in_write_transfer_check);

    // 5. penable_check: penable turns LOW after valid transfer
    property penable_check;
        @(posedge clk_i)
        disable iff (!reset_n)
        (psel && penable && pready |=> !pready);
    endproperty
    assert property (penable_check);

    // 6. psel_check: psel turns LOW after valid transfer
    property psel_check;
        @(posedge clk_i)
        disable iff (!reset_n)
        (psel && penable && pready |=> !psel);
    endproperty
    assert property (psel_check);

endinterface