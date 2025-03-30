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

    // 1. idle_state: paddr should change only when psel is HIGH (start of transfer)
    property idle_state_check;
        @(posedge clk_i)
        (!psel && $rose(psel) |-> $changed(paddr));
    endproperty
    assert property (idle_state_check);

    // 2. setup_state: penable should be high in the next cycle after psel
    property setup_state_check;
        @(posedge clk_i)
        (psel && !penable |=> penable);
    endproperty
    assert property (setup_state_check);

    // 3. access_wait_state: during wait, psel & penable stay HIGH, pready toggles
    property access_wait_state_check;
        @(posedge clk_i)
        (psel && penable && !pready |=> psel && penable);
    endproperty
    assert property (access_wait_state_check);

    // 4. signal_stability_check: signals are stable during valid transfer
    property signal_stability_check;
        @(posedge clk_i)
        disable iff (!reset_n)
        (psel && penable && !pready |->
            $stable(paddr) && $stable(pwrite) && $stable(pwdata));
    endproperty
    assert property (signal_stability_check);

    // 5. signal_unknown_check: no signal should be X during active transfer
    property signal_unknown_check;
        @(posedge clk_i)
        disable iff (!reset_n)
        !(^paddr === 1'bx || ^pwdata === 1'bx || ^prdata === 1'bx || psel === 1'bx || penable === 1'bx || pwrite === 1'bx);
    endproperty
    assert property (signal_unknown_check);

    // 6. pwdata_in_read_transfer: pwdata should not be active during read
    property pwdata_in_read_transfer_check;
        @(posedge clk_i)
        disable iff (!reset_n)
        (psel && penable && !pwrite |-> pwdata == '0);
    endproperty
    assert property (pwdata_in_read_transfer_check);

    // 7. prdata_in_write_transfer: prdata should not change during write
    property prdata_in_write_transfer_check;
        @(posedge clk_i)
        disable iff (!reset_n)
        (psel && penable && pwrite |-> $stable(prdata));
    endproperty
    assert property (prdata_in_write_transfer_check);

    // 8. penable_hold_check: penable remains HIGH during valid transfer
    property penable_hold_check;
        @(posedge clk_i)
        disable iff (!reset_n)
        (psel && penable && !pready |=> penable);
    endproperty
    assert property (penable_hold_check);

    // 9. psel_hold_check: psel remains HIGH during valid transfer
    property psel_hold_check;
        @(posedge clk_i)
        disable iff (!reset_n)
        (psel && penable && !pready |=> psel);
    endproperty
    assert property (psel_hold_check);

endinterface