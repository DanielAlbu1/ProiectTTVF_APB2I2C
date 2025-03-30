interface i2c_if;

    // I2C signals
    logic scl;     // I2C clock signal
    logic sda;     // I2C data signal (bidirectional)

    // Clocking blocks
    clocking cb @(negedge scl); // Sample on falling edge of SCL
        input scl;
        input sda;
    endclocking

    clocking cb_drive @(posedge scl); // Drive data on the rising edge of SCL
        output scl;
        output sda;
    endclocking

    // Modport definitions
    // These allow different components to interact with the interface in specific ways
    modport master (
        input scl,
        inout sda
    );

    modport slave (
        input scl,
        inout sda
    );

  // ------------------------------------------------------------
    // ASSERTIONS / CHECKERS
    // ------------------------------------------------------------

     // 1. Signal Unknown Check
    // Ensure neither scl nor sda are in an unknown (X) state
    property signal_unknown_check;
        @(posedge scl)
        !$isunknown(scl) && !$isunknown(sda);
    endproperty
    assert property (signal_unknown_check);

    // 2. START Condition Check
    // SDA must go LOW while SCL is HIGH (indicates a START condition)
    property start_condition_check;
        @(posedge scl)
        (scl && $fell(sda));
    endproperty
    assert property (start_condition_check);

    // 3. STOP Condition Check
    // SDA must go HIGH while SCL is HIGH (indicates a STOP condition)
    property stop_condition_check;
        @(posedge scl)
        (scl && $rose(sda));
    endproperty
    assert property (stop_condition_check);


endinterface