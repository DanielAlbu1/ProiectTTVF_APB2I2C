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

endinterface