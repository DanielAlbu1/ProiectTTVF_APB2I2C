class i2c_monitor extends uvm_monitor;
  `uvm_component_utils(i2c_monitor)

  // Ports to observe I2C signals
  virtual i2c_if i2c_vif; // Virtual interface for I2C

  // Transaction type for I2C
  typedef struct {
    bit        start_condition; // Start condition detected
    bit        stop_condition;  // Stop condition detected
    logic [7:0] data;           // Data being transmitted or received
    bit        rw;              // Read/Write bit
    bit        ack;             // ACK/NACK response
  } i2c_transaction_t;

  // Analysis port to send the captured transactions
  uvm_analysis_port #(i2c_transaction_t) i2c_ap;

  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
    i2c_ap = new("i2c_ap", this);
  endfunction

  // Build phase
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db #(virtual i2c_if)::get(this, "", "vif", i2c_vif)) begin
      `uvm_fatal("I2C_MONITOR", "Virtual interface not provided for I2C monitor")
    end
  endfunction

  // Run phase (monitoring activity)
  task run_phase(uvm_phase phase);
    i2c_transaction_t i2c_trans;
    bit [7:0] shift_reg;
    bit [2:0] bit_cnt;

    forever begin
      @(negedge i2c_vif.scl); // Sample on falling edge of SCL

      if (i2c_vif.sda == 0 && i2c_vif.scl == 1) begin
        // Start condition detected
        i2c_trans.start_condition = 1;
        i2c_ap.write(i2c_trans);
      end else if (i2c_vif.sda == 1 && i2c_vif.scl == 1) begin
        // Stop condition detected
        i2c_trans.stop_condition = 1;
        i2c_ap.write(i2c_trans);
      end else begin
        // Capture data bits
        shift_reg = {shift_reg[6:0], i2c_vif.sda};
        bit_cnt++;

        if (bit_cnt == 8) begin
          // Data byte captured
          i2c_trans.data = shift_reg;
          i2c_trans.rw = shift_reg[0]; // Last bit is R/W
          i2c_ap.write(i2c_trans);
          bit_cnt = 0;
        end
      end

      // Capture ACK/NACK
      @(posedge i2c_vif.scl);
      i2c_trans.ack = ~i2c_vif.sda; // ACK is 0, NACK is 1
      i2c_ap.write(i2c_trans);
    end
  endtask
endclass