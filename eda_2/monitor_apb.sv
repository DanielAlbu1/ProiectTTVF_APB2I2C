class apb_monitor extends uvm_monitor;
  `uvm_component_utils(apb_monitor)

  // Ports to observe APB signals
  virtual apb_if apb_vif; // Virtual interface to connect to the DUT's APB interface

  // Analysis port to send the captured transactions
  uvm_analysis_port #(tranzactie_apb) apb_ap;

  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
    apb_ap = new("apb_ap", this);
  endfunction

  // Build phase
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db #(virtual apb_if)::get(this, "", "vif", apb_vif)) begin
      `uvm_fatal("APB_MONITOR", "Virtual interface not provided for APB monitor")
    end
  endfunction

  // Run phase (monitoring activity)
  task run_phase(uvm_phase phase);
    tranzactie_apb apb_trans;

    forever begin
      @(posedge apb_vif.clk_i); // Trigger on clock edge

      if (apb_vif.psel && apb_vif.penable) begin
        // Capture transaction
        apb_trans.psel = apb_vif.psel;
        apb_trans.penable = apb_vif.penable;
        apb_trans.pwrite = apb_vif.pwrite;
        apb_trans.paddr = apb_vif.paddr;
        apb_trans.pwdata = apb_vif.pwdata;
        apb_trans.prdata = apb_vif.prdata;
        apb_trans.pready = apb_vif.pready;

        // Send to the analysis port
        apb_ap.write(apb_trans);
      end
    end
  endtask
endclass