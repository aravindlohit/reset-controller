
// source chipmunklogic.com
module test;
  logic rst;
  logic aux_rst;
  logic clk;
  logic f_clk;
  logic f_rst;
int i;
  logic rst1,rst2,rst3;
  // Reset generato
  
  reset_controller_top  dut_inst ( .i_rst(rst) ,
                                  .i_aux_rst(aux_rst),
                                  .clk(clk),
                                  .filt_clk(f_clk),
                                  .filt_rst(f_rst) ,
                                  .o_rst0_sync(rst1),
                                  .o_rst1_sync(rst2),
                                  .o_rst2_sync(rst3));
  initial begin
    
    
    // Initial values
    clk = 0;
    f_clk = 0;
    rst = 0;
    aux_rst = 0;
    f_rst = 1;

    // Wait 2 cycles for clocks to settle
    repeat (2) @(posedge clk);
    f_rst = 0;

    $display("[%0t] === Reset asserted ===", $time);
    // Assert primary reset briefly (glitch)
    rst = 1;
    #10;
    rst = 0;

    // Wait and assert again with longer duration
    #50;
    $display("[%0t] === Valid reset ===", $time);
    rst = 1;
    #10;
    rst = 0;
    #20 rst=1;
    #15 rst=0;
    #25 rst=1;
    #15 rst=0; 

    // Auxiliary reset test
    #50;
    $display("[%0t] === Aux reset ===", $time);
    aux_rst = 1;
    #100;
    aux_rst = 0;

    // Let outputs settle
    #600;

    $finish;
    
  end

  always #5 clk= ~clk;
  
  
  
  //assertion-1
  //as per the design filter reset must be asserted for atleast 10 clock cycles 
  property filter_init;
    @(posedge f_clk) f_rst |-> ##10 f_rst ##1 !rst;
  endproperty
    
  assert property (filter_init)  
    else $error ("filter inti failed");

    //assertion-2 
    // after rst_o asserted low rst_1 should be asserted low after 5 cycles based on the given condition, present design can generate rst with a strecth of 5-16 clock cycles, so rst_1 should be deasserted after 5 cycles rst_1 is deaseerted 
     
    property stretch_check;
      @(posedge clk) !rst1 |-> ##5 $fell(rst1) |-> ##5 $fell(rst2);
    endproperty
    assert property (stretch_check)  
      else $error ("rst strecth failed");
    
 
  initial begin
  $dumpfile("dump.vcd");
    $dumpvars(0,test); 
end

endmodule


