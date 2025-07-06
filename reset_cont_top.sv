`include "a.sv"
`include "b.sv"
`include "c.sv"
`include "d.sv"
`include "e.sv"


// Code your design here
//===================================================================
// Configuration macros
//===================================================================
`define GLF  // Define this macro to generate glitch filter
//===================================================================

// Module definition
module reset_controller_top #(
   // Features enabled/disabled
   parameter EN_FULL_SYNC_RST    = 1'b0   ,  // 1'b0 = Sync only de-assertion, 1'b1 = Sync both assertion & de-assertion (fully synchronous)   
   parameter EN_MIN_WIDTH_RST    = 1'b0   ,  // Enable/disable min. pulse width validation @reset input; enabled iff EN_FULL_SYNC_RST = 1   
   parameter EN_ACTV_LOW_RST_OUT = 1'b0   ,  // 1'b0 = Active-high reset @output, 1'b1 = Active-low reset @output
   
   // Feature parameters
   parameter SYNC_FLOPS          = 3'd3   ,  // No. of sync flops used in synchronizer; min = 2
   parameter GLITCH_LEN          = 20'd16 ,  // Min pulse width (in filt_clk cycles) @primary reset input, below which is glitch; valid values = [1, 1024]  
   parameter MIN_WIDTH_RST       = 20'd16  ,  // Min pulse width (in clk cycles) @synchronized reset, below which is glitch; valid values = [2-31]
   parameter RST0_LEN            = 6'd05  ,  // RST0 min. pulse width at output, stretched by RST0_LEN clk cycles; 0 = disable, valid values = [2-31]
   parameter RST1_LEN            = 6'd05  ,  // RST1 min. pulse width at output, stretched by RST0_LEN + RST1_LEN clk cycles; 0 = disable, valid values = [2-31]
   parameter RST2_LEN            = 6'd05  ,  // RST2 min. pulse width at output, stretched by RST0_LEN + RST1_LEN + RST2_LEN clk cycles; , valid values = [2-31]
   
   // Derived parameters
   `ifdef GLF
   parameter EN_GLITCH_FILT      = 1'b1     // Enable glitch filter @primary reset input
   `else 
   parameter EN_GLITCH_FILT      = 1'b0     // Disable glitch filter @primary reset input
   `endif
)
(
   input  logic i_rst       ,  // Input primary reset; asynchronous, active-high
   input  logic i_aux_rst   ,  // Input auxiliary reset; asynchronous, active-high
   input  logic clk         ,  // Clock
   `ifdef GLF
   input  logic filt_clk    ,  // Glitch filter clock
   input  logic filt_rst    ,  // Glitch filter reset; asynchronous, active-high
   `endif
   output logic o_rst0_sync ,  // Synchronized reset RST0 output
   output logic o_rst1_sync ,  // Synchronized reset RST0 output
   output logic o_rst2_sync    // Synchronized reset RST0 output
);

//===================================================================================================================================================
// Localparams, internal Signals/Registers
//===================================================================================================================================================
localparam RST_POL = ~ EN_ACTV_LOW_RST_OUT ;  // Reset out polarity
logic rst_filt, rst_glb       ;  // Filtered reset, Global reset
logic rst_sync, rst_sync_filt ;  // Synchronized reset, Filtered synchronized reset
logic rst0, rst1, rst2        ;  // Synchronized resets out

// ==============================================
// Glitch filter generator
// ==============================================
generate
   // Glitch filter enabled...
   if (EN_GLITCH_FILT) begin : gen_glitch_filt
      glitch_filt #(
         .N          (GLITCH_LEN) ,    
         .SYNC_FLOPS (SYNC_FLOPS) , 
         .RST_VAL    (1'b1)        // 1'b1: active reset is generated at the output on resetting glitch filter...
      ) inst_glitch_filt (    
         .sample_clk (filt_clk) , 
         .areset     (filt_rst) , 
         .i_sig      (i_rst)    ,
         .o_sig_filt (rst_filt)   
      );
   end
   // Glitch filter not enabled...
   else begin : gen_no_filt
      assign rst_filt = i_rst ;      
   end
endgenerate

// Global reset is generated after ORing with auxiliary reset
// Auxiliary reset is assumed to be coming from some functional block and assumed to be glitch free...
// Global reset should have the same polarity as the reset @output...
if (RST_POL) assign rst_glb  =  (rst_filt | i_aux_rst) ;
else         assign rst_glb  = ~(rst_filt | i_aux_rst) ;

// ==============================================
// Synchronized reset generator
// ==============================================
generate
   // Reset synchronizer for only de-assertion; reset with asynchronous assertion and synchronous de-assertion is generated...
   if (!EN_FULL_SYNC_RST) begin : gen_sync_rst_deasrt
      areset_sync #(
         .STAGES  (SYNC_FLOPS) ,
         .RST_POL (RST_POL)   
      )
      inst_areset_sync (
         .clk          (clk)      ,
         .i_rst_async  (rst_glb)  ,
         .o_rst_sync   (rst_sync) 
      );
   end
   // Reset synchronizer for both assertion and de-assertion; fully synchronous reset is generated...
   else begin : gen_sync_rst_asrt_deasrt
      cdc_sync #(
         .STAGES  (SYNC_FLOPS) 
      )
      inst_areset_sync (
         .clk          (clk)     ,
         .rstn         (1'b1)    ,   // NOTE: Reset port is tied inactive, but that is okay for fully sync reset 
                                     // cz known value is driven at output after couple of clock cycles anyway...
         .i_sig        (rst_glb) ,
         .o_sig_sync   (rst_sync) 
      );    
   end
endgenerate

// ==============================================
// Synchronized reset pulse validation
// ==============================================
generate
   // Pulse validation enabled...
   if (EN_FULL_SYNC_RST && EN_MIN_WIDTH_RST) begin : gen_min_width_rst
      min_width_rst #(
         .MIN_WIDTH (MIN_WIDTH_RST)
      ) inst_min_width_rst (
         .i_rst (rst_sync) ,
         .clk   (clk) ,
         .o_rst (rst_sync_filt)
      );
   end   
   else begin : gen_no_min_width_rst
      assign rst_sync_filt = rst_sync ;
   end
endgenerate

// ==============================================
// Reset stretcher
// ==============================================
generate   
   // RST0 stretcher
   if (RST0_LEN != 0) begin : gen_rst0_stretch
      rst_stretch #(
         .IS_ASYNC  (~EN_FULL_SYNC_RST),
         .RST_POL   (RST_POL),
         .MIN_WIDTH (RST0_LEN)
      )  inst_rst0_stretch (
         .clk   (clk),
         .i_rst (rst_sync_filt),
         .o_rst (rst0)
      );
   end
   else begin : gen_no_rst0_stretch
      assign rst0 = rst_sync_filt ;
   end

   // RST1 stretcher
   if (RST1_LEN != 0) begin : gen_rst1_stretch
      rst_stretch #(
         .IS_ASYNC  (~EN_FULL_SYNC_RST),
         .RST_POL   (RST_POL),
         .MIN_WIDTH (RST1_LEN)
      )  inst_rst1_stretch (
         .clk   (clk),
         .i_rst (rst0),  // Daisy chained to RST0
         .o_rst (rst1)
      );
   end
   else begin : gen_no_rst1_stretch
      assign rst1 = rst0 ;
   end

   // RST2 stretcher
   if (RST2_LEN != 0) begin : gen_rst2_stretch
      rst_stretch #(
         .IS_ASYNC  (~EN_FULL_SYNC_RST),
         .RST_POL   (RST_POL),
         .MIN_WIDTH (RST2_LEN)
      )  inst_rst2_stretch (
         .clk   (clk),
         .i_rst (rst1),  // Daisy chained to RST1
         .o_rst (rst2)
      );
   end
   else begin : gen_no_rst2_stretch
      assign rst2 = rst1 ;
   end   
endgenerate

// ==============================================
// Output resets
// ==============================================
assign o_rst0_sync = rst0 ;
assign o_rst1_sync = rst1 ;
assign o_rst2_sync = rst2 ;

 
    
  
  
endmodule
