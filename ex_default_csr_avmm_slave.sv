// (C) 2001-2024 Intel Corporation. All rights reserved.
// Your use of Intel Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files from any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Intel Program License Subscription 
// Agreement, Intel FPGA IP License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Intel and sold by 
// Intel or its authorized distributors.  Please refer to the applicable 
// agreement for further details.


// Copyright 2023 Intel Corporation.
//
// THIS SOFTWARE MAY CONTAIN PREPRODUCTION CODE AND IS PROVIDED BY THE
// COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED
// WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
// BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
// WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
// OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
// EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//

module ex_default_csr_avmm_slave
  import afu_stall_pkg::*;
(
 
// AVMM Slave Interface
   input               clk,
   input               reset_n,
   input  logic [63:0] writedata,
   input  logic        read,
   input  logic        write,
   input  logic [7:0]  byteenable,
   output logic [63:0] readdata,
   output logic        readdatavalid,
   input  logic [31:0] address,
   input  logic        poison,
   output logic        waitrequest,

   //newly added ports for CXL stall design
   output logic [STALL_NUM_TARGETS-1:0][63:0] csr_stall_addr,
   output logic [STALL_NUM_TARGETS-1:0]       csr_target_en,
   output logic        csr_stall_en,
   output logic [15:0] csr_stall_cycles,
   input  logic [63:0] csr_status_ch0,
   input  logic [63:0] csr_status_ch1
);


 logic [31:0] csr_test_reg;
 logic [63:0] mask ;
 logic config_access; 

 assign mask[7:0]   = byteenable[0]? 8'hFF:8'h0; 
 assign mask[15:8]  = byteenable[1]? 8'hFF:8'h0; 
 assign mask[23:16] = byteenable[2]? 8'hFF:8'h0; 
 assign mask[31:24] = byteenable[3]? 8'hFF:8'h0; 
 assign mask[39:32] = byteenable[4]? 8'hFF:8'h0; 
 assign mask[47:40] = byteenable[5]? 8'hFF:8'h0; 
 assign mask[55:48] = byteenable[6]? 8'hFF:8'h0; 
 assign mask[63:56] = byteenable[7]? 8'hFF:8'h0; 
 assign config_access = address[21];  


//Terminating extented capability header
 localparam EX_CAP_HEADER  = 32'h00000000;


//Write logic
//
//  0x1000        stall_addr[0]
//  0x1008        bit0 = stall_en, bits16:1 = stall_cycles
//  0x1010        stall_addr[1]
//  0x1018        target-enable bitmask (resets to all ones)
//  0x1100 + 8*t  stall_addr[t], full array
//
always @(posedge clk) begin
    if (!reset_n) begin
        csr_test_reg     <= 32'h0;
        csr_stall_addr   <= '0;
        csr_target_en    <= '1;
        csr_stall_en     <= 1'b0;
        csr_stall_cycles <= 16'd0;
    end
    else if (write && ~poison) begin
         if (address[21:0] == 22'h000000) begin
            csr_test_reg <= (writedata[31:0] & mask[31:0]) |
                            (csr_test_reg & ~mask[31:0]);
         end
         else if (address[21:0] == 22'h001000) begin
            csr_stall_addr[0] <= writedata;
         end
         else if (address[21:0] == 22'h001008) begin
            csr_stall_en     <= writedata[0];
            csr_stall_cycles <= writedata[16:1];
         end
         else if (address[21:0] == 22'h001010) begin
            csr_stall_addr[1] <= writedata;
         end
         else if (address[21:0] == 22'h001018) begin
            csr_target_en <= writedata[STALL_NUM_TARGETS-1:0];
         end
         else begin
            for (int t = 0; t < STALL_NUM_TARGETS; t++)
               if (address == (32'h00001100 + t*8))
                  csr_stall_addr[t] <= writedata;
         end
    end
end

always @(posedge clk) begin
    if (!reset_n) begin
        readdata <= 64'h0;
    end
    else if (read) begin
        if (address[21:0] == 22'h000000)
            readdata <= csr_test_reg & mask[31:0];
        else if ((address[20:0] == 21'h00E00) && config_access)
            readdata <= EX_CAP_HEADER & mask;
        else if (address[21:0] == 22'h001000)
            readdata <= csr_stall_addr[0] & mask;
        else if (address[21:0] == 22'h001008)
            readdata <= {47'h0, csr_stall_cycles, csr_stall_en} & mask;
        else if (address[21:0] == 22'h001010)
            readdata <= csr_stall_addr[1] & mask;
        else if (address[21:0] == 22'h001018)
            readdata <= {{(64-STALL_NUM_TARGETS){1'b0}}, csr_target_en} & mask;
        else if (address[21:0] == 22'h001020)
            readdata <= csr_status_ch0 & mask;
        else if (address[21:0] == 22'h001028)
            readdata <= csr_status_ch1 & mask;
        else begin
            readdata <= 64'h0;
            for (int t = 0; t < STALL_NUM_TARGETS; t++)
               if (address == (32'h00001100 + t*8))
                  readdata <= csr_stall_addr[t] & mask;
        end
    end
end


//Control Logic
enum int unsigned { IDLE = 0,WRITE = 2, READ = 4 } state, next_state;

always_comb begin : next_state_logic
   next_state = IDLE;
      case(state)
      IDLE    : begin 
                   if( write ) begin
                       next_state = WRITE;
                   end
                   else begin
                     if (read) begin  
                       next_state = READ;
                     end
                     else begin
                       next_state = IDLE;
                     end
                   end 
                end
      WRITE     : begin
                   next_state = IDLE;
                end
      READ      : begin
                   next_state = IDLE;
                end
      default : next_state = IDLE;
   endcase
end


always_comb begin
   case(state)
   IDLE    : begin
               waitrequest  = 1'b1;
               readdatavalid= 1'b0;
             end
   WRITE     : begin 
               waitrequest  = 1'b0;
               readdatavalid= 1'b0;
             end
   READ     : begin 
               waitrequest  = 1'b0;
               readdatavalid= 1'b1;
             end
   default : begin 
               waitrequest  = 1'b1;
               readdatavalid= 1'b0;
             end
   endcase
end

always_ff@(posedge clk) begin
   if(~reset_n)
      state <= IDLE;
   else
      state <= next_state;
end

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "5SOp2wqjkMCvRs5H/8cuggoPFnOYOVi/4/bu0Ttyg6RGDyAtuEiXM6zkpXTknpEbjlGv1qJhvF6QsriNG9ARPZ7JmiU3BFWTE9LqHzcFT7tPdS7N8boITkYqxt5v97iIEFF1Inp38Z2ZjsNVDWx8i62p0LDZ9g0btA81KMjFRSEqWO+7zoj3fGDFVT4C92nEu4HzJ3Vn/6UckyxLHS+UBqQ5vFQM1/jRM3utVd+aJiLyT0tTWHutElpdR6LPod0xQGJ5GpD/k9pyD/e/b/pmfI326YmR/w73SjQDXJSlOgbeewGPiiXXE5WqQQf/y1VvgCKdl+UTwSkifqCfIpIDwwHkdX7IehT7oromrvPJIKgEzLNQwOUzmXn0mXmUltG4SKTiOYBrh3lST7OVjWmftivvYRK5m3LYnRblq/dnP/UaOWyp+ajAh6Ka2R3iFhhCV0auOG2Ot8SbjdcHT+E9ZwpCp3Tl2Q2HN2dHqWDp5whVwBA+NXB4dBT3On+4SWv1VbD+idlOqthQWpTQ4oKE4QdIXjITxYwABbT40UeJLVZEq3M/rK3kWH8Ydfh2wq0EAVZphWPouet0Sg7oN3mnNM+J2lcQ6Ir14IftmC4o1CHi3BPsCvjdl8NQO96x7vTma5Pbvw96QwlHP3D1wh6ZHylNYiKy/iT9L8Pl5GVzY7Pxs475v1oFLVyv+tvz/CdweYUZdnW6ZrYc5PRSXwXm8tUOeXpTN69c5R9MILDlBTROA+MVPUQavbYjSgdD9kYNx9Y5pnz9xHsEzGWI5XL8MZJN6GiUVlBcSNoM1UJ2nNNh3IoeJ0YpnbUVEqV/yR07pSnnj8Zax4is8ciy0gzrC8xqDCjioL1A1qTmkzHBkbVFnD4XbWT8HExHx9/fuNsXpj7t0s7S//uoQ6BK5IEpH+MXMZ76bDE/rzUbaQICziMHa3B3k42NrxgK69EEoLXe7rK5Ovly7t/SsLk7pCv9WsITQsjplsx1sh2GJ847mISmwUrHfZVG2VnkBN5UrUTp"
`endif