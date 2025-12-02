module divider (          // 5-bit unsigned integer divider
  input            clk,   // clock
  input            rst,   // reset
  input            go,    // start calculation
  input [4:0]      num,   // input: numerator
  input [4:0]      den,   // input: denominator
  output [4:0]     rem,   // result: remainder
  output reg [4:0] quo,   // result: quotient
  output reg       busy,  // calculation in progress
  output reg       done,  // calculation is complete
  output reg       valid, // result is valid
  output reg       dbz    // divide-by-zero detected!
);

  reg [4:0] den_latched;  // copy of denominator
  reg [5:0] acc;          // accumulator
  reg [2:0] ctr;          // iteration counter   
   
  initial begin
    busy <= 0;
    done <= 0;
    valid <= 0;
    dbz <= 0;
    quo <= 0;
    den_latched <= 0; 
    ctr <= 0;
  end

  assign rem = acc[5:1];

  always @(posedge clk) begin
    if (rst) begin
      busy <= 0;
      done <= 0;
      valid <= 0;
      dbz <= 0;
      quo <= 0;   
      den_latched <= 0; 
      ctr <= 0;
    end else if (go) begin
      valid <= 0;
      ctr <= 0;
      if (den == 5'b00000) begin
        busy <= 0;
        done <= 1;
        dbz <= 1;
      end else begin
        done <= 0;
        busy <= 1;
        dbz <= 0;
        den_latched <= den;
        {acc, quo} <= {5'b0, num, 1'b0};
      end
    end else begin
      if (ctr == 4) begin
	ctr <= 0;
        busy <= 0;
        done <= 1;
        valid <= 1;
      end else begin
	done <= 0;
        ctr <= ctr + 1;
      end
      if (acc >= den_latched) 
        {acc, quo} <= {acc - den_latched, quo, 1'b1};
      else
	{acc, quo} <= {acc, quo, 1'b0};
    end  
  end

`ifdef FORMAL
`ifdef VERIFIC
 // Verification goes here.
`endif
`endif
       
endmodule
