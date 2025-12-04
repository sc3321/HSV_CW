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
default clocking cb @ (posedge clk);  
endclocking
assume property (busy |-> !go);

// Task 1
property start_sets_busy_next;
  @(posedge clk)
  disable iff (rst)
    (go && den != 5'b00000) |=> (busy && !valid);
endproperty

assert property (start_sets_busy_next);

// Task 2
property t2_alt;
  @(posedge clk)
  disable iff (rst)
    (go && den != 5'b00000) |=> (busy && !valid)[*5];  // cycles n+1, n+2, n+3, n+4, n+5
endproperty

assert property (t2_alt);

// Task 3
property six_cycles_later;
  @(posedge clk)
  disable iff (rst)
    (go && den != 5'b00000) |-> ##6 (!busy && valid);
endproperty

assert property (six_cycles_later);

// Task 4
property equation_check;
  @(posedge clk)
  disable iff (rst || !go || (den == 5'b00000))  // Ensure go is high and den is non-zero
    (go && den != 5'b00000) |-> ##6 ((num == ($past(den, 6) * quo) + rem));
endproperty

assert property (equation_check);

// Task 5
property den_latch;
  @(posedge clk)
  disable iff (rst)
    ($rose(go) && den != 5'b00000)
    |=> (den_latched == $past(den));
endproperty
assert property (den_latch);

// Task 6
property done_dbz;
  @(posedge clk)
  disable iff (rst)
    ($rose(go) && den == 5'b00000)
    |=> (done && dbz);
endproperty
assert property (done_dbz);

// Task 7
property done_stays_high_except;
  @(posedge clk)
  disable iff (rst)
    (done && !dbz) |=> !done;
endproperty

// Task 8
property rem_smaller_den;
  @(posedge clk)
  disable iff (rst)
    (valid)
      |-> (rem < den_latched);
endproperty

// Task 9
property quo_and_rem;
  @(posedge clk)
  disable iff (rst)
    (valid && !dbz)
    |-> (
      // Case quo = 0: rem must be at most 30
      (quo == 5'd0 && rem <= 5'd30)
      ||
      // Case quo > 0: rem*(quo+1) + quo <= 31
      (quo != 5'd0 &&
       (rem * (quo + 5'd1) + quo <= 5'd31))
    );
endproperty

assert property (quo_and_rem);

// Task 10
genvar q, r;
generate
  for (q = 0; q < 31; q = q + 1) begin : GEN_Q
    for (r = 0; r < 31 ; r = r + 1) begin : GEN_R

      if ( (q == 0 && r <= 30) ||
           (q > 0  && (r * (q + 1) + q <= 31)) ) begin : GEN_QR

        cover property (@(posedge clk)
          disable iff (rst)
          valid && !dbz &&
          quo == q[4:0] &&
          rem == r[4:0]);
      end
    end
  end
endgenerate

// Task 11
property loop_invariant_acc_lt_2den;
  @(posedge clk)
  disable iff (rst)
    (busy && !dbz)
      |-> (acc < (den_latched << 1));
endproperty

assert property (loop_invariant_acc_lt_2den);

`endif
`endif
       
endmodule
