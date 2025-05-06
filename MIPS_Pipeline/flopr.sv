module flopr #(parameter WIDTH = 8) 
(
    input  logic             clk, reset,
    input  logic             en,        // Enable para stall
    input  logic [WIDTH-1:0] d,
    output logic [WIDTH-1:0] q
);
    always_ff @(posedge clk or posedge reset)
        if (reset) q <= 0;
        else if (en) q <= d;  // Só atualiza quando enable=1
endmodule