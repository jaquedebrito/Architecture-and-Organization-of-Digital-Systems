module exception_handler(
    input  logic        clk, reset,
    input  logic [31:0] instr,
    input  logic        div_by_zero,         // Divisão por zero detectada
    input  logic        invalid_instr,       // Instrução inválida
    input  logic        mem_access_error,    // Erro de acesso à memória
    output logic        exception,           // Sinaliza exceção
    output logic [31:0] handler_address      // Endereço do tratador de exceção
);
    parameter HANDLER_ADDR = 32'h80000180;   // Endereço padrão do tratador de exceções MIPS
    
    // Tipo de exceção
    logic [4:0] exception_code;
    
    always_comb begin
        exception = div_by_zero | invalid_instr | mem_access_error;
        
        if (div_by_zero)
            exception_code = 5'h01;
        else if (invalid_instr)
            exception_code = 5'h02;
        else if (mem_access_error)
            exception_code = 5'h03;
        else
            exception_code = 5'h00;
            
        handler_address = HANDLER_ADDR;
    end
endmodule