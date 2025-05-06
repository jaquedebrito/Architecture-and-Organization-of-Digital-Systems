// Aluna: Jaqueline Ferreira de Brito
// Unidade Lógica e Aritmética (ULA) - VERSÃO TOTALMENTE CORRIGIDA

module ula(
    input  logic [31:0] a, b,         // Operandos de entrada
    input  logic [2:0]  ULAcontrol,   // Código da operação a ser realizada
    output logic [31:0] result,       // Resultado da operação
    output logic        zero          // Flag zero (ativa quando result = 0)
);
    // Implementação das operações da ULA
    always_comb begin
        case (ULAcontrol)
            3'b000:  result = a & b;                      // AND lógico (bit a bit)
            3'b001:  result = a | b;                      // OR lógico (bit a bit)
            3'b010:  result = a + b;                      // Adição
            3'b110:  result = a - b;                      // Subtração
            3'b111:  begin
                // SLT corrigido para tratar corretamente comparações com sinal
                if (a[31] != b[31])
                    // Se os sinais são diferentes (um positivo, outro negativo)
                    // O número negativo (bit 31=1) é sempre menor
                    result = a[31] ? 32'd1 : 32'd0;
                else
                    // Se ambos têm o mesmo sinal, a comparação normal funciona
                    result = (a < b) ? 32'd1 : 32'd0;
            end
            default: begin
                // Tratar valores indefinidos baseado no bit menos significativo
                if (ULAcontrol[0] == 0)
                    result = a & b;  // xx0: trata como AND
                else
                    result = a | b;  // xx1: trata como OR
            end
        endcase
        
        // Debug para auxiliar na identificação de problemas
        $display("ULA: a=%h, b=%h, ULAcontrol=%b, result=%h", a, b, ULAcontrol, result);
    end
    
    // Flag zero ativada quando o resultado é zero
    assign zero = (result == 32'b0);
    
endmodule