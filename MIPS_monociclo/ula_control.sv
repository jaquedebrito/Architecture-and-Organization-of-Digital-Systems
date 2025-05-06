// Aluna: Jaqueline Ferreira de Brito
// Controle da Unidade Lógica e Aritmética (ULA)

/*
 * Módulo: ula_control
 * Função: Decodifica os sinais de controle para a ULA com base no ULAop e campo funct
 *
 * Este módulo determina qual operação deve ser realizada pela ULA baseando-se em:
 * - ULAop: Vem do controle principal e indica a classe da operação
 * - funct: Campo de função da instrução (para instruções tipo-R)
 *
 * O código de 3 bits gerado (ULAcontrol) controla diretamente o comportamento da ULA:
 * - 000: AND
 * - 001: OR
 * - 010: ADD
 * - 110: SUB
 * - 111: SLT (Set Less Than)
 */

module ula_control(
    input  logic [1:0] ULAop,       // Código de operação da ULA do controle principal
    input  logic [5:0] funct,       // Campo funct da instrução (bits 5-0)
    output logic [2:0] ULAcontrol   // Sinal de controle para a ULA
);
    always_comb begin
        case(ULAop)
            // Para instruções load/store: sempre usa adição (para cálculo de endereço)
            2'b00: ULAcontrol = 3'b010;  // ADD para lw/sw
            
            // Para instruções de branch: usa subtração (para verificar igualdade)
            2'b01: ULAcontrol = 3'b110;  // SUB para beq
            
            // Para instruções tipo-R: decodifica baseado no campo funct
            2'b10: begin
                case(funct)
                    6'b100000: ULAcontrol = 3'b010; // ADD (funct = 0x20)
                    6'b100010: ULAcontrol = 3'b110; // SUB (funct = 0x22)
                    6'b100100: ULAcontrol = 3'b000; // AND (funct = 0x24)
                    6'b100101: ULAcontrol = 3'b001; // OR  (funct = 0x25)
                    6'b101010: ULAcontrol = 3'b111; // SLT (funct = 0x2A)
                    default:   ULAcontrol = 3'b010; // Default para ADD
                endcase
            end
            
            // Caso default (instruções não suportadas ou mal codificadas)
            default: ULAcontrol = 3'b010;  // Usa ADD como operação segura padrão
        endcase
        
        // Saída de depuração para auxiliar na verificação
        $display("ULAop=%b, ULAcontrol=%b, funct=%b", ULAop, ULAcontrol, funct);
    end
endmodule