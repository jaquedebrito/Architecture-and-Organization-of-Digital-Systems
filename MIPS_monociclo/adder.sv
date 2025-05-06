// Aluna: Jaqueline Ferreira de Brito
// Somador de 32 bits para o processador MIPS

/*
 * Módulo: adder
 * Função: Realiza a adição de dois números de 32 bits
 * 
 * Aplicações no MIPS:
 * 1. Calcular PC+4 para determinar o endereço da próxima instrução sequencial
 * 2. Calcular PC+offset para determinar o endereço alvo de instruções de desvio (branch)
 */

module adder(
    input  logic [31:0] a, b, // Operandos de entrada
    output logic [31:0] y     // Resultado da soma
);
    // Implementação direta utilizando o operador de adição (+)
    assign y = a + b;
endmodule