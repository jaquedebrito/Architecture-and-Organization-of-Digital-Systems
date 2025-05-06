// Aluna: Jaqueline Ferreira de Brito
// Módulo de extensão de sinal para o processador MIPS

/*
 * Módulo: signext
 * Função: Realiza a extensão de sinal de valores de 16 bits para 32 bits
 *
 * No processador MIPS, muitas instruções contêm valores imediatos de 16 bits
 * que precisam ser estendidos para 32 bits para operações na ULA. Esta extensão
 * precisa preservar o sinal (bit mais significativo) para manter corretamente 
 * a representação de números negativos em complemento de 2.
 *
 * Exemplos:
 * - 0x0001 (16 bits, positivo) → 0x00000001 (32 bits, positivo)
 * - 0xFFFF (16 bits, negativo) → 0xFFFFFFFF (32 bits, negativo)
 */

module signext(
    input  logic [15:0] a,  // Valor de entrada de 16 bits
    output logic [31:0] y   // Valor estendido de 32 bits
);
    // Replica o bit mais significativo (bit 15) 16 vezes e concatena com o valor original
    assign y = {{16{a[15]}}, a};
endmodule