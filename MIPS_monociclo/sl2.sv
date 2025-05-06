// Aluna: Jaqueline Ferreira de Brito
// Módulo de deslocamento à esquerda por 2 bits

/*
 * Módulo: sl2 (Shift Left 2)
 * Função: Desloca um valor 2 bits para a esquerda (multiplica por 4)
 *
 * No processador MIPS, este módulo é crucial para o cálculo de endereços de branch:
 * - Os endereços de memória no MIPS são byte-addressable
 * - Cada instrução ocupa 4 bytes (32 bits)
 * - O offset de branch na instrução é especificado em unidades de instruções
 * - Para converter em bytes, multiplicamos por 4 (deslocamos 2 bits à esquerda)
 *
 * Exemplo:
 * Entrada: 0x00000003 (offset = 3 instruções)
 * Saída:   0x0000000C (offset = 12 bytes = 3 instruções × 4 bytes)
 */

module sl2(
    input  logic [31:0] a,  // Valor de entrada
    output logic [31:0] y   // Valor deslocado 2 bits à esquerda
);
    // Implementa deslocamento à esquerda por 2 bits
    // Concatena os 30 bits menos significativos da entrada com dois zeros
    assign y = {a[29:0], 2'b00};
endmodule