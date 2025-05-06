// Aluna: Jaqueline Ferreira de Brito
// Multiplexador 2:1 parametrizado

/*
 * Módulo: mux2
 * Função: Implementa um multiplexador 2:1 de largura parametrizável
 *
 * Seleciona entre duas entradas baseado em um sinal de seleção:
 * - Se s=0, seleciona d0
 * - Se s=1, seleciona d1
 *
 * Uso no processador MIPS:
 * - Selecionar entre registradores rt e rd como destino de escrita
 * - Escolher entre valor imediato e registrador como segundo operando da ULA
 * - Selecionar entre resultado da ULA ou dado da memória para write-back
 * - Escolher entre PC+4 e endereço de branch como próximo valor do PC
 */

module mux2 #(parameter WIDTH = 8)
(
    input  logic [WIDTH-1:0] d0, d1,  // Dados de entrada
    input  logic             s,       // Sinal de seleção
    output logic [WIDTH-1:0] y        // Saída selecionada
);
    // Implementação usando operador ternário
    assign y = s ? d1 : d0;  // Se s=1 seleciona d1, senão seleciona d0
endmodule