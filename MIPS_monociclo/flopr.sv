// Aluna: Jaqueline Ferreira de Brito
// Registrador com reset assíncrono

/*
 * Módulo: flopr (flip-flop com reset)
 * Função: Implementa um registrador parametrizável com reset assíncrono
 *
 * Características:
 * - Parametrizado pela largura dos dados (WIDTH)
 * - Reset assíncrono (ativo em nível alto)
 * - Armazenamento síncrono na borda de subida do clock
 *
 * Uso no processador MIPS:
 * - Utilizado principalmente como Program Counter (PC)
 * - Também pode ser usado em outros registradores do pipeline
 */

module flopr #(parameter WIDTH = 32)
(
    input  logic             clk, reset,   // Sinais de clock e reset
    input  logic [WIDTH-1:0] d,           // Dado de entrada
    output logic [WIDTH-1:0] q            // Dado armazenado
);
    // Processo síncrono com reset assíncrono
    always_ff @(posedge clk, posedge reset) begin
        if (reset) q <= 0;                // Reset assíncrono - zera a saída imediatamente
        else q <= d;                      // Operação normal - armazena entrada na saída
    end
endmodule