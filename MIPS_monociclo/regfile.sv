// Aluna: Jaqueline Ferreira de Brito
// Banco de registradores do processador MIPS

/*
 * Módulo: regfile
 * Função: Implementa o banco de 32 registradores do processador MIPS
 *
 * Características:
 * - 32 registradores de 32 bits cada (designados $0 a $31)
 * - O registrador $0 sempre contém o valor zero (hardwired)
 * - Possui 2 portas de leitura assíncronas (combinacionais)
 * - Possui 1 porta de escrita síncrona (na borda de subida do clock)
 *
 * Este é um componente crítico do datapath que fornece dados para 
 * instruções aritméticas/lógicas e armazena resultados de cálculos.
 */

module regfile(
    input  logic        clk,      // Sinal de clock
    input  logic        we3,      // Write enable
    input  logic [4:0]  ra1, ra2, // Endereços dos registradores para leitura
    input  logic [4:0]  wa3,      // Endereço do registrador para escrita
    input  logic [31:0] wd3,      // Dado a ser escrito
    output logic [31:0] rd1, rd2  // Dados lidos
);
    // 32 registradores de 32 bits cada
    logic [31:0] rf[31:0];
    
    // Inicialização dos registradores para simulação
    initial begin
        for (int i = 0; i < 32; i++)
            rf[i] = 32'h0;  // Inicializa todos os registradores com zero
    end
    
    // Escrita síncrona na borda de subida do clock
    always_ff @(posedge clk) begin
        if (we3) begin
            // Registrador $0 sempre é zero e não pode ser modificado
            if (wa3 != 0) rf[wa3] <= wd3;
        end
    end
    
    // Leitura assíncrona (combinacional)
    // Retorna 0 se o registrador for $0, caso contrário retorna o conteúdo
    assign rd1 = (ra1 != 0) ? rf[ra1] : 0;
    assign rd2 = (ra2 != 0) ? rf[ra2] : 0;
endmodule