// Aluna: Jaqueline Ferreira de Brito
// Memória de dados do processador MIPS

/*
 * Módulo: data_memory
 * Função: Implementa a memória de dados do processador MIPS
 * 
 * Características:
 * - Capacidade: 64 palavras de 32 bits (256 bytes)
 * - Endereçamento: por palavra, com endereços de 6 bits (0-63)
 * - Leitura: assíncrona (combinacional) quando re=1
 * - Escrita: síncrona (na borda de subida do clock) quando we=1
 *
 * Conversão de endereços:
 * - MIPS usa endereçamento por byte (byte-addressable)
 * - Esta implementação usa endereçamento por palavra (word-addressable)
 * - Conversão: índice_na_memória = endereço_físico/4
 * - Exemplo: endereço físico 80 (0x50) corresponde ao índice 20 na memória
 */

module data_memory(
    input  logic        clk,
    input  logic        we,        // Write enable
    input  logic        re,        // Read enable (memread)
    input  logic [5:0]  addr,      // Endereço (64 palavras)
    input  logic [31:0] wd,        // Write data
    output logic [31:0] rd         // Read data
);
    logic [31:0] RAM[63:0];     // 64 palavras de 32 bits
    
    // Inicialização da memória - apenas para simulação
    initial begin
        for (int i = 0; i < 64; i++)
            RAM[i] = '0;
            
        // Valores iniciais para teste
        RAM[20] = 32'h00000005;  // Endereço 0x50 (80 decimal, 20 após divisão por 4)
        RAM[21] = 32'h0000000c;  // Endereço 0x54 (84 decimal, 21 após divisão por 4)
    end
    
    // Leitura combinacional
    always_comb begin
        if (re)
            rd = RAM[addr];
        else
            rd = 32'h0;
    end
    
    // Escrita síncrona
    always @(posedge clk) begin
        if (we) RAM[addr] <= wd;
    end
endmodule