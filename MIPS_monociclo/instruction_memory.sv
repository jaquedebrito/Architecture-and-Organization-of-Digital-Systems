// Aluna: Jaqueline Ferreira de Brito
// Memória de instruções do processador MIPS

/*
 * Módulo: instruction_memory
 * Função: Armazena e disponibiliza as instruções do programa para execução
 *
 * Características:
 * - Capacidade: 64 palavras de 32 bits (256 bytes)
 * - Tipo: ROM (apenas leitura durante a execução)
 * - Acesso: assíncrono (combinacional)
 * - Inicialização: carregada a partir do arquivo "memfile.dat"
 *
 * No contexto do MIPS:
 * - Os endereços são divididos por 4, pois cada instrução ocupa 4 bytes
 * - Para acessar a instrução no endereço físico 0x10, usa-se o índice 4 (0x10/4)
 */

module instruction_memory(
    input  logic [5:0]  addr,     // PC/4 (índice na memória)
    output logic [31:0] instr     // Instrução lida
);
    logic [31:0] RAM [63:0];      // Memória de 64 palavras x 32 bits
    
    // Inicialização da memória a partir do arquivo de programa
    initial
        $readmemh("memfile.dat", RAM);
        
    // Leitura combinacional (sem clock)
    assign instr = RAM[addr];     // Acesso direto ao endereço word-aligned
endmodule