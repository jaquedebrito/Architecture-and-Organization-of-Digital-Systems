// Aluna: Jaqueline Ferreira de Brito
// Módulo top-level do processador MIPS monociclo

/*
 * Módulo: top
 * Função: Módulo principal que integra todos os componentes do processador MIPS monociclo
 *
 * Este módulo conecta:
 * - Memória de instruções (instruction_memory)
 * - Memória de dados (data_memory)
 * - Unidade de controle (controller)
 * - Caminho de dados (datapath)
 *
 * A arquitetura monociclo executa cada instrução em um único ciclo de clock,
 * com todas as operações (busca, decodificação, execução, acesso à memória e
 * write-back) ocorrendo sequencialmente dentro do mesmo ciclo.
 */

module top(
    input  logic        clk, reset,    // Sinais de sistema
    output logic [31:0] writedata,     // Dado a ser escrito na memória
    output logic [31:0] dataadr,       // Endereço de acesso à memória
    output logic        memwrite       // Sinal de escrita na memória
);
    // Sinais internos para interconexão dos módulos
    logic [31:0] pc;                   // Program Counter
    logic [31:0] instr;                // Instrução atual
    logic [31:0] readdata;             // Dado lido da memória
    logic        memtoreg;             // Seleciona entre dado da memória e resultado da ULA
    logic        memread;              // Habilita leitura da memória
    logic        regdst;               // Seleciona registrador destino (rt ou rd)
    logic        regwrite;             // Habilita escrita no banco de registradores
    logic        pcsrc;                // Seleciona próximo PC (sequencial ou branch)
    logic        zero;                 // Flag de resultado zero da ULA
    logic        ULAsrc;               // Seleciona operando da ULA (registrador ou imediato)
    logic [2:0]  ULAcontrol;           // Controla operação da ULA
    
    // Memória de instruções - armazena o programa a ser executado
    instruction_memory imem(
        .addr(pc[7:2]),                // Endereço dividido por 4 (word-aligned)
        .instr(instr)                  // Instrução lida da memória
    );
    
    // Memória de dados - armazena dados utilizados pelo programa
    data_memory dmem(
        .clk(clk),                     // Clock do sistema
        .we(memwrite),                 // Write enable
        .re(memread),                  // Read enable
        .addr(dataadr[7:2]),           // Endereço dividido por 4 (word-aligned)
        .wd(writedata),                // Dado para escrita
        .rd(readdata)                  // Dado lido da memória
    );
    
    // Controlador - gera sinais de controle baseados na instrução
    controller c(
        .op(instr[31:26]),             // Opcode da instrução
        .funct(instr[5:0]),            // Campo funct para instruções tipo-R
        .zero(zero),                   // Flag de zero da ULA (para branches)
        .memtoreg(memtoreg),           // Seleciona fonte de write-back
        .memwrite(memwrite),           // Habilita escrita na memória
        .memread(memread),             // Habilita leitura da memória
        .pcsrc(pcsrc),                 // Controla próximo valor do PC
        .ULAsrc(ULAsrc),               // Seleciona segundo operando da ULA
        .regdst(regdst),               // Seleciona registrador destino
        .regwrite(regwrite),           // Habilita escrita no banco de registradores
        .ULAcontrol(ULAcontrol)        // Controla operação da ULA
    );

    // Datapath - executa operações baseadas nos sinais de controle
    datapath dp(
        .clk(clk),                     // Clock do sistema
        .reset(reset),                 // Sinal de reset
        .memtoreg(memtoreg),           // Seleção de dados para write-back
        .pcsrc(pcsrc),                 // Seleção do próximo PC
        .ULAsrc(ULAsrc),               // Seleção do segundo operando da ULA
        .regdst(regdst),               // Seleção do registrador destino
        .regwrite(regwrite),           // Habilitação de escrita no banco de registradores
        .memread(memread),             // Habilitação de leitura da memória
        .ULAcontrol(ULAcontrol),       // Operação da ULA
        .zero(zero),                   // Flag de zero (resultado zero)
        .pc(pc),                       // Program Counter atual
        .instr(instr),                 // Instrução atual
        .ULAout(dataadr),              // Saída da ULA / endereço de memória
        .writedata(writedata),         // Dado para escrita na memória
        .readdata(readdata)            // Dado lido da memória
    );
endmodule