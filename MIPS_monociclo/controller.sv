// Aluna: Jaqueline Ferreira de Brito
// Unidade de Controle do Processador MIPS

/*
 * Módulo: controller
 * Função: Unidade de controle central que coordena os sinais de controle do processador
 *
 * Este módulo integra:
 * - main_control: gera sinais de controle baseados no opcode da instrução
 * - ula_control: define a operação específica da ULA
 * 
 * O módulo funciona decodificando a instrução atual e produzindo sinais
 * que controlam o comportamento do datapath durante a execução da instrução.
 */

module controller(
    // Entradas
    input  logic [5:0] op,     // opcode da instrução
    input  logic [5:0] funct,  // campo funct para instruções tipo-R
    input  logic       zero,   // flag zero da ULA
    
    // Saídas de controle
    output logic       memtoreg,  // Seleciona dado da memória
    output logic       memwrite,  // Habilita escrita na memória
    output logic       memread,   // Habilita leitura da memória
    output logic       pcsrc,     // Seleciona próximo PC
    output logic       ULAsrc,    // Seleciona segundo operando da ULA
    output logic       regdst,    // Seleciona registrador destino
    output logic       regwrite,  // Habilita escrita no banco de registradores
    output logic [2:0] ULAcontrol // Controle da ULA
);
    // Sinais internos
    logic [1:0] ULAop;   // Operação básica da ULA
    logic       branch;   // Sinal de desvio condicional

    // Instância do controle principal
    main_control mc(
        .op(op),
        .memread(memread),
        .memtoreg(memtoreg),
        .memwrite(memwrite),
        .branch(branch),
        .ULAsrc(ULAsrc),
        .regdst(regdst),
        .regwrite(regwrite),
        .ULAop(ULAop)
    );

    // Instância do controle da ULA
    ula_control uc(
        .funct(funct),
        .ULAop(ULAop),
        .ULAcontrol(ULAcontrol)
    );

    // Lógica para desvio condicional - ativa quando branch=1 e zero=1
    assign pcsrc = branch & zero;

endmodule