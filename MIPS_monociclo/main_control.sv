// Aluna: Jaqueline Ferreira de Brito
// Unidade de controle principal do MIPS

/*
 * Módulo: main_control
 * Função: Decodifica o opcode da instrução e gera os sinais de controle apropriados
 *
 * Este módulo é responsável por interpretar o campo opcode (6 bits) de cada
 * instrução e determinar como o datapath deve se comportar. Ele gera todos os
 * sinais de controle que definem:
 * - Quais registradores serão lidos e escritos
 * - Se a ULA usará um valor imediato ou um registrador
 * - Qual operação será realizada pela ULA
 * - Se haverá acesso à memória de dados
 * - Se ocorrerá um desvio condicional
 */

module main_control(
    // Input
    input  logic [5:0] op,    // opcode da instrução (bits 31-26)

    // Output - Sinais de controle
    output logic regdst,      // RegDst: seleciona registrador destino (1=rd, 0=rt)
    output logic ULAsrc,      // ALUSrc: seleciona segunda entrada da ULA (0=reg, 1=imm)
    output logic memtoreg,    // MemtoReg: seleciona origem do dado para escrita no reg (0=ULA, 1=mem)
    output logic regwrite,    // RegWrite: habilita escrita no banco de registradores
    output logic memread,     // MemRead: habilita leitura da memória
    output logic memwrite,    // MemWrite: habilita escrita na memória
    output logic branch,      // Branch: habilita desvio condicional
    output logic [1:0] ULAop  // ALUOp: controle da operação da ULA {ALUOp1,ALUOp0}
);

    // Definição dos opcodes como parâmetros para melhor legibilidade
    parameter R_FORMAT = 6'b000000;  // Formato R (add, sub, and, or, slt)
    parameter LW       = 6'b100011;  // Load Word
    parameter SW       = 6'b101011;  // Store Word
    parameter BEQ      = 6'b000100;  // Branch if Equal
    parameter ADDI     = 6'b001000;  // Add Immediate
    parameter J        = 6'b000010;  // Jump

    // Lógica combinacional para determinar os sinais de controle
    always_comb begin
        case(op)
            // R-FORMAT (op=000000)
            // Todas as instruções do tipo R compartilham os mesmos sinais de controle
            // A operação específica é determinada pelo ula_control com base no campo funct
            R_FORMAT: begin
                regdst   = 1'b1;  // Usa rd como registrador destino
                ULAsrc   = 1'b0;  // Usa rt como segundo operando da ULA
                memtoreg = 1'b0;  // Escreve resultado da ULA no registrador
                regwrite = 1'b1;  // Habilita escrita no banco de registradores
                memread  = 1'b0;  // Não acessa memória para leitura
                memwrite = 1'b0;  // Não acessa memória para escrita
                branch   = 1'b0;  // Não é uma instrução de branch
                ULAop    = 2'b10; // Código que indica instrução tipo-R
            end

            // LW (op=100011) - Load Word
            // Carrega uma palavra da memória para um registrador
            LW: begin
                regdst   = 1'b0;  // Usa rt como registrador destino
                ULAsrc   = 1'b1;  // Usa valor imediato para cálculo de endereço
                memtoreg = 1'b1;  // Escreve dado da memória no registrador
                regwrite = 1'b1;  // Habilita escrita no banco de registradores
                memread  = 1'b1;  // Habilita leitura da memória
                memwrite = 1'b0;  // Desabilita escrita na memória
                branch   = 1'b0;  // Não é uma instrução de branch
                ULAop    = 2'b00; // Operação de adição para cálculo de endereço
            end

            // SW (op=101011) - Store Word
            // Armazena uma palavra de um registrador na memória
            SW: begin
                regdst   = 1'bx;  // Não relevante - não escreve em registrador
                ULAsrc   = 1'b1;  // Usa valor imediato para cálculo de endereço
                memtoreg = 1'bx;  // Não relevante - não escreve em registrador
                regwrite = 1'b0;  // Desabilita escrita no banco de registradores
                memread  = 1'b0;  // Desabilita leitura da memória
                memwrite = 1'b1;  // Habilita escrita na memória
                branch   = 1'b0;  // Não é uma instrução de branch
                ULAop    = 2'b00; // Operação de adição para cálculo de endereço
            end

            // BEQ (op=000100) - Branch if Equal
            // Desvia se dois registradores forem iguais
            BEQ: begin
                regdst   = 1'bx;  // Não relevante - não escreve em registrador
                ULAsrc   = 1'b0;  // Usa rt para comparação
                memtoreg = 1'bx;  // Não relevante - não escreve em registrador
                regwrite = 1'b0;  // Desabilita escrita no banco de registradores
                memread  = 1'b0;  // Desabilita leitura da memória
                memwrite = 1'b0;  // Desabilita escrita na memória
                branch   = 1'b1;  // Habilita lógica de branch
                ULAop    = 2'b01; // Operação de subtração para comparação
            end
            
            // ADDI (op=001000) - Add Immediate
            // Soma um valor imediato a um registrador
            ADDI: begin
                regdst   = 1'b0;  // Usa rt como registrador destino
                ULAsrc   = 1'b1;  // Usa valor imediato como segundo operando
                memtoreg = 1'b0;  // Escreve resultado da ULA no registrador
                regwrite = 1'b1;  // Habilita escrita no banco de registradores
                memread  = 1'b0;  // Desabilita leitura da memória
                memwrite = 1'b0;  // Desabilita escrita na memória
                branch   = 1'b0;  // Não é uma instrução de branch
                ULAop    = 2'b00; // Operação de adição
            end
            
            // J (op=000010) - Jump
            // Salto incondicional
            J: begin
                regdst   = 1'bx;  // Não relevante - não escreve em registrador
                ULAsrc   = 1'bx;  // Não relevante - ULA não é usada
                memtoreg = 1'bx;  // Não relevante - não escreve em registrador
                regwrite = 1'b0;  // Desabilita escrita no banco de registradores
                memread  = 1'b0;  // Desabilita leitura da memória
                memwrite = 1'b0;  // Desabilita escrita na memória
                branch   = 1'b0;  // Não é uma instrução de branch
                ULAop    = 2'b00; // Valor não relevante, ULA não é usada
            end

            // Instrução não reconhecida ou não implementada
            // Define valores seguros para evitar comportamento imprevisível
            default: begin
                regdst   = 1'b0;  // Valor seguro para síntese
                ULAsrc   = 1'b0;  // Valor seguro para síntese
                memtoreg = 1'b0;  // Valor seguro para síntese
                regwrite = 1'b0;  // Previne escrita indesejada em registradores
                memread  = 1'b0;  // Previne leitura indesejada da memória
                memwrite = 1'b0;  // Previne escrita indesejada na memória
                branch   = 1'b0;  // Previne desvios indesejados
                ULAop    = 2'b00; // Operação segura (adição)
            end
        endcase
    end

endmodule