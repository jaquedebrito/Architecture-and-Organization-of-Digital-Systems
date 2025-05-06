// Aluna: Jaqueline Ferreira de Brito
// Caminho de dados do processador MIPS

/*
 * Módulo: datapath
 * Função: Implementa o caminho de dados do processador MIPS monociclo
 *
 * Este módulo integra todos os componentes responsáveis pelo fluxo de dados:
 * - Program Counter (PC) e lógica de atualização do PC
 * - Banco de registradores para armazenar e acessar os 32 registradores
 * - ULA para realizar operações aritméticas e lógicas
 * - Circuitos para cálculo de endereços de branch e extensão de imediatos
 * - Multiplexadores para selecionar entre diferentes caminhos de dados
 *
 * O fluxo de dados é controlado pelos sinais vindos da unidade de controle
 * como regwrite, memtoreg, ULAsrc, etc.
 */

module datapath(
    input  logic        clk, reset,
    input  logic        memtoreg, pcsrc,     // Sinais de controle para seleção de caminho de dados
    input  logic        ULAsrc, regdst,      // Controle da ULA e seleção de registrador destino
    input  logic        regwrite, memread,   // Controle de escrita em registradores e leitura de memória
    input  logic [2:0]  ULAcontrol,          // Controle da operação da ULA
    output logic        zero,                // Flag zero da ULA (usado para branches)
    output logic [31:0] pc,                  // Program Counter atual
    input  logic [31:0] instr,               // Instrução atual da memória de instruções
    output logic [31:0] ULAout, writedata,   // Resultado da ULA e dado para escrita na memória
    input  logic [31:0] readdata             // Dado lido da memória
);
    // Sinais internos
    logic [4:0]  writereg;                   // Endereço do registrador de destino para escrita
    logic [31:0] pcnext, pcnextbr, pcplus4, pcbranch;  // Sinais para atualização do PC
    logic [31:0] signimm, signimmsh;         // Imediato com extensão de sinal e deslocado
    logic [31:0] srca, srcb;                 // Operandos da ULA
    logic [31:0] result;                     // Resultado a ser escrito no banco de registradores

    // Lógica de atualização do PC
    flopr #(32) pcreg(                       // Registrador do PC
        .clk(clk),
        .reset(reset),
        .d(pcnextbr),     
        .q(pc)
    );

    adder pcadd1(                            // Calcula PC+4 (próxima instrução sequencial)
        .a(pc),
        .b(32'b100),                         // 4 em binário
        .y(pcplus4)
    );

    sl2 immshift(                            // Desloca o imediato 2 bits para a esquerda (multiplica por 4)
        .a(signimm),
        .y(signimmsh)
    );

    adder pcadd2(                            // Calcula endereço de branch (PC+4+offset<<2)
        .a(pcplus4),
        .b(signimmsh),
        .y(pcbranch)
    );

    mux2 #(32) pcbrmux(                      // Seleciona próximo PC (sequencial ou branch)
        .d0(pcplus4),
        .d1(pcbranch),
        .s(pcsrc),
        .y(pcnextbr)      
    );

    // Lógica do banco de registradores
    regfile rf(                              // Banco de 32 registradores
        .clk(clk),
        .we3(regwrite),                      // Habilita escrita quando regwrite=1
        .ra1(instr[25:21]),                  // rs (primeiro registrador fonte)
        .ra2(instr[20:16]),                  // rt (segundo registrador fonte)
        .wa3(writereg),                      // Registrador destino
        .wd3(result),                        // Dado a ser escrito no registrador
        .rd1(srca),                          // Primeiro operando da ULA
        .rd2(writedata)                      // Segundo operando (ou dado para escrita na memória)
    );

    mux2 #(5) wrmux(                         // Seleciona registrador destino (rt ou rd)
        .d0(instr[20:16]),                   // rt (para instruções tipo-I)
        .d1(instr[15:11]),                   // rd (para instruções tipo-R)
        .s(regdst),
        .y(writereg)
    );

    mux2 #(32) resmux(                       // Seleciona fonte do dado para escrita no registrador
        .d0(ULAout),                         // Resultado da ULA
        .d1(readdata),                       // Dado lido da memória
        .s(memtoreg),
        .y(result)
    );

    signext se(                              // Extensão de sinal do imediato
        .a(instr[15:0]),                     // Campo imediato de 16 bits
        .y(signimm)                          // Valor imediato com 32 bits (estendido)
    );

    // Lógica da ULA
    mux2 #(32) srcbmux(                      // Seleciona segundo operando da ULA
        .d0(writedata),                      // Valor do registrador rt
        .d1(signimm),                        // Valor imediato estendido
        .s(ULAsrc),       
        .y(srcb)
    );

    ula mainula(                             // Unidade Lógica e Aritmética
        .a(srca),                            // Primeiro operando (rs)
        .b(srcb),                            // Segundo operando (rt ou imediato)
        .ULAcontrol(ULAcontrol),             // Operação a ser realizada
        .result(ULAout),                     // Resultado da operação
        .zero(zero)                          // Flag zero (1 se resultado=0, usado para branches)
    );

    // Debug para ajudar na verificação
    always @(posedge clk) begin
        $display("PC=%h, Instr=%h", pc, instr);
        $display("ULA: a=%h, b=%h, ctrl=%b, out=%h, zero=%b",
                 srca, srcb, ULAcontrol, ULAout, zero);
        if (regwrite)
            $display("RegWrite: reg=%d, data=%h", writereg, result);
    end

endmodule