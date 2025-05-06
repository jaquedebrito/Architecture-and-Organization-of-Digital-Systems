// Aluna: Jaqueline Ferreira de Brito
// Testbench para o multiplexador 2:1 (mux2) do processador MIPS

/*
 * Módulo: mux2_tb
 * Função: Testar o multiplexador 2:1 parametrizável para todas as larguras
 * utilizadas no processador MIPS
 *
 * Este testbench verifica o funcionamento do multiplexador com diferentes
 * larguras de bits (32, 5 e 1), que correspondem aos diferentes usos do
 * multiplexador no processador MIPS.
 */

module mux2_tb;
    // Parâmetros do testbench
    parameter WIDTH_32 = 32;  // Largura para testes de 32 bits (comum no MIPS)
    parameter WIDTH_5 = 5;    // Largura para testes de 5 bits (endereços de registrador)
    parameter WIDTH_1 = 1;    // Largura para testes de 1 bit (sinais de controle)
    
    // Declaração de sinais para o mux de 32 bits
    logic [WIDTH_32-1:0] d0_32, d1_32;
    logic                s_32;
    logic [WIDTH_32-1:0] y_32;
    
    // Declaração de sinais para o mux de 5 bits
    logic [WIDTH_5-1:0]  d0_5, d1_5;
    logic                s_5;
    logic [WIDTH_5-1:0]  y_5;
    
    // Declaração de sinais para o mux de 1 bit
    logic                d0_1, d1_1;
    logic                s_1;
    logic                y_1;
    
    // Contadores para estatísticas de teste
    int tests_passed = 0;
    int tests_failed = 0;
    
    // Instâncias do dispositivo em teste com diferentes larguras
    mux2 #(WIDTH_32) dut_32bits (
        .d0(d0_32),
        .d1(d1_32),
        .s(s_32),
        .y(y_32)
    );
    
    mux2 #(WIDTH_5) dut_5bits (
        .d0(d0_5),
        .d1(d1_5),
        .s(s_5),
        .y(y_5)
    );
    
    mux2 #(WIDTH_1) dut_1bit (
        .d0(d0_1),
        .d1(d1_1),
        .s(s_1),
        .y(y_1)
    );
    
    // Tarefa para verificar resultados de 32 bits
    task check_result_32(string test_name, logic [WIDTH_32-1:0] expected);
        if (y_32 === expected) begin
            $display("PASS: %s - d0=0x%h, d1=0x%h, s=%b, y=0x%h", 
                     test_name, d0_32, d1_32, s_32, y_32);
            tests_passed++;
        end else begin  // Corrigido: adicionado "end"
            $display("FAIL: %s - d0=0x%h, d1=0x%h, s=%b, y=0x%h, expected=0x%h", 
                     test_name, d0_32, d1_32, s_32, y_32, expected);
            tests_failed++;
        end
    endtask
    
    // Tarefa para verificar resultados de 5 bits
    task check_result_5(string test_name, logic [WIDTH_5-1:0] expected);
        if (y_5 === expected) begin
            $display("PASS: %s - d0=0x%h, d1=0x%h, s=%b, y=0x%h", 
                     test_name, d0_5, d1_5, s_5, y_5);
            tests_passed++;
        end else begin
            $display("FAIL: %s - d0=0x%h, d1=0x%h, s=%b, y=0x%h, expected=0x%h", 
                     test_name, d0_5, d1_5, s_5, y_5, expected);
            tests_failed++;
        end
    endtask
    
    // Tarefa para verificar resultados de 1 bit
    task check_result_1(string test_name, logic expected);
        if (y_1 === expected) begin
            $display("PASS: %s - d0=%b, d1=%b, s=%b, y=%b", 
                     test_name, d0_1, d1_1, s_1, y_1);
            tests_passed++;
        end else begin
            $display("FAIL: %s - d0=%b, d1=%b, s=%b, y=%b, expected=%b", 
                     test_name, d0_1, d1_1, s_1, y_1, expected);
            tests_failed++;
        end
    endtask
    
    // Procedimento de teste
    initial begin
        // Cabeçalho do teste
        $display("Iniciando testes para o módulo Multiplexador 2:1 (mux2)");
        $display("----------------------------------------");
        
        // TESTES COM MUX DE 32 BITS (comum para dados no MIPS)
        $display("\n=== TESTES COM MUX DE 32 BITS ===");
        
        // Caso 1: Seleção de d0 (s=0)
        d0_32 = 32'h12345678;
        d1_32 = 32'hABCDEF01;
        s_32 = 0;
        #10; // Esperar estabilização
        check_result_32("32-bits, s=0", 32'h12345678);
        
        // Caso 2: Seleção de d1 (s=1)
        s_32 = 1;
        #10;
        check_result_32("32-bits, s=1", 32'hABCDEF01);
        
        // Caso 3: Valores zero
        d0_32 = 32'h00000000;
        d1_32 = 32'h00000000;
        s_32 = 0;
        #10;
        check_result_32("32-bits, ambos zeros, s=0", 32'h00000000);
        
        s_32 = 1;
        #10;
        check_result_32("32-bits, ambos zeros, s=1", 32'h00000000);
        
        // Caso 4: Valores típicos do MIPS (PC+4 vs PCBranch)
        d0_32 = 32'h00400004; // PC+4
        d1_32 = 32'h00400020; // PCBranch
        s_32 = 0; // Sem branch
        #10;
        check_result_32("32-bits, PC+4 vs PCBranch, sem branch", 32'h00400004);
        
        s_32 = 1; // Com branch
        #10;
        check_result_32("32-bits, PC+4 vs PCBranch, com branch", 32'h00400020);
        
        // Caso 5: Valores com padrão alternado
        d0_32 = 32'h55555555; // Padrão 01010101...
        d1_32 = 32'hAAAAAAAA; // Padrão 10101010...
        s_32 = 0;
        #10;
        check_result_32("32-bits, padrao alternado, s=0", 32'h55555555);
        
        s_32 = 1;
        #10;
        check_result_32("32-bits, padrao alternado, s=1", 32'hAAAAAAAA);
        
        // TESTES COM MUX DE 5 BITS (para seleção de registradores)
        $display("\n=== TESTES COM MUX DE 5 BITS ===");
        
        // Caso 1: Seleção básica com endereços de registradores
        d0_5 = 5'b01010; // rt = 10
        d1_5 = 5'b11001; // rd = 25
        s_5 = 0; // Selecionar rt (instrução tipo I)
        #10;
        check_result_5("5-bits, registradores, s=0", 5'b01010);
        
        s_5 = 1; // Selecionar rd (instrução tipo R)
        #10;
        check_result_5("5-bits, registradores, s=1", 5'b11001);
        
        // Caso 2: Registrador zero ($0) e valor máximo
        d0_5 = 5'b00000; // $0
        d1_5 = 5'b11111; // $31
        s_5 = 0;
        #10;
        check_result_5("5-bits, $0 vs $31, s=0", 5'b00000);
        
        s_5 = 1;
        #10;
        check_result_5("5-bits, $0 vs $31, s=1", 5'b11111);
        
        // Caso 3: Valores típicos em instruções MIPS
        d0_5 = 5'b00010; // $2 (v0)
        d1_5 = 5'b00100; // $4 (a0)
        s_5 = 0;
        #10;
        check_result_5("5-bits, $2 vs $4, s=0", 5'b00010);
        
        s_5 = 1;
        #10;
        check_result_5("5-bits, $2 vs $4, s=1", 5'b00100);
        
        // TESTES COM MUX DE 1 BIT (para sinais de controle)
        $display("\n=== TESTES COM MUX DE 1 BIT ===");
        
        // Caso 1: Seleção de bits simples
        d0_1 = 0;
        d1_1 = 1;
        s_1 = 0;
        #10;
        check_result_1("1-bit, d0=0 d1=1, s=0", 0);
        
        s_1 = 1;
        #10;
        check_result_1("1-bit, d0=0 d1=1, s=1", 1);
        
        // Caso 2: Ambas as entradas iguais
        d0_1 = 1;
        d1_1 = 1;
        s_1 = 0;
        #10;
        check_result_1("1-bit, d0=1 d1=1, s=0", 1);
        
        s_1 = 1;
        #10;
        check_result_1("1-bit, d0=1 d1=1, s=1", 1);
        
        d0_1 = 0;
        d1_1 = 0;
        s_1 = 0;
        #10;
        check_result_1("1-bit, d0=0 d1=0, s=0", 0);
        
        s_1 = 1;
        #10;
        check_result_1("1-bit, d0=0 d1=0, s=1", 0);
        
        // Relatório final
        $display("----------------------------------------");
        $display("Testes concluidos:");
        $display("Testes aprovados: %0d", tests_passed);
        $display("Testes falhos: %0d", tests_failed);
        if (tests_failed == 0)
            $display("TODOS OS TESTES PASSARAM!");
        else
            $display("ALGUM TESTE FALHOU!");
        $display("----------------------------------------");
        
        $finish; // Finalizar simulação
    end
endmodule

/*   Explicação do Testbench

Este testbench verifica completamente a funcionalidade do módulo mux2 parametrizável com os seguintes testes:

    Configuração:
        Instancia três versões do multiplexador com larguras diferentes:
            32 bits: comum para dados no MIPS (valores de registradores, resultados da ALU)
            5 bits: para endereços de registradores
            1 bit: para sinais de controle
        Define tarefas específicas para verificar os resultados de cada largura.

    Casos de Teste para 32 bits:
        Seleção básica: Testa a seleção entre dois valores distintos.
        Valores zero: Verifica o comportamento quando ambas as entradas são zero.
        Valores típicos do MIPS: Testa com endereços típicos como PC+4 vs PCBranch.
        Padrões alternados: Testa com padrões de bits alternados.

    Casos de Teste para 5 bits:
        Seleção de registradores: Testa a seleção entre registradores rt e rd.
        Registrador especial: Testa com $0 e $31 (registradores especiais no MIPS).
        Registradores comuns: Testa com registradores frequentemente usados no MIPS.

    Casos de Teste para 1 bit:
        Seleção de bits: Testa a seleção entre 0 e 1.
        Entradas iguais: Verifica o comportamento quando ambas as entradas são iguais.

    Verificação:
        Para cada caso, verifica se a saída corresponde exatamente ao valor esperado com base no sinal de seleção.
        Usa tarefas separadas para verificar cada largura de multiplexador.

    Relatório:
        Apresenta um relatório detalhado dos testes aprovados e falhos.

Este testbench é abrangente e verifica o comportamento do multiplexador 2:1 em todas as larguras e situações comuns no processador MIPS, garantindo seu funcionamento correto em todos os contextos onde é usado no datapath.
*/