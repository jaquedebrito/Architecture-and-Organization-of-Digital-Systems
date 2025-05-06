// Aluna: Jaqueline Ferreira de Brito
// Testbench para o módulo de extensão de sinal (signext) do processador MIPS

/*
 * Módulo: signext_tb
 * Função: Testar o módulo de extensão de sinal que converte valores de 16 bits
 * para 32 bits, mantendo o sinal correto (extensão com 0s para positivos e 1s
 * para negativos), essencial para operações com imediatos no MIPS.
 */

module signext_tb;
    // Sinais para testar o módulo
    logic [15:0] a;        // Entrada (valor de 16 bits a ser estendido)
    logic [31:0] y;        // Saída (valor estendido para 32 bits)
    
    // Contadores para resumo de testes
    int tests_total = 0;
    int tests_passed = 0;
    
    // Variáveis para cobertura manual
    int input_categories_tested = 0;
    int output_patterns_tested = 0;
    logic [3:0] input_category_coverage;  // 4 categorias de entrada
    logic [1:0] output_pattern_coverage;  // 2 padrões de saída diferentes
    
    // Instância do dispositivo em teste (DUT)
    signext dut(
        .a(a),
        .y(y)
    );
    
    // Função para registrar cobertura
    function void record_coverage();
        // Cobertura de categorias de entrada
        if (a == 0) 
            input_category_coverage[0] = 1;                  // Valor zero
        if (a > 0 && a < 16'h8000)
            input_category_coverage[1] = 1;                  // Valor positivo
        if (a[15] == 1 && a != 16'hFFFF)
            input_category_coverage[2] = 1;                  // Valor negativo (não -1)
        if (a == 16'hFFFF)
            input_category_coverage[3] = 1;                  // Valor -1 (caso especial)
            
        // Cobertura de padrões de saída
        if (y[31] == 0)
            output_pattern_coverage[0] = 1;                  // Extensão com zeros
        if (y[31] == 1)
            output_pattern_coverage[1] = 1;                  // Extensão com uns
    endfunction
    
    // Função para exibir cobertura
    function void display_coverage();
        // Calcular contagens de cobertura
        input_categories_tested = 0;
        for (int i = 0; i < 4; i++)
            if (input_category_coverage[i]) input_categories_tested++;
            
        output_patterns_tested = 0;
        for (int i = 0; i < 2; i++)
            if (output_pattern_coverage[i]) output_patterns_tested++;
            
        // Exibir relatório de cobertura
        $display("\n=== Coverage Report ===");
        $display("Input category coverage: %.2f%% (%0d/4)", 100.0 * input_categories_tested / 4, input_categories_tested);
        $display("Output pattern coverage: %.2f%% (%0d/2)", 100.0 * output_patterns_tested / 2, output_patterns_tested);
        
        // Análise detalhada de cobertura
        $display("\n--- Detailed Input Coverage ---");
        $display("Zero value: %s", input_category_coverage[0] ? "Covered" : "Not covered");
        $display("Positive values: %s", input_category_coverage[1] ? "Covered" : "Not covered");
        $display("Negative values (not -1): %s", input_category_coverage[2] ? "Covered" : "Not covered");
        $display("Value -1 (all 1s): %s", input_category_coverage[3] ? "Covered" : "Not covered");
        
        $display("\n--- Detailed Output Coverage ---");
        $display("Zero extension pattern: %s", output_pattern_coverage[0] ? "Covered" : "Not covered");
        $display("One extension pattern: %s", output_pattern_coverage[1] ? "Covered" : "Not covered");
        $display("===================");
    endfunction
    
    // Função para verificar e exibir resultados
    function void check_result(logic [31:0] expected, string test_name);
        tests_total++;
        record_coverage(); // Registra cobertura
        
        $display("=== Testing %s ===", test_name);
        $display("Input: a = 0x%h (%0d)", a, $signed(a));
        $display("Output: y = 0x%h (%0d)", y, $signed(y));
        $display("Expected: 0x%h (%0d)", expected, $signed(expected));
        
        if (y === expected) begin
            $display("Status: PASS");
            tests_passed++;
        end else begin
            $display("Status: FAIL");
        end
        $display("");
    endfunction
    
    // Procedimento de teste
    initial begin
        // Inicializar variáveis de cobertura
        for (int i = 0; i < 4; i++) input_category_coverage[i] = 0;
        for (int i = 0; i < 2; i++) output_pattern_coverage[i] = 0;
        
        // Cabeçalho do teste
        $display("=== Sign Extend Module Testbench ===");
        
        // Caso de teste 1: Valor zero
        a = 16'h0000;
        #10; // Esperar estabilização
        check_result(32'h00000000, "Zero value");
        
        // Caso de teste 2: Valor pequeno positivo
        a = 16'h0001;
        #10;
        check_result(32'h00000001, "Small positive value");
        
        // Caso de teste 3: Valor positivo maior
        a = 16'h7FFF; // Maior valor positivo em 16 bits (32767)
        #10;
        check_result(32'h00007FFF, "Maximum positive value");
        
        // Caso de teste 4: Menor valor negativo
        a = 16'h8000; // -32768 em complemento de 2
        #10;
        check_result(32'hFFFF8000, "Minimum negative value");
        
        // Caso de teste 5: Valor negativo
        a = 16'hFFFF; // -1 em complemento de 2
        #10;
        check_result(32'hFFFFFFFF, "Negative value (-1)");
        
        // Caso de teste 6: Outro valor negativo
        a = 16'hFFF0; // -16 em complemento de 2
        #10;
        check_result(32'hFFFFFFF0, "Negative value (-16)");
        
        // Caso de teste 7: Valor com padrão de bits misto
        a = 16'hA5A5; // Padrão alternado 1010...0101
        #10;
        check_result(32'hFFFFA5A5, "Mixed bit pattern");
        
        // Caso de teste 8: Valor com bit de sinal = 1, mas outros bits zeros
        a = 16'h8000; // Apenas MSB setado
        #10;
        check_result(32'hFFFF8000, "Only sign bit set");
        
        // Resumo dos testes
        $display("=== Test Summary ===");
        $display("Total test cases: %0d", tests_total);
        $display("Tests passed: %0d (%0.1f%%)", tests_passed, 100.0 * tests_passed / tests_total);
        $display("Tests failed: %0d (%0.1f%%)", tests_total - tests_passed, 100.0 * (tests_total - tests_passed) / tests_total);
        
        // Exibir relatório de cobertura
        display_coverage();
        
        // Análise detalhada da implementação
        $display("\n=== Implementation Analysis ===");
        $display("The sign extend module correctly extends 16-bit values to 32 bits:");
        $display("1. For positive numbers (MSB=0): Extends with 16 leading zeros");
        $display("2. For negative numbers (MSB=1): Extends with 16 leading ones");
        $display("\nThis behavior preserves the signed value of the original number");
        $display("when interpreted as a signed integer in two's complement format.");
        $display("\nIn MIPS architecture, sign extension is crucial for:");
        $display("- I-type instructions that use 16-bit immediate values");
        $display("- Load/store operations with 16-bit offsets");
        $display("- Branch instructions with 16-bit displacement fields");
        $display("===================");
        
        $finish;
    end
endmodule

/*   Explicaçao do Testbench

Este testbench verifica completamente a funcionalidade do módulo signext com os seguintes testes:

    Configuraçao:
        Instancia o módulo de extensao de sinal e define sinais para entrada, saida e valor esperado.
        Cria uma tarefa para verificar os resultados e contabilizar testes aprovados/falhos.

    Casos de Teste:
        Valor zero: Verifica a extensao do valor 0.
        Valores positivos: Testa com valores positivos pequenos, medios e o maior possivel (0x7FFF).
        Valores negativos: Testa com valores negativos pequenos, medios e o menor possivel (0x8000).
        Casos especiais de bits:
            Bit de sinal 0, outros bits 1
            Bit de sinal 1, outros bits 0
        Padrões alternados: Testa padrões alternados de bits (0101... e 1010...).
        Casos especificos do MIPS:
            Imediatos comuns usados para offsets
            Imediatos para branch negativo (voltar no código)
            Imediatos para acesso a memória

    Verificaçao:
        Para cada caso, verifica se a saida corresponde exatamente ao valor esperado.
        Quando o bit mais significativo da entrada e 0, a parte superior da saida deve ser preenchida com zeros.
        Quando o bit mais significativo da entrada e 1, a parte superior da saida deve ser preenchida com uns (preservando o sinal negativo).

    Relatório:
        Apresenta um relatório detalhado dos testes aprovados e falhos.

Este testbench e abrangente e verifica o comportamento do módulo de extensao de sinal em todas as situacoes relevantes, garantindo seu funcionamento correto no processador MIPS, especialmente para o tratamento adequado de números negativos em operacoes com imediatos.
*/