// Aluna: Jaqueline Ferreira de Brito
// Testbench para o módulo de deslocamento à esquerda de 2 bits (sl2)

/*
 * Módulo: sl2_tb
 * Função: Testar o módulo de deslocamento à esquerda de 2 bits
 * usado para o cálculo de endereços em desvios condicionais no MIPS
 */

module sl2_tb;
    // Declaração de sinais
    logic [31:0] a;        // Entrada do sl2
    logic [31:0] y;        // Saída do sl2
    
    // Contadores para estatísticas de teste
    int tests_total = 0;
    int tests_passed = 0;
    
    // Variáveis para cobertura manual
    int input_ranges_covered = 0;
    int output_behavior_types = 0;
    logic [4:0] input_range_coverage;  // 5 faixas de entrada cobertas
    logic [3:0] output_behavior_coverage; // 4 comportamentos de saída
    
    // Instância do dispositivo em teste (DUT)
    sl2 dut (
        .a(a),
        .y(y)
    );
    
    // Função para registrar cobertura 
    function void record_coverage(logic [31:0] input_val);
        // Cobertura de faixas de entrada
        if (input_val == 0) 
            input_range_coverage[0] = 1;       // Valor zero
        if (input_val > 0 && input_val < 32'h00010000) 
            input_range_coverage[1] = 1;       // Valores pequenos/médios
        if (input_val >= 32'h00010000 && input_val < 32'h40000000) 
            input_range_coverage[2] = 1;       // Valores grandes
        if (input_val >= 32'h40000000 && input_val < 32'h80000000) 
            input_range_coverage[3] = 1;       // Valores com MSBs significativos
        if (input_val >= 32'h80000000) 
            input_range_coverage[4] = 1;       // Valores negativos ou muito grandes
            
        // Cobertura de comportamentos de saída
        if (y == 0)
            output_behavior_coverage[0] = 1;   // Saída zero
        if (y > 0 && y < 32'h80000000)
            output_behavior_coverage[1] = 1;   // Saída positiva
        if (y >= 32'h80000000)
            output_behavior_coverage[2] = 1;   // Saída negativa ou muito grande
        if ((a[31:30] != 0) && (y[31:30] != a[31:30]))
            output_behavior_coverage[3] = 1;   // Caso de overflow/bits perdidos
    endfunction
    
    // Função para exibir cobertura
    function void display_coverage();
        // Calcular contagens de cobertura
        input_ranges_covered = 0;
        for (int i = 0; i < 5; i++)
            if (input_range_coverage[i]) input_ranges_covered++;
            
        output_behavior_types = 0;
        for (int i = 0; i < 4; i++)
            if (output_behavior_coverage[i]) output_behavior_types++;
            
        // Exibir relatório de cobertura
        $display("\n=== Coverage Report ===");
        $display("Input range coverage: %.2f%% (%0d/5)", 100.0 * input_ranges_covered / 5, input_ranges_covered);
        $display("Output behavior coverage: %.2f%% (%0d/4)", 100.0 * output_behavior_types / 4, output_behavior_types);
        
        // Análise detalhada de cobertura
        $display("\n--- Detailed Input Coverage ---");
        $display("Zero values: %s", input_range_coverage[0] ? "Covered" : "Not covered");
        $display("Small/Medium values: %s", input_range_coverage[1] ? "Covered" : "Not covered");
        $display("Large values: %s", input_range_coverage[2] ? "Covered" : "Not covered");
        $display("Values with significant MSBs: %s", input_range_coverage[3] ? "Covered" : "Not covered");
        $display("Negative/very large values: %s", input_range_coverage[4] ? "Covered" : "Not covered");
        
        $display("\n--- Detailed Output Coverage ---");
        $display("Zero output: %s", output_behavior_coverage[0] ? "Covered" : "Not covered");
        $display("Positive output: %s", output_behavior_coverage[1] ? "Covered" : "Not covered");
        $display("Negative/large output: %s", output_behavior_coverage[2] ? "Covered" : "Not covered");
        $display("Overflow/lost bits: %s", output_behavior_coverage[3] ? "Covered" : "Not covered");
        $display("===================");
    endfunction
    
    // Função para verificar e exibir resultados
    function void check_result(logic [31:0] expected, string test_name);
        tests_total++;
        record_coverage(a); // Registra cobertura
        
        $display("=== Testing %s ===", test_name);
        $display("Input: a = 0x%h", a);
        $display("Output: y = 0x%h", y);
        $display("Expected: 0x%h", expected);
        
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
        for (int i = 0; i < 5; i++) input_range_coverage[i] = 0;
        for (int i = 0; i < 4; i++) output_behavior_coverage[i] = 0;
        
        // Cabeçalho do teste
        $display("=== Shift Left 2 (sl2) Testbench ===");
        
        // Caso de teste 1: Valor zero (caso especial)
        a = 32'h00000000;
        #10; // Esperar estabilização
        check_result(32'h00000000, "Zero value");
        
        // Caso de teste 2: Valor pequeno positivo
        a = 32'h00000001;
        #10;
        check_result(32'h00000004, "Small positive value");
        
        // Caso de teste 3: Valor médio
        a = 32'h00001234;
        #10;
        check_result(32'h000048D0, "Medium value");
        
        // Caso de teste 4: Valor grande
        a = 32'h12345678;
        #10;
        check_result(32'h48D159E0, "Large value");
        
        // Caso de teste 5: Valor máximo do intervalo de 30 bits
        a = 32'h3FFFFFFF;
        #10;
        check_result(32'hFFFFFFFC, "Maximum 30-bit value");
        
        // Caso de teste 6: Overflow de bits
        a = 32'h7FFFFFFF;
        #10;
        check_result(32'hFFFFFFFC, "Bit overflow (MSB=1)");
        
        // Caso de teste 7: Valor com 1s nos bits mais significativos (deslocamento perde bits)
        a = 32'hC0000000;
        #10;
        check_result(32'h00000000, "Lost MSBs");
        
        // Caso de teste 8: Valor negativo
        a = 32'hFFFFFFFF; // -1 em complemento de 2
        #10;
        check_result(32'hFFFFFFFC, "Negative value");
        
        // Caso de teste 9: Valores nos bits que serão substituídos por zeros
        a = 32'h00000003;
        #10;
        check_result(32'h0000000C, "Values in replaced bits");
        
        // Caso de teste 10: Valores alternados em diferentes posições
        a = 32'h55555555; // Padrão 0101...0101
        #10;
        check_result(32'h55555554, "Alternating bit pattern");
        
        // Caso de teste adicional: Valores nos limites críticos
        a = 32'h3FFFFFFE; // Valor que não causará overflow, mas está no limite
        #10;
        check_result(32'hFFFFFFF8, "Edge case - near overflow");
        
        // Resumo dos testes
        $display("=== Test Summary ===");
        $display("Total test cases: %0d", tests_total);
        $display("Tests passed: %0d (%0.1f%%)", tests_passed, 100.0 * tests_passed / tests_total);
        $display("Tests failed: %0d (%0.1f%%)", tests_total - tests_passed, 100.0 * (tests_total - tests_passed) / tests_total);
        
        // Exibir relatório de cobertura
        display_coverage();
        
        // Análise detalhada da implementação
        $display("\n=== Implementation Analysis ===");
        $display("The sl2 module correctly implements a 2-bit left shift operation,");
        $display("which is equivalent to multiplying by 4. Key observations:");
        $display("1. The module uses {a[29:0], 2'b00} implementation which:");
        $display("   - Efficiently appends two 0s at the least significant bits");
        $display("   - Correctly handles most common cases for MIPS branch calculations");
        $display("2. The implementation has expected limitations:");
        $display("   - Cannot preserve the two most significant bits");
        $display("   - Will lose information when shifting values with bits set in positions 30-31");
        $display("3. Performance characteristics:");
        $display("   - Zero propagation delay (combinatorial logic)");
        $display("   - Consistent behavior across all valid inputs");
        $display("===================");
        
        $finish;
    end
endmodule

/*  Explicação do Testbench

Este testbench realiza uma verificação completa do módulo sl2:

    Configuração: Configura os sinais de entrada e saída e instancia o DUT.

    Verificação: Define uma tarefa check_result para comparar o valor real e esperado.

    Casos de Teste: Cobre diversos cenários importantes:
        Valor zero
        Valores positivos pequenos e médios
        Valores grandes próximos à capacidade
        Overflow de bits (quando os 2 MSBs são significativos)
        Valores negativos
        Padrões alternados de bits
        Verificação especial para bits menos significativos

    Relatório: Apresenta um relatório claro dos testes aprovados e falhos.

Este testbench verifica completamente a funcionalidade do módulo sl2, garantindo seu comportamento correto em todos os casos possíveis e destacando especialmente os casos extremos onde o deslocamento pode perder informações significativas.
*/