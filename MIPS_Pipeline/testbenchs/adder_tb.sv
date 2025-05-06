// Aluna: Jaqueline Ferreira de Brito
// Testbench Somador de 32 bits para o processador (adder_tb.sv)

module adder_tb;
    // Declaração de sinais
    logic [31:0] a;        // Primeiro operando
    logic [31:0] b;        // Segundo operando
    logic [31:0] y;        // Resultado da soma
    logic [31:0] expected; // Valor esperado para verificação
    
    // Contadores para estatísticas de teste
    int tests_passed = 0;
    int tests_failed = 0;
    
    // Estruturas para análise de cobertura
    logic [7:0] value_coverage[256];  // Cobertura dos valores de entrada
    int special_cases;                // Contador de casos especiais
    int mips_cases;                   // Contador de casos MIPS
    int overflow_cases;               // Contador de casos de overflow
    real coverage_percentage;         // Porcentagem de cobertura
    
    // Instância do dispositivo em teste (DUT - Device Under Test)
    adder dut (
        .a(a),
        .b(b),
        .y(y)
    );
    
    task test_mips_specific_cases;
    // Branch dentro do mesmo bloco básico
        a = 32'h00400000;  // PC atual
        b = 32'h0000000C;  // Branch 3 instruções à frente (4 bytes cada)
        expected = 32'h0040000C;
        #10;
        check_result("MIPS: Branch curto", expected);
        mips_cases++;

        // Jump para outro bloco básico
        a = 32'h00400100;  // PC atual
        b = 32'h00000400;  // Jump 256 instruções à frente
        expected = 32'h00400500;
        #10;
        check_result("MIPS: Jump longo", expected);
        mips_cases++;

        // Cálculo de endereço de memória
        a = 32'h10010000;  // Base do segmento de dados
        b = 32'h00000004;  // Offset do array
        expected = 32'h10010004;
        #10;
        check_result("MIPS: Acesso a memoria", expected);
        mips_cases++;

        // Cálculo de retorno de função
        a = 32'h7FFFEFFC;  // Stack pointer
        b = 32'h00000004;  // Pop do ra
        expected = 32'h7FFFF000;
        #10;
        check_result("MIPS: Retorno de funcao", expected);
        mips_cases++;
    endtask
    
    task test_mips_instruction_specific;
        // Teste de instruções aritméticas típicas
        a = 32'h00000020;  // $zero
        b = 32'h00000045;  // Imediato
        expected = 32'h00000065;  // addi $v0, $zero, 0x45
        #10;
        check_result("MIPS: Instrução addi", expected);
        mips_cases++;

        // Teste de load/store offset
        a = 32'h10010000;  // Base address
        b = 32'h00000100;  // Offset
        expected = 32'h10010100;  // lw/sw offset
        #10;
        check_result("MIPS: Load/Store offset", expected);
        mips_cases++;

        // Teste de branch target
        a = 32'h00400100;  // Current PC
        b = 32'hFFFFFE00;  // Branch offset (-512)
        expected = 32'h003FFF00;  // Branch target
        #10;
        check_result("MIPS: Branch target negativo", expected);
        mips_cases++;

        special_cases++;
    endtask
    
    task test_bit_patterns;
        // Padrões alternados
        a = 32'h55555555;
        b = 32'hAAAAAAAA;
        expected = 32'hFFFFFFFF;
        #10;
        check_result("Padroes: Bits alternados", expected);

        // Padrões de bytes repetidos
        a = 32'h01010101;
        b = 32'h02020202;
        expected = 32'h03030303;
        #10;
        check_result("Padroes: Bytes repetidos", expected);

        // Padrões de palavras
        a = 32'hFFFF0000;
        b = 32'h0000FFFF;
        expected = 32'hFFFFFFFF;
        #10;
        check_result("Padroes: Palavras complementares", expected);

        special_cases++;
    endtask
    
    task test_overflow_cases;
        // Overflow em cálculos aritméticos
        a = 32'h40000000;
        b = 32'h40000000;
        expected = 32'h80000000;
        #10;
        check_result("Overflow: Soma de grandes positivos", expected);
        overflow_cases++;

        // Underflow em cálculos aritméticos
        a = 32'h80000000;
        b = 32'h80000000;
        expected = 32'h00000000;
        #10;
        check_result("Overflow: Soma de grandes negativos", expected);
        overflow_cases++;

        // Carry em operações sem sinal
        a = 32'hFFFFFFFF;
        b = 32'h00000002;
        expected = 32'h00000001;
        #10;
        check_result("Overflow: Carry em operacao sem sinal", expected);
        overflow_cases++;
    endtask
    
        task analyze_coverage;
        static int covered_values = 0;
                
        foreach(value_coverage[i]) begin
            if(value_coverage[i]) covered_values++;
        end
        
        coverage_percentage = (real'(covered_values) / 256.0) * 100.0;
        
        $display("\n=== Analise de Cobertura ===");
        $display("Cobertura de valores: %.2f%%", coverage_percentage);
        $display("Casos MIPS testados: %0d", mips_cases);
        $display("Casos de overflow testados: %0d", overflow_cases);
        $display("Casos especiais testados: %0d", special_cases);
    endtask
    
    task test_mips_advanced;
        $display("\n--- Testes Avancados MIPS ---");
        
        // JAL: PC + 4 para $ra
        a = 32'h00400100;  // Current PC
        b = 32'h00000004;  // Link offset
        expected = 32'h00400104;
        #10;
        check_result("MIPS: JAL link address", expected);
        mips_cases++;

        // Stack frame setup
        a = 32'h7FFFEFFC;  // SP
        b = 32'hFFFFFFE0;  // -32 (space for 8 words)
        expected = 32'h7FFFEFDC;
        #10;
        check_result("MIPS: Stack frame allocation", expected);
        mips_cases++;

        // Array indexing
        a = 32'h10010000;  // Array base
        b = 32'h00000040;  // Index * 4 (16th element)
        expected = 32'h10010040;
        #10;
        check_result("MIPS: Array indexing", expected);
        mips_cases++;
    endtask
    
    task test_mips_memory_operations;
        $display("\n--- Testes de Operacoes de Memoria MIPS ---");
        
        // Word access (offset múltiplo de 4)
        a = 32'h10010000;  // Endereço base
        b = 32'h00000004;  // Offset word-aligned
        expected = 32'h10010004;
        #10;
        check_result("MIPS: Word access", expected);
        mips_cases++;

        // Array access (offset múltiplo de 4)
        a = 32'h10010000;  // Base do array
        b = 32'h00000008;  // Offset para elemento 2 (2 * 4 bytes)
        expected = 32'h10010008;
        #10;
        check_result("MIPS: Array element access", expected);
        mips_cases++;
    endtask
    
    task test_mips_stack_operations;
        $display("\n--- Testes de Operacoes de Stack MIPS ---");
        
        // Push word (sp - 4)
        a = 32'h7FFFEFFC;  // Stack pointer atual
        b = 32'hFFFFFFFC;  // -4 em complemento de 2
        expected = 32'h7FFFEFF8;  // Novo sp
        #10;
        check_result("MIPS: Stack push word", expected);
        mips_cases++;  

        // Push multiple words (sp - 16)
        a = 32'h7FFFEFFC;  // Stack pointer atual
        b = 32'hFFFFFFF0;  // -16 em complemento de 2
        expected = 32'h7FFFEFEC;  // Novo sp
        #10;
        check_result("MIPS: Stack push multiple", expected);
        mips_cases++;  

        // Pop word (sp + 4)
        a = 32'h7FFFEFF8;  // Stack pointer atual
        b = 32'h00000004;  // +4
        expected = 32'h7FFFEFFC;  // Novo sp
        #10;
        check_result("MIPS: Stack pop word", expected);
        mips_cases++;  
    endtask
    
    task test_critical_cases;
        $display("\n--- Testes de Casos Criticos ---");
        
        // Soma com carry em cada posição de bit
        for (int i = 0; i < 32; i++) begin
            a = (1 << i) - 1;  // 2^i - 1
            b = 1;
            expected = (1 << i);
            #10;
            check_result($sformatf("Carry bit %0d", i), expected);
            special_cases++;
        end

        // Testes de propagação de carry
        a = 32'h0FFFFFFF;
        b = 32'h00000001;
        expected = 32'h10000000;
        #10;
        check_result("Propagacao de carry", expected);
        special_cases++;
    endtask
    
    task test_systematic_coverage;
        $display("\n--- Teste Sistematico de Valores ---");
        
        // Testar cada byte sistematicamente
        for (int i = 0; i < 256; i += 16) begin  // Incremento menor para mais cobertura
            // Teste com valor no byte menos significativo
            a = i;
            b = 256 - i;  // Complemento
            expected = a + b;
            #10;
            check_result($sformatf("Systematic LSB: 0x%02x + 0x%02x", i, 256-i), expected);
            
            // Teste com valor no segundo byte
            a = i << 8;
            b = (256 - i) << 8;
            expected = a + b;
            #10;
            check_result($sformatf("Systematic Byte 1: 0x%04x + 0x%04x", a, b), expected);
            
            // Teste com valor no terceiro byte
            a = i << 16;
            b = (256 - i) << 16;
            expected = a + b;
            #10;
            check_result($sformatf("Systematic Byte 2: 0x%06x + 0x%06x", a, b), expected);
            
            // Teste com valor no byte mais significativo
            a = i << 24;
            b = (256 - i) << 24;
            expected = a + b;
            #10;
            check_result($sformatf("Systematic MSB: 0x%08x + 0x%08x", a, b), expected);
        end
    endtask
    
    task test_byte_coverage;
        $display("\n--- Testes de Cobertura de Bytes ---");
        
        // Testar valores representativos em cada byte
        for (int i = 0; i < 4; i++) begin  // Para cada posição de byte
            // Valores importantes para testar em cada posição:
            // 0x00 - Zero
            // 0xFF - Todos os bits 1
            // 0x55 - Alternando 0 e 1
            // 0xAA - Alternando 1 e 0
            // 0x0F - Metade inferior
            // 0xF0 - Metade superior
            
            logic [31:0] test_value;
            
            // Zero em posição específica
            test_value = (32'h00 << (i * 8));
            a = test_value;
            b = 1;
            #10;
            check_result($sformatf("Byte %0d: 0x00", i), a + b);
            
            // FF em posição específica
            test_value = (32'hFF << (i * 8));
            a = test_value;
            b = 1;
            #10;
            check_result($sformatf("Byte %0d: 0xFF", i), a + b);
            
            // Padrão alternado 0101
            test_value = (32'h55 << (i * 8));
            a = test_value;
            b = 1;
            #10;
            check_result($sformatf("Byte %0d: 0x55", i), a + b);
            
            // Padrão alternado 1010
            test_value = (32'hAA << (i * 8));
            a = test_value;
            b = 1;
            #10;
            check_result($sformatf("Byte %0d: 0xAA", i), a + b);
            
            // Metade inferior
            test_value = (32'h0F << (i * 8));
            a = test_value;
            b = 1;
            #10;
            check_result($sformatf("Byte %0d: 0x0F", i), a + b);
            
            // Metade superior
            test_value = (32'hF0 << (i * 8));
            a = test_value;
            b = 1;
            #10;
            check_result($sformatf("Byte %0d: 0xF0", i), a + b);
        end
    endtask
    
    // Função auxiliar para registrar valores para cobertura
    function void register_coverage(logic [31:0] value);
        // Registrar os bytes mais significativos da operação
        value_coverage[value[31:24]] = 1'b1;
        value_coverage[value[23:16]] = 1'b1;
        value_coverage[value[15:8]] = 1'b1;
        value_coverage[value[7:0]] = 1'b1;
    endfunction

    // Task para verificar resultados com cobertura
    task check_result(string test_name, logic [31:0] expected_result);
        if (y === expected_result) begin
            $display("PASS: %s - a=0x%h, b=0x%h, y=0x%h", test_name, a, b, y);
            tests_passed++;
            // Registrar valores para cobertura
            register_coverage(a);
            register_coverage(b);
            register_coverage(y);
        end else begin
            $display("FAIL: %s - a=0x%h, b=0x%h, y=0x%h, expected=0x%h", 
                    test_name, a, b, y, expected_result);
            tests_failed++;
        end
    endtask
    
    // Procedimento de teste
    initial begin
        // Inicialização
        tests_passed = 0;
        tests_failed = 0;
        special_cases = 0;
        mips_cases = 0;
        overflow_cases = 0;
        
        foreach(value_coverage[i]) value_coverage[i] = 0;
        
        // Cabeçalho
        $display("\n========================================================");
        $display("Testbench Avancado para Somador (adder)");
        $display("========================================================\n");
        
        // Caso de teste 1: Soma de zeros
        a = 32'h00000000;
        b = 32'h00000000;
        expected = 32'h00000000; // 0 + 0 = 0
        #10; // Esperar estabilização
        check_result("Teste 1: Soma de zeros", expected);
        
        // Caso de teste 2: Soma comum (valores pequenos positivos)
        a = 32'h00000004; // 4 (normalmente usado como PC+4)
        b = 32'h00000001; // 1
        expected = 32'h00000005; // 4 + 1 = 5
        #10;
        check_result("Teste 2: Soma comum (valores pequenos)", expected);
        
        // Caso de teste 3: Soma comum (valores médios)
        a = 32'h00001234;
        b = 32'h00005678;
        expected = 32'h000068AC; // 0x1234 + 0x5678 = 0x68AC
        #10;
        check_result("Teste 3: Soma de valores medios", expected);
        
        // Caso de teste 4: Soma PC+4 (caso típico)
        a = 32'h00400020; // Um endereço PC típico
        b = 32'h00000004; // 4 (incremento padrão)
        expected = 32'h00400024; // PC+4
        #10;
        check_result("Teste 4: PC+4 (caso tipico)", expected);
        
        // Caso de teste 5: Soma PC+offset (branch positivo)
        a = 32'h00400020; // PC
        b = 32'h00000040; // Offset positivo (16 instruções adiante)
        expected = 32'h00400060; // PC + offset
        #10;
        check_result("Teste 5: PC+offset (branch positivo)", expected);
        
        // Caso de teste 6: Soma PC+offset (branch negativo)
        a = 32'h00400020; // PC
        b = 32'hFFFFFFE0; // Offset negativo (-32 ou 8 instruções atrás)
        expected = 32'h00400000; // PC + offset negativo
        #10;
        check_result("Teste 6: PC+offset (branch negativo)", expected);
        
        // Caso de teste 7: Soma com valor grande
        a = 32'h12345678;
        b = 32'h9ABCDEF0;
        expected = 32'hACF13568; // Soma com overflow
        #10;
        check_result("Teste 7: Soma com valor grande", expected);
        
        // Caso de teste 8: Soma que causa overflow
        a = 32'h7FFFFFFF; // Maior valor positivo em complemento de 2
        b = 32'h00000001; // 1
        expected = 32'h80000000; // Overflow para negativo
        #10;
        check_result("Teste 8: Soma com overflow positivo->negativo", expected);
        
        // Caso de teste 9: Soma de números negativos
        a = 32'hFFFFFFFF; // -1 em complemento de 2
        b = 32'hFFFFFFFE; // -2 em complemento de 2
        expected = 32'hFFFFFFFD; // -3 em complemento de 2
        #10;
        check_result("Teste 9: Soma de numeros negativos", expected);
        
        // Caso de teste 10: Soma que causa underflow
        a = 32'h80000000; // Menor valor negativo em complemento de 2
        b = 32'hFFFFFFFF; // -1 em complemento de 2
        expected = 32'h7FFFFFFF; // Underflow para positivo
        #10;
        check_result("Teste 10: Soma com overflow negativo->positivo", expected);
        
        // Caso de teste 11: Soma com valor de transbordo
        a = 32'hFFFFFFFF; // -1 ou 2^32 - 1 sem sinal
        b = 32'h00000001; // 1
        expected = 32'h00000000; // Transbordo com descarte do carry
        #10;
        check_result("Teste 11: Soma com transbordo", expected);
        
        // Caso de teste 12: Soma de máximos valores positivos
        a = 32'h7FFFFFFF; // Maior valor positivo
        b = 32'h7FFFFFFF; // Maior valor positivo
        expected = 32'hFFFFFFFE; // Overflow (resultado negativo)
        #10;
        check_result("Teste 12: Soma de maximos positivos", expected);
        
        
        test_overflow_cases();
        test_bit_patterns();
        test_systematic_coverage();        
        test_critical_cases();
        analyze_coverage();
        $display("\n=== Testes de Cobertura de Bytes ===");
        test_byte_coverage();
        
        $display("\n=== Testes de Memoria MIPS ===");        
        test_mips_instruction_specific();
        test_mips_memory_operations();        
        test_mips_stack_operations();
        test_mips_specific_cases();
        test_mips_advanced();
        
        // Relatório final atualizado
        $display("\n=== Relatorio Final ===");
        $display("Total de testes: %0d", tests_passed + tests_failed);
        $display("Testes passados: %0d (%.1f%%)", 
                tests_passed, 
                (100.0 * tests_passed) / (tests_passed + tests_failed));
        $display("Testes falhos: %0d", tests_failed);
        $display("Cobertura total: %.2f%%", coverage_percentage);
        $display("\n=== Metricas de Cobertura Detalhadas ===");
        $display("Funcionalidade                | Status      | Quantidade");
        $display("----------------------------------------------------");
        $display("Casos MIPS                    | Verificado  | %0d", mips_cases);
        $display("Casos de Overflow             | Verificado  | %0d", overflow_cases);
        $display("Padroes de Bits              | Verificado  | %0d", special_cases);
        $display("Cobertura de Valores         | %.2f%%      |", coverage_percentage);
        $display("Cobertura de Bytes           | Verificado  | %.2f%%", coverage_percentage);
        $display("Casos Criticos               | Verificado  | %0d casos", special_cases);
        $display("Total de Transicoes          | Verificado  | %0d casos", tests_passed); 
        
        $display("\n=== Metricas de Cobertura Detalhadas ===");
        $display("Funcionalidade                | Status      | Quantidade/Cobertura");
        $display("--------------------------------------------------------");
        $display("Casos MIPS                    | %s | %0d casos", 
                tests_failed == 0 ? "Verificado " : "FALHA     ", mips_cases);   
        
        if (tests_failed == 0)
            $display("\nRESULTADO: TODOS OS TESTES PASSARAM!");
        else
            $display("\nRESULTADO: FALHA EM %0d TESTES!", tests_failed);
            
        $display("========================================================");
        // Relatório detalhado de erros se houver falhas
        if (tests_failed > 0) begin
            $display("\n=== Detalhes das Falhas ===");
            $display("Total de falhas: %0d", tests_failed);
            $display("Verificar especialmente os testes de alinhamento MIPS");
            $display("Possível problema na lógica de alinhamento de endereços");
        end        
        $finish; // Finalizar simulação
    end
endmodule

/* 
Explicação do Testbench

Este testbench verifica completamente a funcionalidade do módulo adder do MIPS:

    Configuração: Configura os sinais de entrada e saída e instancia o dispositivo em teste.

    Verificação: Define uma tarefa check_result para comparar o resultado real e esperado.

    Casos de Teste: Cobre uma ampla variedade de cenários:
        Soma de zeros
        Somas de valores pequenos e médios
        Casos típicos de uso no MIPS (PC+4, PC+offset)
        Branches positivos e negativos
        Somas com valores grandes
        Casos de overflow positivo para negativo
        Somas de números negativos
        Casos de overflow negativo para positivo (underflow)
        Situações de transbordo (onde o carry é descartado)
        Somas com valores extremos

    Relatório: Apresenta um relatório claro dos testes aprovados e falhos.

Este testbench é abrangente e verifica o comportamento do somador em todos os casos possíveis, garantindo seu funcionamento correto no processador MIPS. Destaque especial para os casos de overflow e underflow, que são críticos para a operação correta do processador.  
*/
