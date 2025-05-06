// Aluna: Jaqueline Ferreira de Brito
// Testbench para a ULA (Unidade Lógico-Aritmética) do processador MIPS

module ula_tb;
    // Sinais para teste
    logic [31:0] a, b;
    logic [2:0]  ULAcontrol;
    logic [31:0] result;
    logic        zero;
    
    // Contadores para Estatisticas por Operacao
    integer op_tests[string];
    integer op_errors[string];
    string operations[5]; // Para armazenar os nomes das operações
    int op_count;
    
    // Instância da ULA a ser testada
    ula dut(
        .a(a),
        .b(b),
        .ULAcontrol(ULAcontrol),
        .result(result),
        .zero(zero)
    );
    
    // Variáveis para verificação
    string op_name;
    logic [31:0] expected_result;
    logic expected_zero;
    integer test_number = 0;
    integer errors = 0;
    
    // Função para obter o nome da Operacao baseado no código de controle
    function string get_op_name(logic [2:0] control);
        case(control)
            3'b000: return "AND";
            3'b001: return "OR";
            3'b010: return "ADD";
            3'b110: return "SUB";
            3'b111: return "SLT";
            default: return $sformatf("UNKNOWN(%b)", control);
        endcase
    endfunction
    
    // Tarefa para verificar o resultado de um teste
    task check_result;
        input string test_desc;
        begin
            test_number = test_number + 1;
            op_name = get_op_name(ULAcontrol);
            
            // Atualiza contadores de Estatisticas
            if (!op_tests.exists(op_name)) begin
                op_tests[op_name] = 0;
                op_errors[op_name] = 0;
                operations[op_count] = op_name;
                op_count++;
            end
            op_tests[op_name]++;
            
            $write("Test #%0d: %s - %s: ", test_number, op_name, test_desc);
            
            if (result === expected_result && zero === expected_zero) begin
                $display("PASSED");
            end else begin
                $display("FAILED");
                $display("    a = %0d (0x%0h), b = %0d (0x%0h)", a, a, b, b);
                $display("    Expected: result = %0d (0x%0h), zero = %0b", expected_result, expected_result, expected_zero);
                $display("    Actual:   result = %0d (0x%0h), zero = %0b", result, result, zero);
                errors = errors + 1;
                op_errors[op_name]++;
            end
        end
    endtask
    
     // Início do teste
    initial begin
        // Inicialização de variáveis
        op_count = 0;
        
        // Cabeçalho do teste
        $display("=================================================================");
        $display("=== ULA Testbench ===");
        $display("=================================================================");
        
        // Inicialização dos contadores
        op_tests["AND"] = 0;
        op_tests["OR"]  = 0;
        op_tests["ADD"] = 0;
        op_tests["SUB"] = 0;
        op_tests["SLT"] = 0;
        
        op_errors["AND"] = 0;
        op_errors["OR"]  = 0;
        op_errors["ADD"] = 0;
        op_errors["SUB"] = 0;
        op_errors["SLT"] = 0;
        
        // Armazene os nomes das operações no array
        operations[0] = "AND";
        operations[1] = "OR";
        operations[2] = "ADD";
        operations[3] = "SUB";
        operations[4] = "SLT";
        op_count = 5;
        
        // Seção 1: Testes básicos das operações
        $display("\n=== Testes Basicos das Operacoes ===");
        
        // Teste 1: AND operation (positive numbers)
        a = 32'h0000_00FF;
        b = 32'h0000_000F;
        ULAcontrol = 3'b000;  // AND
        expected_result = 32'h0000_000F;  // 255 & 15 = 15
        expected_zero = 0;
        #10;
        check_result("Positive Numbers");
        
        // Teste 2: AND operation (negative numbers)
        a = 32'hFFFF_FF00;  // -256
        b = 32'hFFFF_FFF0;  // -16
        ULAcontrol = 3'b000;  // AND
        expected_result = 32'hFFFF_FF00;
        expected_zero = 0;
        #10;
        check_result("Negative Numbers");
        
        // Teste 3: AND operation (result zero)
        a = 32'h0000_FF00;
        b = 32'h0000_00FF;
        ULAcontrol = 3'b000;  // AND
        expected_result = 32'h0000_0000;
        expected_zero = 1;
        #10;
        check_result("Result Zero");
        
        // Teste 4: OR operation (positive numbers)
        a = 32'h0000_00F0;
        b = 32'h0000_000F;
        ULAcontrol = 3'b001;  // OR
        expected_result = 32'h0000_00FF;  // 240 | 15 = 255
        expected_zero = 0;
        #10;
        check_result("Positive Numbers");
        
        // Teste 5: OR operation (negative numbers)
        a = 32'hFFFF_FF00;  // -256
        b = 32'hFFFF_000F;  // Negativo com bits em posição diferente
        ULAcontrol = 3'b001;  // OR
        expected_result = 32'hFFFF_FF0F;
        expected_zero = 0;
        #10;
        check_result("Mixed Numbers");
        
        // Teste 6: OR operation (zeros)
        a = 32'h0000_0000;
        b = 32'h0000_0000;
        ULAcontrol = 3'b001;  // OR
        expected_result = 32'h0000_0000;
        expected_zero = 1;
        #10;
        check_result("Result Zero");
        
        // Teste 7: ADD operation (positive numbers)
        a = 32'd100;
        b = 32'd50;
        ULAcontrol = 3'b010;  // ADD
        expected_result = 32'd150;
        expected_zero = 0;
        #10;
        check_result("Positive Numbers");
        
        // Teste 8: ADD operation (negative + positive)
        a = 32'hFFFF_FFE2;  // -30
        b = 32'd50;
        ULAcontrol = 3'b010;  // ADD
        expected_result = 32'd20;
        expected_zero = 0;
        #10;
        check_result("Negative + Positive");
        
        // Teste 9: ADD operation (result zero)
        a = 32'd100;
        b = 32'hFFFF_FF9C;  // -100
        ULAcontrol = 3'b010;  // ADD
        expected_result = 32'h0000_0000;
        expected_zero = 1;
        #10;
        check_result("Result Zero");
        
        // Teste 10: ADD operation (overflow)
        a = 32'h7FFF_FFFF;  // Maximum positive signed integer
        b = 32'h0000_0001;  // 1
        ULAcontrol = 3'b010;  // ADD
        expected_result = 32'h8000_0000;  // Overflow to negative
        expected_zero = 0;
        #10;
        check_result("Overflow");
        
        // Teste 11: SUB operation (positive result)
        a = 32'd100;
        b = 32'd50;
        ULAcontrol = 3'b110;  // SUB
        expected_result = 32'd50;  // 100 - 50 = 50
        expected_zero = 0;
        #10;
        check_result("Positive Result");
        
        // Teste 12: SUB operation (negative result)
        a = 32'd50;
        b = 32'd100;
        ULAcontrol = 3'b110;  // SUB
        expected_result = 32'hFFFF_FFCE;  // 50 - 100 = -50
        expected_zero = 0;
        #10;
        check_result("Negative Result");
        
        // Teste 13: SUB operation (result zero)
        a = 32'd100;
        b = 32'd100;
        ULAcontrol = 3'b110;  // SUB
        expected_result = 32'h0000_0000;
        expected_zero = 1;
        #10;
        check_result("Result Zero");
        
        // Teste 14: SLT operation (a < b)
        a = 32'd50;
        b = 32'd100;
        ULAcontrol = 3'b111;  // SLT
        expected_result = 32'h0000_0001;  // 50 < 100, result should be 1
        expected_zero = 0;
        #10;
        check_result("a < b (Positive Numbers)");
        
        // Teste 15: SLT operation (a > b)
        a = 32'd100;
        b = 32'd50;
        ULAcontrol = 3'b111;  // SLT
        expected_result = 32'h0000_0000;  // 100 > 50, result should be 0
        expected_zero = 1;
        #10;
        check_result("a > b (Positive Numbers)");
        
        // Teste 16: SLT operation (a < b, negative numbers)
        a = 32'hFFFF_FFD8;  // -40
        b = 32'hFFFF_FFE2;  // -30
        ULAcontrol = 3'b111;  // SLT
        expected_result = 32'h0000_0001;  // -40 < -30
        expected_zero = 0;
        #10;
        check_result("a < b (Negative Numbers)");
        
        // Teste 17: SLT operation (positive vs negative)
        a = 32'h0000_0005;  // 5
        b = 32'hFFFF_FFFB;  // -5
        ULAcontrol = 3'b111;  // SLT
        expected_result = 32'h0000_0000;  // 5 > -5
        expected_zero = 1;
        #10;
        check_result("a > b (Positive vs Negative)");
        
        // Teste 18: SLT operation (negative vs positive)
        a = 32'hFFFF_FFFB;  // -5
        b = 32'h0000_0005;  // 5
        ULAcontrol = 3'b111;  // SLT
        expected_result = 32'h0000_0001;  // -5 < 5
        expected_zero = 0;
        #10;
        check_result("a < b (Negative vs Positive)");

        // Seção 2: Testes específicos para instruções MIPS
        $display("\n=== Testes Especificos para Instrucoes MIPS ===");
        
        // beq/bne (verificar flag zero)
        a = 32'h00000004;
        b = 32'h00000004;
        ULAcontrol = 3'b110; // SUB
        expected_result = 32'h00000000;
        expected_zero = 1;
        #10;
        check_result("beq equal");

        // addi positivo
        a = 32'h00000004;
        b = 32'h00000001;
        ULAcontrol = 3'b010; // ADD
        expected_result = 32'h00000005;
        expected_zero = 0;
        #10;
        check_result("addi positive");

        // addi negativo (extensão de sinal)
        a = 32'h00000004;
        b = 32'hFFFFFFFF; // -1 em complemento de 2
        ULAcontrol = 3'b010; // ADD
        expected_result = 32'h00000003;
        expected_zero = 0;
        #10;
        check_result("addi negative");
        
        // Testes adicionais de instruções MIPS
        // lui (load upper immediate)
        a = 32'h0000_0000;
        b = 32'h1234_0000; // Immediate value shifted
        ULAcontrol = 3'b001; // OR operation for lui
        expected_result = 32'h1234_0000;
        expected_zero = 0;
        #10;
        check_result("lui");

        // jalr (jump and link register)
        a = 32'h0040_0100; // Current PC
        b = 32'h0000_0004; // Link offset
        ULAcontrol = 3'b010; // ADD
        expected_result = 32'h0040_0104;
        expected_zero = 0;
        #10;
        check_result("jalr link calculation");

        // lw/sw address calculation
        a = 32'h1001_0000; // Base address
        b = 32'h0000_0004; // Offset
        ULAcontrol = 3'b010; // ADD
        expected_result = 32'h1001_0004;
        expected_zero = 0;
        #10;
        check_result("lw/sw address calculation");

        // Seção 3: Testes de casos limites
        $display("\n=== Testes de Casos Limites ===");
        
        // Maior positivo + 1 (overflow)
        a = 32'h7FFFFFFF;
        b = 32'h00000001;
        ULAcontrol = 3'b010; // ADD
        expected_result = 32'h80000000;
        expected_zero = 0;
        #10;
        check_result("MAX_INT + 1");

        // Menor negativo - 1 (underflow)
        a = 32'h80000000;
        b = 32'hFFFFFFFF; // -1
        ULAcontrol = 3'b010; // ADD
        expected_result = 32'h7FFFFFFF;
        expected_zero = 0;
        #10;
        check_result("MIN_INT - 1");
                // Overflow em subtração (positivo - negativo)
        a = 32'h7FFF_FFFF; // Maior positivo
        b = 32'h8000_0000; // Menor negativo
        ULAcontrol = 3'b110; // SUB
        expected_result = 32'hFFFF_FFFF;
        expected_zero = 0;
        #10;
        check_result("MAX_INT - MIN_INT");

        // Overflow em subtração (negativo - positivo)
        a = 32'h8000_0000; // Menor negativo
        b = 32'h7FFF_FFFF; // Maior positivo
        ULAcontrol = 3'b110; // SUB
        expected_result = 32'h0000_0001;
        expected_zero = 0;
        #10;
        check_result("MIN_INT - MAX_INT");

        // Overflow em operações com números negativos
        a = 32'h8000_0000; // Menor negativo
        b = 32'h8000_0000; // Menor negativo
        ULAcontrol = 3'b010; // ADD
        expected_result = 32'h0000_0000;
        expected_zero = 1;
        #10;
        check_result("MIN_INT + MIN_INT");

        // Seção 4: Testes de padrões de bits
        $display("\n=== Testes de Padroes de Bits ===");
        
        // Alternating bits
        a = 32'h55555555;
        b = 32'hAAAAAAAA;
        ULAcontrol = 3'b000; // AND
        expected_result = 32'h00000000;
        expected_zero = 1;
        #10;
        check_result("Alternating bits AND");

        ULAcontrol = 3'b001; // OR
        expected_result = 32'hFFFFFFFF;
        expected_zero = 0;
        #10;
        check_result("Alternating bits OR");
        
        // Seção 5: Testes para valores indefinidos
        $display("\n=== Testes para Valores Indefinidos (ULAcontrol) ===");
        
        // Teste com ULAcontrol indefinido - comportamento esperado como AND
        a = 32'h0000_00FF;
        b = 32'h0000_000F;
        ULAcontrol = 3'bxx0;  // Indefinido, mas último bit é 0 (trata como AND)
        expected_result = 32'h0000_000F;
        expected_zero = 0;
        #10;
        check_result("Indefinido como AND");
        
        // Teste com ULAcontrol indefinido - comportamento esperado como OR
        a = 32'h0000_00F0;
        b = 32'h0000_000F;
        ULAcontrol = 3'bxx1;  // Indefinido, mas último bit é 1 (trata como OR)
        expected_result = 32'h0000_00FF;
        expected_zero = 0;
        #10;
        check_result("Indefinido como OR");

        // Seção 6: Testes de desempenho e estabilidade
        $display("\n=== Testes de Desempenho e Estabilidade ===");
        
        // Teste de propagação de carry
        a = 32'h0FFF_FFFF;
        b = 32'h0000_0001;
        ULAcontrol = 3'b010; // ADD
        expected_result = 32'h1000_0000;
        expected_zero = 0;
        #10;
        check_result("Carry propagation");

        // Teste de alternância rápida de operações
        // AND seguido de OR com mesmos operandos
        a = 32'h5555_5555;
        b = 32'hAAAA_AAAA;
        ULAcontrol = 3'b000; // AND
        expected_result = 32'h0000_0000;
        expected_zero = 1;
        #5; // Metade do tempo normal
        check_result("Quick AND");

        ULAcontrol = 3'b001; // OR
        expected_result = 32'hFFFF_FFFF;
        expected_zero = 0;
        #5; // Metade do tempo normal
        check_result("Quick OR");

        // Teste de estabilidade com operandos alternando
        a = 32'hFFFF_FFFF;
        b = 32'h0000_0000;
        ULAcontrol = 3'b010; // ADD
        expected_result = 32'hFFFF_FFFF;
        expected_zero = 0;
        #5;
        check_result("Alternating operands 1");

        a = 32'h0000_0000;
        b = 32'hFFFF_FFFF;
        ULAcontrol = 3'b010; // ADD
        expected_result = 32'hFFFF_FFFF;
        expected_zero = 0;
        #5;
        check_result("Alternating operands 2");

        // Seção 7: Testes de Condicoes Criticas
        $display("\n=== Testes de Condicoes Criticas ===");
        
        // Máximo carry chain
        a = 32'hFFFF_FFFF;
        b = 32'h0000_0001;
        ULAcontrol = 3'b010; // ADD
        expected_result = 32'h0000_0000;
        expected_zero = 1;
        #10;
        check_result("Maximum carry chain");

        // Alternância de todos os bits
        a = 32'h5555_5555;
        b = 32'hAAAA_AAAA;
        ULAcontrol = 3'b010; // ADD
        expected_result = 32'hFFFF_FFFF;
        expected_zero = 0;
        #10;
        check_result("All bits toggling");
        
        // Resumo dos testes
        $display("=================================================================");
        $display("Resumo dos Testes:");
        $display("  Total de Testes: %0d", test_number);
        $display("  Aprovados: %0d", test_number - errors);
        $display("  Falhas: %0d", errors);
        $display("  Status: %s", (errors == 0) ? "SUCESSO" : "FALHA");
        $display("=================================================================");
        
        // Estatisticas detalhadas por Operacao
        $display("\nEstatisticas Detalhadas por Operacao:");
        
        // Percorrer array de operações
        for (int i = 0; i < op_count; i++) begin
            string current_op;
            current_op = operations[i];
            $display("  %s: %0d testes, %0d erros", 
                    current_op, op_tests[current_op], op_errors[current_op]);
        end
        
        $display("=================================================================");
        $display("Testbench concluido");
        $display("=================================================================");
        
        // Finaliza a simulação
        #10 $finish;
    end
endmodule

/*******************************************************************************
* Explicação do Testbench para ULA (Unidade Lógico-Aritmética)
*
* Este testbench implementa uma verificação completa da ULA do MIPS, testando
* todas as operações implementadas (AND, OR, ADD, SUB, SLT) sob diversas condições,
* incluindo:
*
* 1. Testes básicos de cada operação:
*    - Valores positivos, negativos e zero
*    - Verificação da flag zero
*    - Casos especiais como overflow e underflow
*
* 2. Testes específicos para instruções MIPS:
*    - Instruções beq/bne (verificação do flag zero)
*    - addi (incluindo valores negativos com extensão de sinal)
*    - load/store (cálculo de endereços)
*    - lui, jalr e outras instruções que usam a ULA
*
* 3. Testes de casos limites:
*    - Overflow com números grandes
*    - Underflow com números negativos extremos
*    - Operações com MAX_INT e MIN_INT
*
* 4. Testes de padrões de bits:
*    - Bits alternados (0101... e 1010...)
*    - Verificação de propagação de carry
*
* 5. Testes de valores indefinidos e comportamento com entradas imprevistas
*
* 6. Testes de desempenho e estabilidade
*
* 7. Análise estatística detalhada por operação
*
* O testbench utiliza uma abordagem sistemática, organizando os testes em seções
* lógicas e fornecendo estatísticas detalhadas sobre os resultados.
* Cada teste é verificado contra o resultado esperado e as discrepâncias são
* reportadas com informações detalhadas para facilitar a depuração.
*******************************************************************************/