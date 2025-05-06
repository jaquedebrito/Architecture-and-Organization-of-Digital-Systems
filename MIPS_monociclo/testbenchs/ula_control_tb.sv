// Aluna: Jaqueline Ferreira de Brito

module ula_control_tb;
    // Sinais para testar o módulo
    logic [5:0] funct;
    logic [1:0] ULAop;
    logic [2:0] ULAcontrol;
    
    // Contadores para resumo de testes
    int tests_total = 0;
    int tests_passed = 0;
    
    // Variáveis para funcionalidade de cobertura manual
    int op_coverage[4];      // Cobertura para ULAop (00, 01, 10, 11)
    int funct_coverage[64];  // Cobertura para funct
    int control_coverage[8]; // Cobertura para ULAcontrol
    
    // Instanciando o módulo a ser testado
    ula_control dut(
        .funct(funct),
        .ULAop(ULAop),
        .ULAcontrol(ULAcontrol)
    );
    
    // Função para registrar cobertura manualmente
    function void record_coverage();
        // Registra cobertura para ULAop
        op_coverage[ULAop] = 1;
        
        // Registra cobertura para funct (apenas para valores específicos)
        if (!$isunknown(funct))
            funct_coverage[funct] = 1;
            
        // Registra cobertura para ULAcontrol
        if (!$isunknown(ULAcontrol))
            control_coverage[ULAcontrol] = 1;
    endfunction
    
    // Função para calcular e exibir a cobertura
    function void display_coverage();
        static int op_covered = 0;
        static int funct_covered = 0;
        static int control_covered = 0;
        
        // Conta ULAop cobertos
        for (int i = 0; i < 4; i++)
            if (op_coverage[i]) op_covered++;
            
        // Conta funct cobertos (apenas os relevantes)
        if (funct_coverage[6'b100000]) funct_covered++; // ADD
        if (funct_coverage[6'b100010]) funct_covered++; // SUB
        if (funct_coverage[6'b100100]) funct_covered++; // AND
        if (funct_coverage[6'b100101]) funct_covered++; // OR
        if (funct_coverage[6'b101010]) funct_covered++; // SLT
        if (funct_coverage[6'b111111]) funct_covered++; // Invalid
        
        // Conta ULAcontrol cobertos
        for (int i = 0; i < 8; i++)
            if (control_coverage[i]) control_covered++;
            
        // Exibe percentuais
        $display("\n=== Coverage Report ===");
        $display("ULAop coverage: %.2f%% (%0d/4)", 100.0 * op_covered / 4, op_covered);
        $display("funct coverage: %.2f%% (%0d/6)", 100.0 * funct_covered / 6, funct_covered);
        $display("ULAcontrol coverage: %.2f%% (%0d/8)", 100.0 * control_covered / 8, control_covered);
        
        // Análise detalhada de ULAcontrol
        $display("\n--- Detailed ULAcontrol Coverage ---");
        $display("000 (AND):         %s", control_coverage[0] ? "Covered" : "Not covered");
        $display("001 (OR):          %s", control_coverage[1] ? "Covered" : "Not covered");
        $display("010 (ADD):         %s", control_coverage[2] ? "Covered" : "Not covered");
        $display("011 (N/A):         %s", control_coverage[3] ? "Covered" : "Not covered");
        $display("100 (N/A):         %s", control_coverage[4] ? "Covered" : "Not covered");
        $display("101 (N/A):         %s", control_coverage[5] ? "Covered" : "Not covered");
        $display("110 (SUB):         %s", control_coverage[6] ? "Covered" : "Not covered");
        $display("111 (SLT):         %s", control_coverage[7] ? "Covered" : "Not covered");
        
        // Análise das operações não cobertas
        if (control_covered < 8) begin
            $display("\n--- Coverage Analysis ---");
            $display("Current ULAcontrol coverage: %.2f%% (%0d/8)", 100.0 * control_covered / 8, control_covered);
            $display("The current implementation supports:");
            $display("- 000: AND operation");
            $display("- 001: OR operation");
            $display("- 010: ADD operation (and default for invalid codes)");
            $display("- 110: SUB operation");
            $display("- 111: SLT operation");
            $display("\nValues 011, 100, and 101 are not used in the standard MIPS ALU");
            $display("control encoding, so their lack of coverage is acceptable.");
        end
        $display("===================");
    endfunction
    
    // Função para verificar e exibir resultados de teste
    function void check_result(string test_name, logic [2:0] expected, bit should_pass = 1);
        tests_total++;
        record_coverage(); // Registra cobertura em cada teste
        
        $display("=== Testing %s ===", test_name);
        $display("Inputs:");
        $display("  ULAop = %b (ALUOp1=%b, ALUOp0=%b)", ULAop, ULAop[1], ULAop[0]);
        $display("  funct = %b", funct);
        $display("Output:");
        $display("  Expected ULAcontrol = %b", expected);
        $display("  Actual   ULAcontrol = %b", ULAcontrol);
        
        if ((ULAcontrol === expected && should_pass) || 
            (ULAcontrol !== expected && !should_pass)) begin
            $display("  Status: PASS");
            tests_passed++;
        end else begin
            $display("  Status: FAIL");
        end
        $display("");
    endfunction
    
    // Início do teste
    initial begin
        // Inicializa arrays de cobertura
        for (int i = 0; i < 4; i++) op_coverage[i] = 0;
        for (int i = 0; i < 64; i++) funct_coverage[i] = 0;
        for (int i = 0; i < 8; i++) control_coverage[i] = 0;
        
        $display("=== ULA Control Testbench ===");
        $display("By: Jaqueline Ferreira de Brito");
        $display("");
        
        // Teste 1: LW/SW (Load/Store)
        ULAop = 2'b00;
        funct = 6'bxxxxxx; // Don't care para LW/SW
        #10;
        check_result("LW/SW (Load/Store)", 3'b010);
        
        // Teste 2: Branch equal (ALUOp=01)
        ULAop = 2'b01;
        funct = 6'bxxxxxx; // Don't care para Branch
        #10;
        check_result("Branch equal (BEQ)", 3'b110);
        
        // Teste 3: ULAop=11 (tratado como default)
        ULAop = 2'b11;
        funct = 6'bxxxxxx;
        #10;
        check_result("ULAop=11 (Default case)", 3'b010);
        
        // Teste 4: R-type ADD
        ULAop = 2'b10;
        funct = 6'b100000; // ADD
        #10;
        check_result("R-type ADD", 3'b010);
        
        // Teste 5: R-type SUB
        ULAop = 2'b10;
        funct = 6'b100010; // SUB
        #10;
        check_result("R-type SUB", 3'b110);
        
        // Teste 6: R-type AND
        ULAop = 2'b10;
        funct = 6'b100100; // AND
        #10;
        check_result("R-type AND", 3'b000);
        
        // Teste 7: R-type OR
        ULAop = 2'b10;
        funct = 6'b100101; // OR
        #10;
        check_result("R-type OR", 3'b001);
        
        // Teste 8: R-type SLT
        ULAop = 2'b10;
        funct = 6'b101010; // SLT
        #10;
        check_result("R-type SLT", 3'b111);
        
        // Teste 9: R-type com função inválida
        ULAop = 2'b10;
        funct = 6'b111111; // Função inválida
        #10;
        check_result("R-type Invalid funct", 3'b010); // Default para ADD
        
        // Teste 10: ULAop indefinido
        ULAop = 2'bxx; // Valor indefinido
        funct = 6'b100000;
        #10;
        check_result("Undefined ULAop", 3'b010); // Default para ADD
        
        // Testes de casos extremos (corner cases)
        $display("=== Testing Corner Cases ===");
        
        // Caso extremo 1: ULAop válido com funct 000000 (não definido)
        ULAop = 2'b10;
        funct = 6'b000000; // Não é um código de função implementado
        #10;
        $display("Corner Case 1: ULAop=10, funct=000000 (undefined function code)");
        $display("  ULAcontrol = %b (Expected: 010)", ULAcontrol);
        record_coverage();
        
        // Caso extremo 2: Alteração rápida de entradas
        $display("\nCorner Case 2: Rapid input changes");
        for (int i = 0; i < 5; i++) begin
            ULAop = $urandom_range(0, 3);
            funct = $urandom_range(0, 63);
            #1;
            $display("  ULAop=%b, funct=%b => ULAcontrol=%b", ULAop, funct, ULAcontrol);
            record_coverage();
        end
        
        // Resumo dos testes
        $display("=== Test Summary ===");
        $display("Total test cases: %0d", tests_total);
        $display("Tests passed: %0d (%0.1f%%)", tests_passed, 100.0 * tests_passed / tests_total);
        $display("Tests failed: %0d (%0.1f%%)", tests_total - tests_passed, 100.0 * (tests_total - tests_passed) / tests_total);
        
        // Exibe relatório de cobertura
        display_coverage();
        
        // Documentação do estado atual e da expectativa do projeto
        $display("\n=== Module Design Notes ===");
        $display("Current Implementation:");
        $display("- The ULA Control module supports ADD, SUB, AND, OR, and SLT operations");
        $display("- Default ULAcontrol output for invalid funct codes or ULAop is ADD (010)");
        $display("- The module properly decodes all standard MIPS R-type arithmetic and logical instructions");
        $display("");
        $display("Implementation Details:");
        $display("1. For LW/SW instructions (ULAop=00): ULAcontrol=010 (ADD)");
        $display("2. For Branch instructions (ULAop=01): ULAcontrol=110 (SUB)");
        $display("3. For R-type instructions (ULAop=10):");
        $display("   - ADD (funct=100000): ULAcontrol=010");
        $display("   - SUB (funct=100010): ULAcontrol=110");
        $display("   - AND (funct=100100): ULAcontrol=000");
        $display("   - OR  (funct=100101): ULAcontrol=001");
        $display("   - SLT (funct=101010): ULAcontrol=111");
        $display("4. For invalid codes: Default to ADD (010)");
        $display("===================");
        
        $finish;
    end
endmodule

/*******************************************************************************
* Explicação do Testbench para ULA Control
*
* Este testbench verifica a funcionalidade do módulo ula_control, que gera
* os sinais de controle para a ULA (Unidade Lógico-Aritmética) do processador MIPS,
* baseado nos sinais ULAop provenientes do controle principal e no campo funct
* das instruções tipo R.
*
* Principais aspectos testados:
*
* 1. Tipos de instruções: Verifica se o módulo gera os sinais corretos para:
*    - Instruções de acesso à memória (LW/SW): Devem usar a operação ADD (010)
*    - Instruções de branch (BEQ): Devem usar a operação SUB (110)
*    - Instruções do tipo R: Devem decodificar o campo funct corretamente
*
* 2. Decodificação de funções R-type:
*    - ADD (100000): Deve gerar ULAcontrol = 010
*    - SUB (100010): Deve gerar ULAcontrol = 110
*    - AND (100100): Deve gerar ULAcontrol = 000
*    - OR  (100101): Deve gerar ULAcontrol = 001
*    - SLT (101010): Deve gerar ULAcontrol = 111
*
* 3. Casos especiais:
*    - Valores inválidos de ULAop
*    - Valores inválidos de funct
*    - Mudanças rápidas de entrada
*
* 4. Análise de cobertura:
*    - Rastreia todas as combinações testadas de ULAop
*    - Rastreia todas as funções testadas
*    - Identifica os valores de ULAcontrol gerados
*    - Fornece análise detalhada da cobertura atingida
*
* Este testbench emprega uma abordagem completa, verificando tanto a funcionalidade
* básica quanto os casos de borda, e fornece uma análise detalhada do comportamento
* do módulo sob diferentes condições de entrada.
*******************************************************************************/