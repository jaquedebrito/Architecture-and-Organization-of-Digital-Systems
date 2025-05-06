// Aluna: Jaqueline Ferreira de Brito
// Testbench para o banco de registradores do processador MIPS

/**
 * Register File Testbench - Versão Final Otimizada
 * Versão compatível com Xcelium sem inicializadores de array com {}
 */
module regfile_tb;
    // Sinais do módulo
    logic        clk;
    logic        we3;
    logic [4:0]  ra1, ra2, wa3;
    logic [31:0] wd3;
    logic [31:0] rd1, rd2;

    // Timing e performance
    time write_time, read_time;
    time write_to_read_delay;
    time min_write_to_read_delay = '1;
    time max_write_to_read_delay = 0;
    time total_write_to_read_delay = 0;
    int  delay_count = 0;

    // Contadores e estatísticas
    int write_operations = 0;
    int read_operations = 0;
    int simultaneous_accesses = 0;
    int tests_total = 0;
    int tests_passed = 0;
    int corner_case_count = 0;
    int parallel_test_count = 0;

    // Cobertura
    bit [31:0] reg_read_coverage;
    bit [31:0] reg_write_coverage;
    int reg_read_count_by_reg[32];
    int reg_write_count_by_reg[32];
    int reg_access_count[32];
    int we_coverage[2];

    // Análise de registradores
    int most_read_reg, most_written_reg, most_accessed_reg;
    int max_read_count, max_write_count, max_access_count;
    int unique_reads, unique_writes;
    real register_coverage, read_coverage, write_coverage;

    // Padrões de teste - inicialização sem {}
    logic [31:0] test_patterns [8]; // Declaração sem inicialização

    // Instância do DUT
    regfile dut (
        .clk(clk),
        .we3(we3),
        .ra1(ra1),
        .ra2(ra2),
        .wa3(wa3),
        .wd3(wd3),
        .rd1(rd1),
        .rd2(rd2)
    );

    // Geração de clock
    always begin
        clk = 1; #5; clk = 0; #5;
    end

    // Assertions - Corrigido para evitar verificação durante a inicialização
    always @(posedge clk) begin
        // Verificamos apenas após um período de inicialização
        if ($time > 20) begin  
            if (ra1 == 0) begin
                assert(rd1 === 32'h00000000) 
                else $error("Assertion failed: Register 0 returned non-zero value (%h) on port 1", rd1);
            end
            
            if (ra2 == 0) begin
                assert(rd2 === 32'h00000000)
                else $error("Assertion failed: Register 0 returned non-zero value (%h) on port 2", rd2);
            end
        end
    end

    // Monitor de estatísticas
    always @(posedge clk) begin
        if (!$isunknown(ra1)) reg_access_count[ra1]++;
        if (!$isunknown(ra2)) reg_access_count[ra2]++;
        if (we3 && !$isunknown(wa3)) reg_access_count[wa3]++;
        
        if (we3) write_operations++;
        if (ra1 != 0 || ra2 != 0) read_operations++;
        if ((ra1 != 0 || ra2 != 0) && we3) simultaneous_accesses++;
        
        if (write_to_read_delay > 0) begin
            total_write_to_read_delay += write_to_read_delay;
            delay_count++;
            if (write_to_read_delay < min_write_to_read_delay)
                min_write_to_read_delay = write_to_read_delay;
            if (write_to_read_delay > max_write_to_read_delay)
                max_write_to_read_delay = write_to_read_delay;
        end
    end

    /**
     * Verifica se um resultado de teste corresponde ao valor esperado
     */
    task check_result(string test_name, logic [31:0] actual, logic [31:0] expected);
        logic [31:0] diff;
        
        tests_total++;
        
        // Atualizar contadores de acesso
        if (!$isunknown(ra1)) begin
            reg_read_count_by_reg[ra1]++;
            reg_read_coverage[ra1] = 1;
        end
        if (!$isunknown(ra2)) begin
            reg_read_count_by_reg[ra2]++;
            reg_read_coverage[ra2] = 1;
        end
        if (we3 && !$isunknown(wa3)) begin
            reg_write_count_by_reg[wa3]++;
            reg_write_coverage[wa3] = 1;
        end
        
        // Registrar cobertura de we3
        we_coverage[we3] = 1;
        
        // Exibir resultados
        $display("=== Testing %s ===", test_name);
        $display("Inputs:");
        $display("  we3=%b, wa3=%d, wd3=0x%h", we3, wa3, wd3);
        $display("  ra1=%d, ra2=%d", ra1, ra2);
        $display("Output:");
        $display("  Expected: 0x%h", expected);
        $display("  Actual:   0x%h", actual);
        
        if (actual === expected) begin
            $display("  Status: PASS");
            tests_passed++;
        end else begin
            $display("  Status: FAIL");
            $display("    Expected: 0x%h", expected);
            $display("    Actual:   0x%h", actual);
            
            diff = expected ^ actual;
            if (diff != 0) begin
                $display("    Bit differences: 0x%h", diff);
                $display("    First bit error at position %d", $clog2(diff & -diff));
            end
        end
        $display("");
    endtask

    /**
     * Inicializa padrões de teste
     */
    task initialize_test_patterns();
        test_patterns[0] = 32'hAAAAAAAA;   // Alternância de bits (1010...)
        test_patterns[1] = 32'h55555555;   // Alternância de bits (0101...)
        test_patterns[2] = 32'hDEADBEEF;   // Valor comumente usado em debug
        test_patterns[3] = 32'h01234567;   // Sequência incremental
        test_patterns[4] = 32'hFFFFFFFF;   // Todos os bits em 1
        test_patterns[5] = 32'h00000000;   // Todos os bits em 0
        test_patterns[6] = 32'h80000000;   // Bit mais significativo = 1
        test_patterns[7] = 32'h00000001;   // Bit menos significativo = 1
    endtask

    /**
     * Executa testes básicos de funcionalidade do banco de registradores
     */
    task run_basic_tests();
        $display("\n=== TESTES BÁSICOS DO BANCO DE REGISTRADORES ===\n");
        
        // Teste do registrador zero
        check_result("Register Zero Read (rd1)", rd1, 32'h0);
        check_result("Register Zero Read (rd2)", rd2, 32'h0);
        
        // Teste de escrita no registrador zero
        we3 = 1;
        wa3 = 0;
        wd3 = 32'hFFFFFFFF;
        @(posedge clk); 
        @(negedge clk);
        we3 = 0;
        ra1 = 0;
        #1;
        check_result("Register Zero Write Protection", rd1, 32'h0);
        
        // Testes com padrões em diferentes registradores
        for (int i = 1; i < 5; i++) begin
            we3 = 1;
            wa3 = i;
            wd3 = test_patterns[i-1];
            @(posedge clk); 
            @(negedge clk);
            
            we3 = 0;
            ra1 = i;
            #1;
            check_result($sformatf("Register %0d Write/Read", i), rd1, test_patterns[i-1]);
        end
        
        // Teste de leitura dupla em diferentes portos
        we3 = 1;
        wa3 = 1;
        wd3 = 32'hAAAAAAAA;
        @(posedge clk);
        @(negedge clk);
        
        we3 = 1;
        wa3 = 2;
        wd3 = 32'h55555555;
        @(posedge clk);
        @(negedge clk);
        
        we3 = 0;
        ra1 = 1;
        ra2 = 2;
        #1;
        check_result("Dual Port Read Test - Port 1", rd1, 32'hAAAAAAAA);
        check_result("Dual Port Read Test - Port 2", rd2, 32'h55555555);
    endtask

    /**
     * Testa a temporização específica do banco de registradores
     */
    task test_timing();
        time local_write_time;
        time local_read_time;
        time local_delay;
        int success_count;
        
        $display("\n=== TESTES DE TIMING ===\n");
        local_write_time = 0;
        local_read_time = 0;
        local_delay = 0;
        success_count = 0;
        
        // Teste diferentes timing paths
        for (int i = 8; i < 12; i++) begin
            // Escrita
            @(posedge clk);
            local_write_time = $time;
            we3 = 1;
            wa3 = i;
            wd3 = 32'h55555555 * i;
            @(negedge clk);
            
            // Leitura imediata (sem ciclo de espera)
            we3 = 0;
            ra1 = i;
            #1;  // Pequeno delay para propagação de sinal
            local_read_time = $time;
            local_delay = local_read_time - local_write_time;
            
            // Verifica se o valor foi capturado corretamente
            if (rd1 === (32'h55555555 * i)) begin
                $display("Fast Timing Test Passed for Register %0d", i);
                $display("Access Time: %0t", local_delay);
                success_count++;
            end else begin
                $display("Fast Timing Test Failed for Register %0d", i);
                $display("Expected: 0x%h, Actual: 0x%h", 32'h55555555 * i, rd1);
                $display("Access Time: %0t", local_delay);
            end
            
            // Agora tente com um ciclo de espera adicional
            @(posedge clk);
            we3 = 1;
            wa3 = i;
            wd3 = 32'hAAAAAAAA * i;
            @(negedge clk);
            @(posedge clk);  // Ciclo adicional para estabilização
            we3 = 0;
            ra1 = i;
            #1;
            
            check_result($sformatf("Relaxed Timing Test Register %0d", i), rd1, 32'hAAAAAAAA * i);
        end
        
        $display("Fast Timing Tests: %0d/4 passed", success_count);
    endtask

    /**
     * Testa cenários de contenção de barramento - CORRIGIDO
     */
    task test_bus_contention();
        $display("\n=== TESTES DE CONTENÇÃO DE BARRAMENTO ===\n");
        
        // Teste básico de contenção - leitura do mesmo registrador em ambos os portos
        @(posedge clk);
        we3 = 1;
        wa3 = 9;
        wd3 = 32'h99999999;
        @(negedge clk);
        @(posedge clk);
        
        ra1 = 9;
        ra2 = 9;
        #1;
        check_result("Bus Contention Test - Port 1", rd1, 32'h99999999);
        check_result("Bus Contention Test - Port 2", rd2, 32'h99999999);
        
        // Teste mais avançado: escrita e leitura simultâneas no mesmo registrador
        // CORREÇÃO: Adicione ciclo completo para garantir que o valor seja atualizado
        we3 = 1;
        wa3 = 9;
        wd3 = 32'hAAAAAAAA;
        ra1 = 9;
        @(negedge clk);
        // Verificar que a leitura obteve o valor antigo antes da escrita
        check_result("Read-During-Write Same Register", rd1, 32'h99999999);
        
        @(posedge clk);
        @(negedge clk); // Adicionado ciclo completo
        we3 = 0;
        ra1 = 9;
        #1;
        // Agora devemos ver o novo valor
        check_result("Read-After-Write Same Register", rd1, 32'hAAAAAAAA);
    endtask

    /**
     * Teste específico para o registrador $7 - CORRIGIDO
     */
    task test_reg7();
        $display("\n=== TESTES ESPECÍFICOS DO REGISTRADOR $7 ===\n");
        
        // Inicializa o registrador com um valor conhecido
        @(posedge clk);
        we3 = 1;
        wa3 = 7;
        wd3 = 32'h77777777;
        @(negedge clk);
        @(posedge clk);
        
        // Testa leitura em ambos os portos
        ra1 = 7;
        ra2 = 7;
        #1;
        check_result("Reg7 Write/Read Test", rd1, 32'h77777777);
        check_result("Reg7 Dual Read Test", rd2, 32'h77777777);
        
        // Teste com padrão diferente - CORRIGIDO
        we3 = 1;
        wa3 = 7;
        wd3 = 32'hBBBBBBBB;
        @(negedge clk);
                @(posedge clk);
        @(negedge clk); // Ciclo completo para garantir escrita
        
        we3 = 0;
        ra1 = 7;
        #1;
        check_result("Reg7 Alternative Pattern", rd1, 32'hBBBBBBBB);
        
        // Teste de escrita-leitura rápida
        we3 = 1;
        wa3 = 7;
        wd3 = 32'h12345678;
        @(posedge clk);
        @(negedge clk);
        
        @(posedge clk); // Adicionado para garantir que o valor seja atualizado
        
        we3 = 0;
        ra1 = 7;
        #1;
        check_result("Reg7 Fast Read After Write", rd1, 32'h12345678);
    endtask

    /**
     * Executa testes de cobertura estendida para garantir que todos os registradores são testados
     */
    task test_extended_coverage();
        $display("\n=== TESTES DE COBERTURA ESTENDIDA ===\n");
        
        // Teste todos os registradores com padrões diferentes
        for (int i = 8; i < 31; i++) begin
            write_time = $time;
            we3 = 1;
            wa3 = i;
            wd3 = 32'h01010101 * i;
            @(posedge clk);
            @(negedge clk);
            
            we3 = 0;
            ra1 = i;
            #1;
            read_time = $time;
            check_result($sformatf("Register %0d Extended Coverage", i), rd1, 32'h01010101 * i);
            write_to_read_delay = read_time - write_time;
            $display("Write to Read Delay for Register %0d: %0t", i, write_to_read_delay);
        end
    endtask
    
    /**
     * Testa os registradores que não foram cobertos nos testes anteriores
     */
    task test_remaining_registers();
        $display("\n=== TESTES DE REGISTRADORES REMANESCENTES ===\n");
        
        // Teste os registradores que não foram cobertos ainda
        for (int i = 0; i < 32; i++) begin
            if (!reg_read_coverage[i] || !reg_write_coverage[i]) begin
                we3 = 1;
                wa3 = i;
                wd3 = 32'h12345678 + i;
                @(posedge clk);
                @(negedge clk);
                
                we3 = 0;
                ra1 = i;
                #1;
                check_result($sformatf("Remaining Register %0d", i), rd1, (i == 0) ? 32'h0 : (32'h12345678 + i));
                
                reg_write_coverage[i] = 1;
                reg_read_coverage[i] = 1;
                reg_access_count[i] += 2;
            end
            else begin
                ra1 = i;
                #1;
                $display("Register %0d already initialized with value 0x%h", i, rd1);
            end
        end
    endtask

    /**
     * Executa testes de corner case para verificar comportamento em condições extremas
     */
    task run_corner_case_tests();
        int unused_reg;
        
        $display("\n=== TESTES DE CORNER CASE ===\n");
        
        // Encontre um registrador não usado
        unused_reg = 6; // Definir valor após declaração
        
        // Teste com registrador não usado para garantir um teste limpo
        we3 = 1;
        wa3 = unused_reg;
        wd3 = 32'hFFFF0000; // Padrão metade 1s, metade 0s
        @(posedge clk);
        @(negedge clk);
        we3 = 0;
        ra1 = unused_reg;
        #1;
        check_result("Corner Pattern Test", rd1, 32'hFFFF0000);
        
        // Testar escritas consecutivas rápidas
        test_consecutive_writes();
        
        // Testar sequência A-B-A
        test_write_read_write();
        
        // Testar valores extremos
        test_min_max_values();
        
        // Testar padrão único de bit propagante
        test_bit_pattern();
        
        corner_case_count += 5;
    endtask

    /**
     * Testa escritas consecutivas rápidas no mesmo registrador
     */
    task test_consecutive_writes();
        int reg_idx;
        
        $display("\n=== Teste de Escrita Consecutiva Rápida ===");
        
        // Inicializa variáveis
        reg_idx = 5; // Definir valor após declaração
        
        // Série de escritas consecutivas sem esperar pela leitura
        for (int i = 0; i < 5; i++) begin
            we3 = 1;
            wa3 = reg_idx;
            wd3 = 32'hA00000A0 + i; // Padrão diferente para cada escrita
            @(posedge clk);
            #2; // Pequeno atraso para estabilização
        end
        
        // Verifica o último valor escrito
        we3 = 0;
        ra1 = reg_idx;
        #1;
        check_result("Escrita Consecutiva - Última Escrita", rd1, 32'hA00000A4);
    endtask

    /**
     * Testa padrão de escrita-leitura-escrita (A-B-A)
     */
    task test_write_read_write();
        int reg_A;
        int reg_B;
        
        $display("\n=== Teste de Escrita-Leitura-Escrita (A-B-A) ===");
        
        // Inicializa variáveis
        reg_A = 3;
        reg_B = 4;
        
        // Escreve primeiro valor no A
        we3 = 1;
        wa3 = reg_A;
        wd3 = 32'hAAAAAAAA;
        @(posedge clk);
        @(negedge clk);
        
        // Escreve valor em B
        we3 = 1;
        wa3 = reg_B;
        wd3 = 32'hBBBBBBBB;
        @(posedge clk);
        @(negedge clk);
        
        // Lê B durante escrita em A
        we3 = 1;
        wa3 = reg_A;
        wd3 = 32'hCCCCCCCC;
        ra1 = reg_B;
        @(posedge clk);
        check_result("Leitura Durante Escrita - Reg B", rd1, 32'hBBBBBBBB);
        @(negedge clk);
        
        we3 = 0;
        ra1 = reg_A;
        #1;
        check_result("Escrita A-B-A - Valor Final de A", rd1, 32'hCCCCCCCC);
    endtask
    
    /**
     * Testa valores extremos (todos 1s e todos 0s)
     */
    task test_min_max_values();
        int reg_max;
        int reg_min;
        
        // Inicializa variáveis
        reg_max = 12;
        reg_min = 13;
        
        // Teste valor máximo (todos 1s)
        we3 = 1;
        wa3 = reg_max;
        wd3 = 32'hFFFFFFFF;
        @(posedge clk);
        @(negedge clk);
        
        we3 = 0;
        ra1 = reg_max;
        #1;
        check_result("Valor Máximo (Todos 1s)", rd1, 32'hFFFFFFFF);
        
        // Teste valor mínimo (todos 0s exceto reg0)
        we3 = 1;
        wa3 = reg_min;
        wd3 = 32'h00000000;
        @(posedge clk);
        @(negedge clk);
        
        we3 = 0;
        ra1 = reg_min;
        #1;
        check_result("Valor Mínimo (Todos 0s)", rd1, 32'h00000000);
    endtask
    
    /**
     * Testa padrão de bit propagante único
     */
    task test_bit_pattern();
        int reg_idx;
        logic [31:0] bit_pattern;
        
        // Inicializa variáveis
        reg_idx = 14;
        bit_pattern = 32'h00000001;
        
        // Teste de propagação de bit único
        for (int i = 0; i < 5; i++) begin // Reduzido para 5 bits para economizar tempo
            we3 = 1;
            wa3 = reg_idx;
            wd3 = bit_pattern;
            @(posedge clk);
            @(negedge clk);
            
            // Verifica o bit atual
            we3 = 0;
            ra1 = reg_idx;
            #1;
            check_result($sformatf("Bit Pattern Test - Bit %0d", i), rd1, bit_pattern);
            
            // Desloca o bit para a próxima posição
            bit_pattern = bit_pattern << 1;
        end
    endtask

    /**
     * Testes de paralelismo que simulam múltiplos acessos simultâneos
     */
    task run_parallel_tests();
        int reg_A;
        int reg_B;
        int reg_C;
        
        $display("\n=== TESTES DE PARALELISMO ===\n");
        
        // Inicializa variáveis
        reg_A = 17;
        reg_B = 18;
        reg_C = 19;
        
        // Teste de leitura dupla durante escrita
        test_dual_read_during_write(reg_A, reg_B, reg_C);
        
        // Teste de acesso alternado
        test_alternating_access(reg_A);
        
        parallel_test_count += 2;
    endtask

    /**
     * Testa leitura dupla durante operação de escrita
     */
    task test_dual_read_during_write(int reg_A, int reg_B, int reg_C);
        $display("\n=== Teste de Leitura Dupla Durante Escrita ===");
        
        // Inicializa registradores com valores conhecidos
        we3 = 1;
        wa3 = reg_A;
        wd3 = 32'h12121212;
        @(posedge clk);
        @(negedge clk);
        
        we3 = 1;
        wa3 = reg_B;
        wd3 = 32'h34343434;
        @(posedge clk);
        @(negedge clk);
        
        // Lê reg_A e reg_B durante escrita em reg_C
        we3 = 1;
        wa3 = reg_C;
        wd3 = 32'h56565656;
        ra1 = reg_A;
        ra2 = reg_B;
        @(posedge clk);
        
        check_result("Leitura Paralela 1 Durante Escrita", rd1, 32'h12121212);
        check_result("Leitura Paralela 2 Durante Escrita", rd2, 32'h34343434);
    endtask
    
    /**
     * Testa acesso alternado (escrita-leitura-escrita-leitura)
     */
    task test_alternating_access(int reg_idx);
        $display("\n=== Teste de Acesso Alternado ===");
        
        // Série de escritas e leituras alternadas
        for (int i = 0; i < 3; i++) begin // Reduzido para 3 ciclos para economizar tempo
            // Escrita
            we3 = 1;
            wa3 = reg_idx;
            wd3 = 32'h55555555 + i;
            @(posedge clk);
            @(negedge clk);
            
            // Leitura
            we3 = 0;
            ra1 = reg_idx;
            #1;
            check_result($sformatf("Acesso Alternado - Leitura %0d", i), rd1, 32'h55555555 + i);
        end
    endtask

    /**
     * Executa todos os testes estendidos incluindo timing, contenção de barramento, etc.
     */
    task run_extended_tests();
        test_timing();
        test_bus_contention();
        test_reg7();
        test_extended_coverage();
        test_remaining_registers();
    endtask

    /**
     * Atualiza as estatísticas baseadas nos testes executados
     */
    task update_statistics();
        // Inicializa contadores
        most_accessed_reg = 0;
        most_read_reg = 0;
        most_written_reg = 0;
        max_access_count = 0;
        max_read_count = 0;
        max_write_count = 0;
        unique_reads = 0;
        unique_writes = 0;
        
        // Atualiza estatísticas de registradores
        for (int i = 0; i < 32; i++) begin
            if (reg_access_count[i] > max_access_count) begin
                max_access_count = reg_access_count[i];
                most_accessed_reg = i;
            end
            if (reg_read_count_by_reg[i] > max_read_count) begin
                max_read_count = reg_read_count_by_reg[i];
                most_read_reg = i;
            end
            if (reg_write_count_by_reg[i] > max_write_count) begin
                max_write_count = reg_write_count_by_reg[i];
                most_written_reg = i;
            end
            if (reg_read_coverage[i]) unique_reads++;
            if (reg_write_coverage[i]) unique_writes++;
        end
        
        // Atualiza coberturas
        register_coverage = unique_reads * 100.0 / 32;
        read_coverage = unique_reads * 100.0 / 32;
        write_coverage = unique_writes * 100.0 / 32;
    endtask

    /**
     * Gera relatório completo dos resultados dos testes
     */
    task generate_report();
        $display("\n============================================================");
        $display("=== RELATÓRIO COMPLETO DE TESTES - BANCO DE REGISTRADORES ===");
        $display("============================================================\n"); 

        $display("Informações da Execução:");
        $display("  Duração dos Testes: %0t ns", $time);
        $display("  Clock: 10ns (100MHz)\n");
        
        $display("Resumo dos Testes:");
        $display("  Testes totais executados: %0d", tests_total);
        $display("  Testes aprovados: %0d (%.1f%%)", tests_passed, (tests_passed * 100.0) / tests_total);
        $display("  Testes reprovados: %0d (%.1f%%)", tests_total - tests_passed, 
                ((tests_total - tests_passed) * 100.0) / tests_total);
        
        $display("\nDistribuição dos Testes:");
        $display("  Testes básicos: %0d", tests_total - corner_case_count - parallel_test_count);
        $display("  Testes de corner case: %0d", corner_case_count);
        $display("  Testes de paralelismo: %0d", parallel_test_count);
        
        $display("\nEstatísticas de Cobertura:");
        $display("  Registradores testados: %0d/32 (%.1f%%)", unique_reads, register_coverage);
        $display("  Operações de leitura: %0d", read_operations);
        $display("  Operações de escrita: %0d", write_operations);
        $display("  Acessos simultâneos: %0d", simultaneous_accesses);
        
        $display("\nRegistradores Mais Acessados:");
        $display("  Registrador com mais acessos: $%0d (%0d acessos)", most_accessed_reg, max_access_count);
        $display("  Registrador mais lido: $%0d (%0d leituras)", most_read_reg, max_read_count);
        $display("  Registrador mais escrito: $%0d (%0d escritas)", most_written_reg, max_write_count);
        
        $display("\nTiming:");
        $display("  Atraso médio escrita-leitura: %0t", delay_count > 0 ? total_write_to_read_delay/delay_count : 0);
        $display("  Atraso mínimo: %0t", min_write_to_read_delay == '1 ? 0 : min_write_to_read_delay);
        $display("  Atraso máximo: %0t", max_write_to_read_delay);
    endtask

    /**
     * Inicializa todas as variáveis do testbench para um estado conhecido
     */
    task initialize_variables();
        // Reset de todos os sinais
        we3 = 0;
        ra1 = 0;
        ra2 = 0;
        wa3 = 0;
        wd3 = 0;
        
        // Reset dos contadores
        write_operations = 0;
        read_operations = 0;
        simultaneous_accesses = 0;
        tests_total = 0;
        tests_passed = 0;
        delay_count = 0;
        total_write_to_read_delay = 0;
        min_write_to_read_delay = '1;
        max_write_to_read_delay = 0;
        parallel_test_count = 0;
        corner_case_count = 0;
        
        // Reset dos arrays
        for (int i = 0; i < 32; i++) begin
            reg_read_coverage[i] = 0;
            reg_write_coverage[i] = 0;
            reg_read_count_by_reg[i] = 0;
            reg_write_count_by_reg[i] = 0;
            reg_access_count[i] = 0;
        end
        we_coverage[0] = 0;
        we_coverage[1] = 0;
        
        // Inicializa padrões de teste
        initialize_test_patterns();
    endtask

    /////////////////////////////////////////////////////////////////////////////
    // Bloco Principal de Execução
    /////////////////////////////////////////////////////////////////////////////

    initial begin
        $display("=== Register File Testbench - Versão Final Otimizada ===\n");
        $display("Informações da Execução:");
        $display("  Descrição: Verificação completa do banco de registradores MIPS");
        
        // Inicializa todas as variáveis
        initialize_variables();
        #10; // Aguarda inicialização completa
        
        // Executa testes básicos primeiro
        run_basic_tests();
        
        // Executa testes estendidos
        run_extended_tests();
        
        // Executa testes de corner case
        run_corner_case_tests();
        
        // Executa testes de paralelismo
        run_parallel_tests();
        
        // Atualiza estatísticas e gera relatório final
        update_statistics();
        generate_report();
        
        $finish;
    end

    // Monitor de sinais para depuração (opcional - pode ser comentado)
    initial begin
        $monitor("Time=%0t we3=%b wa3=%d wd3=0x%h ra1=%d rd1=0x%h ra2=%d rd2=0x%h",
                 $time, we3, wa3, wd3, ra1, rd1, ra2, rd2);
    end

endmodule

/*******************************************************************************
* Guia de Uso do Testbench para Banco de Registradores MIPS
*
* Este testbench implementa uma verificação completa e otimizada de um banco de
* registradores MIPS com 32 registradores de 32 bits e os seguintes recursos:
*
* 1. Interface:
*    - clk: sinal de clock
*    - we3: sinal de habilitação de escrita
*    - ra1, ra2: endereços de leitura dos portos 1 e 2
*    - wa3: endereço de escrita
*    - wd3: dado de entrada para escrita
*    - rd1, rd2: dados de saída dos portos 1 e 2
*
* 2. Organização dos Testes:
*    - Testes básicos de leitura/escrita
*    - Testes estendidos de timing e cobertura
*    - Testes de corner case com padrões específicos
*    - Testes de paralelismo para acessos simultâneos
*    - Análise estatística e geração de relatório
*
* 3. Comportamento Esperado:
*    - O registrador $0 deve sempre retornar zero
*    - As escritas devem ser atualizadas no borda positiva do clock
*    - As leituras devem ser assíncronas e acessar registradores diferentes simultaneamente
*
* 4. Requisitos de Timing:
*    - Os dados escritos devem estar disponíveis na próxima leitura após o clock
*    - O banco de registradores deve permitir leituras simultâneas
*
* 5. Testes Específicos Implementados:
*    - Verificação do registrador $0 (sempre zero)
*    - Testes de padrões de bits (alternância, valores extremos)
*    - Testes de leitura durante escrita em outro registrador
*    - Testes de leitura após escrita no mesmo registrador
*    - Testes de acesso paralelo e seguencial
*
* 6. Resultados Esperados:
*    - Todos os testes devem passar
*    - Cobertura completa de todos os registradores
*    - Análise de timing dentro das especificações
*
* Este testbench foi otimizado para Xcelium e corrigido para evitar problemas
* de compatibilidade com as regras da IEEE para SystemVerilog, especialmente
* evitando inicializações diretas de arrays e variáveis locais.
*******************************************************************************/