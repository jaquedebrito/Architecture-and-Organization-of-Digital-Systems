// Aluna: Jaqueline Ferreira de Brito
// Testbench para a memória de instruções do processador MIPS

/*
 * Módulo: instruction_memory_tb
 * Função: Testar o funcionamento da memória de instruções do processador MIPS
 *
 * Este testbench:
 * - Carrega instruções do arquivo memfile.dat
 * - Verifica se as instruções são corretamente lidas da memória
 * - Verifica a integridade de cada instrução armazenada
 */

module instruction_memory_tb;
    logic [5:0]  addr;
    logic [31:0] instr;
    
    // Contadores para estatísticas
    int tests_passed = 0;
    int tests_failed = 0;
    int fd;
    string line;
    logic [31:0] expected_instructions[$];  // Queue para armazenar instruções esperadas
    
    // Instância do módulo sob teste
    instruction_memory dut (
        .addr(addr),
        .instr(instr)
    );
    
    // Task para verificação de resultados
    task check_result(string test_name, logic [31:0] actual, logic [31:0] expected);
        if (actual === expected) begin
            $display("PASS: %s - Got: 0x%h", test_name, actual);
            tests_passed++;
        end else begin
            $display("FAIL: %s - Got: 0x%h, Expected: 0x%h", test_name, actual, expected);
            tests_failed++;
        end
    endtask
    
    // Procedimento de teste principal
    initial begin
        // Cabeçalho
        $display("\n=== Memória de Instruções - Testbench ===");
        $display("----------------------------------------\n");
        
        // Ler instruções do arquivo memfile.dat
        fd = $fopen("memfile.dat", "r");
        if (fd == 0) begin
            $display("Erro: Não foi possível abrir memfile.dat");
            $finish;
        end
        
        // Carregar instruções na queue para comparação posterior
        while (!$feof(fd)) begin
            logic [31:0] temp_instr;
            if ($fscanf(fd, "%h", temp_instr) == 1)
                expected_instructions.push_back(temp_instr);
        end
        
        $fclose(fd);
        
        // Testar cada instrução lida da memória de instruções
        for (int i = 0; i < expected_instructions.size(); i++) begin
            addr = i[5:0];  // Endereço dividido por 4 (word-aligned)
            #5;  // Tempo para estabilização
            check_result($sformatf("Instrução %0d", i), instr, expected_instructions[i]);
        end
        
        // Relatório final
        $display("\n----------------------------------------");
        $display("Testes concluídos:");
        $display("Passou: %0d", tests_passed);
        $display("Falhou: %0d", tests_failed);
        if (tests_failed == 0)
            $display("TODOS OS TESTES PASSARAM!");
        else
            $display("ALGUM TESTE FALHOU!");
        $display("----------------------------------------\n");
        
        $finish;
    end
    
    // Monitor para depuração
    always @(addr) begin
        $display("T=%0t: PC/4=%0d, Instrução=0x%h", $time, addr, instr);
    end
endmodule

/* Explicação do Testbench

Este testbench verifica detalhadamente a funcionalidade da Memória de Instruções com os seguintes testes:

    Configuração:
        Define sinais para endereço e instrução
        Implementa uma tarefa para verificar os resultados
        Lê instruções do arquivo padrão memfile.dat

    Preparação de Dados:
        Carrega instruções do arquivo memfile.dat
        Armazena as instruções esperadas em uma queue para comparação

    Testes essenciais:
        Instruções básicas: Verifica se cada instrução no arquivo é lida corretamente
        Endereços válidos: Verifica instruções em diferentes posições na memória
        
    Simulação de execução:
        Simula a busca sequencial de instruções como ocorreria durante a execução do processador

    Verificação:
        Para cada caso, verifica se a instrução lida corresponde exatamente ao valor esperado

Este testbench é essencial para garantir que o processador MIPS possa ler corretamente as instruções
armazenadas em memória, um componente crítico para a execução do programa.
*/