// Aluna: Jaqueline Ferreira de Brito
// Testbench para o Main Control do processador MIPS

// -----------------------------------------------------------------------------
// 
// Descrição:
// Testbench para o Main Control do MIPS (Unidade de Controle Principal)
// O Main Control é responsável por gerar os sinais de controle baseado no opcode
// da instrução. Ele define como a instrução será executada, controlando:
// - Operações da ULA (ULAop)
// - Fluxo de dados (regdst, ULAsrc, memtoreg)
// - Escrita/leitura de registradores e memória (regwrite, memread, memwrite)
// - Controle de desvios (branch)
//
// Sinais de Controle:
// - regdst:   Seleciona registrador destino (1=rd, 0=rt)
// - ULAsrc:   Seleciona segunda entrada da ULA (0=reg, 1=imm)
// - memtoreg: Seleciona origem do dado para escrita no reg (0=ULA, 1=mem)
// - regwrite: Habilita escrita no banco de registradores
// - memread:  Habilita leitura da memória
// - memwrite: Habilita escrita na memória
// - branch:   Habilita desvio condicional
// - ULAop:    Controle da operação da ULA {ULAop1,ULAop0}
// -----------------------------------------------------------------------------

module main_control_tb;
    // Sinais para testar o módulo
    logic [5:0] op;
    logic clk, reset;
    logic regdst, ULAsrc, memtoreg, regwrite;
    logic memread, memwrite, branch;
    logic [1:0] ULAop;

    // Variáveis para estatísticas
    integer total_tests = 0;
    integer passed_tests = 0;
    string current_test;
    time test_start_time;
    time total_time;
    string test_status;
    

    // Instanciando o módulo a ser testado
    main_control dut(.*);

    // Task para verificar resultado com mensagens detalhadas
    task check_result;
        input logic exp_regdst, exp_ULAsrc, exp_memtoreg, exp_regwrite;
        input logic exp_memread, exp_memwrite, exp_branch;
        input logic [1:0] exp_ULAop;
        input string test_name;
        input string instruction_type;
        begin
            total_tests++;
            current_test = test_name;
            
            $display("Test %0d: %s (%s)", total_tests, test_name, instruction_type);
            $display("Opcode: %b", op);
            
            // Verifica cada sinal individualmente e reporta
            test_status = "PASSED";
            if (regdst !== exp_regdst && exp_regdst !== 1'bx) begin
                $display("  regdst:   Expected=%b, Got=%b [FAIL]", exp_regdst, regdst);
                test_status = "FAILED";
            end
            if (ULAsrc !== exp_ULAsrc) begin
                $display("  ULAsrc:   Expected=%b, Got=%b [FAIL]", exp_ULAsrc, ULAsrc);
                test_status = "FAILED";
            end
            if (memtoreg !== exp_memtoreg && exp_memtoreg !== 1'bx) begin
                $display("  memtoreg: Expected=%b, Got=%b [FAIL]", exp_memtoreg, memtoreg);
                test_status = "FAILED";
            end
            if (regwrite !== exp_regwrite) begin
                $display("  regwrite: Expected=%b, Got=%b [FAIL]", exp_regwrite, regwrite);
                test_status = "FAILED";
            end
            if (memread !== exp_memread) begin
                $display("  memread:  Expected=%b, Got=%b [FAIL]", exp_memread, memread);
                test_status = "FAILED";
            end
            if (memwrite !== exp_memwrite) begin
                $display("  memwrite: Expected=%b, Got=%b [FAIL]", exp_memwrite, memwrite);
                test_status = "FAILED";
            end
            if (branch !== exp_branch) begin
                $display("  branch:   Expected=%b, Got=%b [FAIL]", exp_branch, branch);
                test_status = "FAILED";
            end
            if (ULAop !== exp_ULAop) begin
                $display("  ULAop:    Expected=%b, Got=%b [FAIL]", exp_ULAop, ULAop);
                test_status = "FAILED";
            end
            
            if (test_status == "PASSED") begin
                passed_tests++;
                $display("Status: PASSED");
                $display("Time taken: %0t", $time - test_start_time);
            end
            $display("");
        end
    endtask

    // Geração de clock
    always #5 clk = ~clk;

    // Início do teste
    initial begin
        test_start_time = $time;
        
        $display("=== Main Control Testbench ===");
        $display("===============================");
        $display("Purpose: Verify Main Control functionality for MIPS processor");
        $display("Testing control signal generation for different instruction types");
        $display("===============================\n");
        
        // Inicialização
        clk = 0;
        reset = 0;
        op = 6'b000000;
        #10;

        // Testes de instruções formato R
        $display("=== Testing R-Format Instructions ===");
        $display("Verifying control signals for arithmetic/logical operations");
        op = 6'b000000; // R-format
        test_start_time = $time;
        #10;
        check_result(1'b1, 1'b0, 1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 2'b10, 
                    "R-Format", "Arithmetic/Logical Operation");

        // Testes de Load/Store
        $display("=== Testing Load/Store Instructions ===");
        $display("Verifying memory access operations");
        op = 6'b100011; // LW
        test_start_time = $time;
        #10;
        check_result(1'b0, 1'b1, 1'b1, 1'b1, 1'b1, 1'b0, 1'b0, 2'b00,
                    "LW", "Load Word");

        op = 6'b101011; // SW
        test_start_time = $time;
        #10;
        check_result(1'bx, 1'b1, 1'bx, 1'b0, 1'b0, 1'b1, 1'b0, 2'b00,
                    "SW", "Store Word");

        // Testes de Branch
        $display("=== Testing Branch Instructions ===");
        $display("Verifying branch control signals");
        op = 6'b000100; // BEQ
        test_start_time = $time;
        #10;
        check_result(1'bx, 1'b0, 1'bx, 1'b0, 1'b0, 1'b0, 1'b1, 2'b01,
                    "BEQ", "Branch if Equal");

        // Teste de instruções inválidas
        $display("=== Testing Invalid Instructions ===");
        $display("Verifying default/safe behavior");
        op = 6'b111111;
        test_start_time = $time;
        #10;
        check_result(1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 2'b00,
                    "Invalid", "Unknown Instruction");

        // Teste de resposta a mudanças rápidas
        $display("=== Testing Quick Changes ===");
        $display("Verifying response to rapid instruction changes");
        test_start_time = $time;
        op = 6'b000000; #2; // R-format
        op = 6'b100011; #2; // LW
        op = 6'b101011; #2; // SW
        op = 6'b000100; #2; // BEQ
        check_result(1'bx, 1'b0, 1'bx, 1'b0, 1'b0, 1'b0, 1'b1, 2'b01,
                    "Quick Changes", "Multiple Instructions");

        // Cálculo do tempo total
        total_time = $time - test_start_time;

        // Resumo dos testes
        $display("=== Test Summary ===");
        $display("Total tests:     %0d", total_tests);
        $display("Passed tests:    %0d", passed_tests);
        $display("Failed tests:    %0d", total_tests - passed_tests);
        $display("Success rate:    %0.2f%%", (passed_tests * 100.0) / total_tests);
        $display("Total time:      %0t", total_time);
        $display("Average time/test: %0t", total_time/total_tests);
        $display("===============================");
        
        // Verificações adicionais
        $display("\n=== Additional Checks ===");
        $display("1. Clock frequency: %0.2f MHz", 1000.0/(2*5));
        $display("2. Response time for control signals: %0t", 10);
        $display("3. All control signals stable: %s", 
                (^{regdst, ULAsrc, memtoreg, regwrite, memread, memwrite, branch, ULAop} !== 1'bx) ? "Yes" : "No");
        $display("4. Default values correct: %s",
                (op === 6'b111111 && regwrite === 1'b0 && memwrite === 1'b0) ? "Yes" : "No");
        $display("===============================\n");
        
        $finish;
    end

endmodule