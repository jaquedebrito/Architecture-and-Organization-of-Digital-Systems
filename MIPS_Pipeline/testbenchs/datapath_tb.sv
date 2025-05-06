// Aluna: Jaqueline Ferreira de Brito
// Testbench para o caminho de dados (datapath) do processador MIPS

/*
 * Módulo: datapath_tb
 * Função: Testar o caminho de dados do processador MIPS isoladamente
 *
 * Este testbench verifica o funcionamento do datapath para diferentes instruções,
 * simulando os sinais de controle que seriam gerados pelo controlador e
 * verificando os resultados esperados para cada operação.
 */

module datapath_tb;
    // Sinais de teste - interface do datapath
    logic        clk, reset;
    logic        memtoreg, pcsrc;
    logic        ULAsrc, regdst;
    logic        regwrite, memread;
    logic [2:0]  ULAcontrol;
    logic        zero;
    logic [31:0] pc;
    logic [31:0] instr;
    logic [31:0] ULAout;
    logic [31:0] writedata;
    logic [31:0] readdata;
    
    // Contadores de teste
    int tests_passed = 0;
    int tests_failed = 0;
    
    // Memórias simuladas
    logic [31:0] instr_memory[63:0];
    logic [31:0] data_memory[63:0];
    
    // Instância do módulo sob teste
    datapath dut (.*);
    
    // Geração de clock - período de 10ns
    always begin
        clk = 0; #5;
        clk = 1; #5;
    end
    
    // Simula a execução de uma instrução lw
    task execute_lw;
        @(posedge clk);
        #1; // Espera estabilização do endereço
        readdata = data_memory[ULAout >> 2];
        $display("DEBUG LW: Endereço=%h, Dado=%h, Reg destino=%d", 
                 ULAout >> 2, readdata, instr[20:16]);
        @(negedge clk);
    endtask
    
    // Simula acesso à memória para instruções lw/sw
    task execute_memory_instruction;
        @(posedge clk);
        #1; // Espera estabilização do endereço
        
        if (instr[31:26] == 6'b101011) begin // SW
            data_memory[ULAout >> 2] = writedata;
            $display("DEBUG SW: Endereço=%h, Dado=%h", ULAout >> 2, writedata);
        end
        else if (instr[31:26] == 6'b100011) begin // LW
            readdata = data_memory[ULAout >> 2];
            $display("DEBUG LW: Endereço=%h, Dado=%h", ULAout >> 2, readdata);
        end
        else begin
            $display("DEBUG: Não é uma instrução de acesso à memória");
        end
        
        @(negedge clk);
    endtask

    // Task para verificar resultados
    task check_result(
        input string test_name,
        input logic [31:0] actual,
        input logic [31:0] expected
    );
        $write("Teste %s: ", test_name);
        if (actual === expected) begin
            $display("PASSOU! (0x%h)", actual);
            tests_passed++;
        end else begin
            $display("FALHOU! Obtido=0x%h, Esperado=0x%h", actual, expected);
            tests_failed++;
        end
    endtask

    // Inicializa as memórias de instrução e dados
    task initialize_memories;
        // Memória de instruções (programa de teste)
        instr_memory[0] = 32'h20020005;  // addi $2, $0, 5
        instr_memory[1] = 32'h2003000C;  // addi $3, $0, 12
        instr_memory[2] = 32'h00432020;  // add $4, $2, $3
        instr_memory[3] = 32'h00822822;  // sub $5, $4, $2
        instr_memory[4] = 32'h00823024;  // and $6, $4, $2
        instr_memory[5] = 32'h00823825;  // or $7, $4, $2
        instr_memory[6] = 32'h0043402A;  // slt $8, $2, $3
        instr_memory[7] = 32'hAC040004;  // sw $4, 4($0)
        instr_memory[8] = 32'h8C0A0004;  // lw $10, 4($0)
        
        // Limpa memória de dados
        for (int i = 0; i < 64; i++) begin
            data_memory[i] = 32'h0;
        end
        
        $display("Memórias inicializadas com sucesso");
    endtask

    // Executa um ciclo de clock
    task execute_cycle;
        @(posedge clk);
        #1; // Espera estabilização
        $display("Ciclo de clock executado (PC=%h)", pc);
    endtask

    // Procedimento de teste
    initial begin
        $display("=== Início dos Testes do Datapath ===");
        
        // Reset inicial
        reset = 1;
        regwrite = 0;
        memread = 0;
        execute_cycle();
        reset = 0;
        
        // Inicialização
        initialize_memories();
        
        // Teste 1: ADDI $2, $0, 5
        $display("\n>> Teste ADDI $2, $0, 5");
        instr = instr_memory[0];
        regdst = 0;         // Seleciona rt como registrador destino
        ULAsrc = 1;         // Seleciona imediato como segundo operando
        memtoreg = 0;       // Seleciona resultado da ULA para escrita no registrador
        regwrite = 1;       // Habilita escrita no banco de registradores
        ULAcontrol = 3'b010; // Operação de adição
        execute_cycle();
        check_result("ADDI $2", dut.rf.rf[2], 32'h5);
        
        // Teste 2: ADDI $3, $0, 12
        $display("\n>> Teste ADDI $3, $0, 12");
        instr = instr_memory[1];
        execute_cycle();
        check_result("ADDI $3", dut.rf.rf[3], 32'hC);
        
        // Teste 3: ADD $4, $2, $3
        $display("\n>> Teste ADD $4, $2, $3");
        instr = instr_memory[2];
        regdst = 1;         // Seleciona rd como registrador destino
        ULAsrc = 0;         // Seleciona registrador como segundo operando
        execute_cycle();
        check_result("ADD $4", dut.rf.rf[4], 32'h11);
        
        // Teste 4: SUB $5, $4, $2
        $display("\n>> Teste SUB $5, $4, $2");
        instr = instr_memory[3];
        ULAcontrol = 3'b110; // Operação de subtração
        execute_cycle();
        check_result("SUB $5", dut.rf.rf[5], 32'hC);
        
        // Teste 5: AND $6, $4, $2
        $display("\n>> Teste AND $6, $4, $2");
        instr = instr_memory[4];
        ULAcontrol = 3'b000; // Operação AND
        execute_cycle();
        check_result("AND $6", dut.rf.rf[6], 32'h1);
        
        // Teste 6: OR $7, $4, $2
        $display("\n>> Teste OR $7, $4, $2");
        instr = instr_memory[5];
        ULAcontrol = 3'b001; // Operação OR
        execute_cycle();
        check_result("OR $7", dut.rf.rf[7], 32'h15);
        
        // Teste 7: SLT $8, $2, $3
        $display("\n>> Teste SLT $8, $2, $3");
        instr = instr_memory[6];
        ULAcontrol = 3'b111; // Operação SLT (Set Less Than)
        execute_cycle();
        check_result("SLT $8", dut.rf.rf[8], 32'h1);
        
        // Teste 8: SW $4, 4($0)
        $display("\n>> Teste SW $4, 4($0)");
        instr = instr_memory[7];
        regwrite = 0;       // Desabilita escrita no banco de registradores
        ULAsrc = 1;         // Seleciona imediato como segundo operando
        memtoreg = 0;       // Não importa para SW
        ULAcontrol = 3'b010; // Operação de adição (para cálculo do endereço)
        
        // Prepara o dado a ser escrito
        writedata = dut.rf.rf[4]; // Valor de $4
        execute_memory_instruction();
        check_result("SW $4", data_memory[1], 32'h11);
        
        // Teste 9: LW $10, 4($0)
        $display("\n>> Teste LW $10, 4($0)");
        instr = instr_memory[8];
        regwrite = 1;       // Habilita escrita no banco de registradores
        ULAsrc = 1;         // Seleciona imediato como segundo operando
        memtoreg = 1;       // Seleciona dado da memória para escrita no registrador
        memread = 1;        // Habilita leitura da memória
        regdst = 0;         // Seleciona rt como registrador destino
        
        // Executa LW
        execute_lw();
        
        // Espera um ciclo para a escrita no registrador
        @(posedge clk);
        #1;
        
        // Verifica o resultado
        check_result("LW $10", dut.rf.rf[10], 32'h11);
        
        // Relatório final
        $display("\n=== Resultado dos Testes ===");
        $display("Total de testes: %0d", tests_passed + tests_failed);
        $display("Passou: %0d", tests_passed);
        $display("Falhou: %0d", tests_failed);
        if (tests_failed == 0)
            $display("TODOS OS TESTES PASSARAM!");
        else
            $display("ALGUNS TESTES FALHARAM!");
        
        $finish;
    end
    
    // Monitor de sinais importantes
    always @(posedge clk) begin
        $display("\nT=%0t:", $time);
        $display("  PC=%h", pc);
        $display("  Instr=%h", instr);
        $display("  RegWrite=%b", regwrite);
        $display("  ULAcontrol=%b", ULAcontrol);
        $display("  ULAout=%h", ULAout);
        $display("  WriteData=%h", writedata);
        $display("  ReadData=%h", readdata);
        $display("  Zero=%b", zero);
        if (regwrite) begin
            logic [4:0] write_reg;
            write_reg = regdst ? instr[15:11] : instr[20:16];
            $display("  WriteReg Data: reg=%d, data=%h", 
                    write_reg,
                    memtoreg ? readdata : ULAout);
        end
        if (instr[31:26] == 6'b101011) // SW
            $display("  SW: mem[%h] <- %h", ULAout >> 2, writedata);
        if (instr[31:26] == 6'b100011) // LW
            $display("  LW: reg[%d] <- mem[%h] = %h",
                    instr[20:16], ULAout >> 2, readdata);
    end
    
endmodule