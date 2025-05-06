// Aluna: Jaqueline Ferreira de Brito
// Testbench para o processador MIPS monociclo

/*
 * Módulo: top_tb
 * Função: Testar o funcionamento completo do processador MIPS monociclo
 *
 * Este testbench:
 * - Inicializa registradores e memória com valores específicos
 * - Executa o programa carregado em memfile.dat
 * - Monitora a execução do processador a cada ciclo
 * - Exibe informações sobre instruções, registradores e sinais de controle
 * - Termina quando encontra uma condição de sucesso ou após um número máximo de ciclos
 */

module top_tb();
    logic        clk;
    logic        reset;
    logic [31:0] writedata, dataadr;
    logic        memwrite;
    
    // Instanciação do módulo top (device under test)
    top dut(
        .clk(clk),
        .reset(reset),
        .writedata(writedata),
        .dataadr(dataadr),
        .memwrite(memwrite)
    );
    
    // Inicialização dos sinais e ambiente de teste
    initial begin
        clk = 0;
        reset = 1;
        
        // Mensagem de início
        $display("=================================================================");
        $display("Testbench do Processador MIPS Monociclo - Início");
        $display("=================================================================");
        
        // Inicializar valores nos registradores
        dut.dp.rf.rf[2] = 32'h00000005; // $2 = 5
        dut.dp.rf.rf[3] = 32'h0000000C; // $3 = 12
        
        // Inicializar valores na memória
        dut.dmem.RAM[20] = 32'h00000005; // Mem[80] = 5  (80/4 = 20)
        dut.dmem.RAM[21] = 32'h0000000C; // Mem[84] = 12 (84/4 = 21)
        
        $display("Inicialização: Registradores $2=5, $3=12");
        $display("Inicialização: Memória[80]=5, Memória[84]=12");
        
        // Verificar conteúdo de memfile.dat (primeiras instruções)
        $display("\nInstruções carregadas da memória:");
        for(int i = 0; i < 10; i++) begin
            $display("Endereço 0x%2h: 0x%8h", i*4, dut.imem.RAM[i]);
        end
        
        // Aguardar 22 unidades de tempo e desativar o reset
        #22; reset = 0;
    end
    
    // Geração de clock
    always begin
        #5 clk = ~clk;  // Clock com período = 10 unidades de tempo
    end
    
    // Contador de ciclos para monitoramento
    int ciclo = 0;
    
    // Monitoramento a cada ciclo de clock
    always @(posedge clk) begin
        if (~reset) begin
            ciclo = ciclo + 1;
            
            $display("\n--- Ciclo %0d (@%0t) ---", ciclo, $time);
            $display("PC=0x%h, Instr=0x%h", dut.pc, dut.instr);
            
            // Decodificar a instrução atual
            decode_instr(dut.instr);
            
            // Mostrar informações detalhadas dos registradores
            $display("Registradores: $2=%0d, $3=%0d, $4=%0d, $5=%0d, $7=%0d", 
                    dut.dp.rf.rf[2], dut.dp.rf.rf[3], 
                    dut.dp.rf.rf[4], dut.dp.rf.rf[5], 
                    dut.dp.rf.rf[7]);
                    
            // Mostrar estado da ULA
            $display("ULA: a=0x%h, b=0x%h, result=0x%h, zero=%b", 
                    dut.dp.srca, dut.dp.srcb, dut.dataadr, dut.zero);
            
            // Mostrar sinais de controle
            $display("Controle: RegWrite=%b, MemWrite=%b, Branch=%b", 
                    dut.regwrite, dut.memwrite, dut.c.branch);
                    
            // Mostrar informações sobre branch
            if (dut.c.branch)
                $display("** BRANCH: alvo=0x%h, tomado=%b **", 
                        dut.dp.pcbranch, dut.pcsrc);
                
            // Monitorar escrita em memória
            if (dut.memwrite) begin
                $display("** ESCRITA EM MEMÓRIA: Endereço=0x%h, Valor=0x%h **", 
                        dataadr, writedata);
                        
                // Condição de término bem-sucedida
                // Verifica se foi escrito o valor 1 no endereço 0x54
                if (dataadr === 32'h54 && writedata === 32'h1) begin
                    $display("\n=================================================================");
                    $display("SUCESSO! Teste concluído corretamente após %0d ciclos.", ciclo);
                    $display("Escrita do valor 1 no endereço 0x54 (84) confirmada!");
                    $display("=================================================================\n");
                    
                    dump_state();
                    $finish;
                end
            end
            
            // Timeout após muitos ciclos para evitar simulação infinita
            if (ciclo >= 50) begin
                $display("\n=================================================================");
                $display("TIMEOUT! Simulação interrompida após %0d ciclos.", ciclo);
                $display("=================================================================\n");
                
                dump_state();
                $finish;
            end
        end
    end
    
    // Task para decodificar e exibir a instrução atual em formato legível
    task decode_instr(input [31:0] instr);
        if (instr === 32'hxxxxxxxx)
            $display("Instrução: INVÁLIDA");
        else if (instr[31:26] == 6'b000000) begin // Instruções tipo-R
            case (instr[5:0])
                6'b100000: $display("Instrução: add $%0d, $%0d, $%0d", 
                                 instr[15:11], instr[25:21], instr[20:16]);
                6'b100010: $display("Instrução: sub $%0d, $%0d, $%0d", 
                                 instr[15:11], instr[25:21], instr[20:16]);
                6'b100100: $display("Instrução: and $%0d, $%0d, $%0d", 
                                 instr[15:11], instr[25:21], instr[20:16]);
                6'b100101: $display("Instrução: or $%0d, $%0d, $%0d", 
                                 instr[15:11], instr[25:21], instr[20:16]);
                6'b101010: $display("Instrução: slt $%0d, $%0d, $%0d", 
                                 instr[15:11], instr[25:21], instr[20:16]);
                default: $display("Instrução R-type desconhecida: funct=0x%h", instr[5:0]);
            endcase
        end
        else if (instr[31:26] == 6'b001000) // Instruções tipo-I
            $display("Instrução: addi $%0d, $%0d, %0d", 
                  instr[20:16], instr[25:21], $signed(instr[15:0]));
        else if (instr[31:26] == 6'b100011)
            $display("Instrução: lw $%0d, %0d($%0d)", 
                  instr[20:16], $signed(instr[15:0]), instr[25:21]);
        else if (instr[31:26] == 6'b101011)
            $display("Instrução: sw $%0d, %0d($%0d)", 
                  instr[20:16], $signed(instr[15:0]), instr[25:21]);
        else if (instr[31:26] == 6'b000100)
            $display("Instrução: beq $%0d, $%0d, %0d", 
                  instr[25:21], instr[20:16], $signed(instr[15:0]));
        else if (instr[31:26] == 6'b000010) // Instruções tipo-J
            $display("Instrução: j %0d", instr[25:0]);
        else
            $display("Instrução desconhecida: 0x%h", instr);
    endtask
    
    // Task para exibir o estado final do processador
    task dump_state;
        $display("\nEstado final dos registradores:");
        for (int i = 0; i < 10; i = i + 1)
            $display("$%0d = %0d (0x%h)", i, $signed(dut.dp.rf.rf[i]), dut.dp.rf.rf[i]);
        
        $display("\nEstado final da memória:");
        $display("Mem[0x50] = %0d (0x%h)", dut.dmem.RAM[20], dut.dmem.RAM[20]);
        $display("Mem[0x54] = %0d (0x%h)", dut.dmem.RAM[21], dut.dmem.RAM[21]);
        
        // Exibir o estado final das instruções
        $display("\nEstado final das instruções:");
        for (int i = 0; i < 10; i = i + 1)
            $display("Instr[0x%2h] = 0x%8h", i*4, dut.imem.RAM[i]);
    endtask
    
endmodule