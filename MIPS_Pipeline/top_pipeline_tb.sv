// Aluna: Jaqueline Ferreira de Brito
// Testbench para o processador MIPS pipeline

module top_pipeline_tb();
    // Constantes
    localparam string TIMESTAMP = "2025-03-20";
    localparam string USER = "jaquedebrito";
    localparam int MAX_CYCLES = 200;

    function string get_state_name(input logic [1:0] state);
        case(state)
            2'b00: return "NORMAL";
            2'b01: return "STALL";
            2'b10: return "ERROR";
            2'b11: return "INVALID";
            default: return "UNKNOWN";
        endcase
    endfunction

    // Timestamp global
    logic [63:0] current_time;
    
    // Sinais básicos
    logic        clk;
    logic        reset;
    logic [31:0] writedata, dataadr;
    logic        memwrite;
    
    // Status dos módulos
    logic [1:0]  ula_status;
    logic [1:0]  mem_status;
    logic [1:0]  reg_status;
    logic [63:0] last_access_times[5]; // [IF, ID, EX, MEM, WB]

    string stage_names[5] = '{"IF", "ID", "EX", "MEM", "WB"};
    
    // Sinais para monitoramento de branch prediction
    logic        is_branch;
    logic        branch_prediction;
    logic        branch_taken;
    logic [31:0] branch_target;
    logic [31:0] correct_predictions;
    logic [31:0] total_predictions;
    
    // Contadores de estatísticas
    int          stall_count;
    int          flush_count;
    int          branch_count;
    int          branch_taken_count;
    int          overflow_count;
    int          memory_error_count;
    int          register_error_count;
    
    // Estrutura para estatísticas de performance
    typedef struct {
        int     total_cycles;
        int     instruction_count;
        real    cpi;
        real    branch_accuracy;
        real    stall_rate;
        real    flush_rate;
        int     data_hazards;
        int     control_hazards;
    } performance_stats_t;
    
    performance_stats_t perf_stats;

    // Grupos de cobertura
    covergroup state_coverage @(posedge clk);
        option.per_instance = 1;
        option.comment = "Cobertura de estados do pipeline";
        
        // Cobertura dos estados da ULA
        ula_states: coverpoint ula_status {
            bins normal = {2'b00};
            bins overflow = {2'b01};
            bins error = {2'b10};
            bins invalid = {2'b11};
            option.comment = "Estados da ULA";
        }
        
        // Cobertura dos estados da memória
        mem_states: coverpoint mem_status {
            bins idle = {2'b00};
            bins busy = {2'b01};
            bins error = {2'b10};
            bins reserved = {2'b11};
            option.comment = "Estados da memória";
        }
        
        // Cobertura dos estados dos registradores
        reg_states: coverpoint reg_status {
            bins normal = {2'b00};
            bins writing = {2'b01};
            bins error = {2'b10};
            bins reading = {2'b11};
            option.comment = "Estados dos registradores";
        }
        
        // Cross coverage
        state_cross: cross ula_states, mem_states, reg_states {
            option.comment = "Combinações de estados";
        }
    endgroup

    // Cobertura de hazards
    covergroup hazard_coverage @(posedge clk);
        option.per_instance = 1;
        option.comment = "Cobertura de hazards do pipeline";
        
        // Tipos de forwarding
        forward_types: coverpoint {dut.c.forward_a, dut.c.forward_b} {
            bins no_forward = {4'b0000};
            bins forward_a_only = {4'b0100, 4'b1000};
            bins forward_b_only = {4'b0001, 4'b0010};
            bins both_forward = {4'b0101, 4'b0110, 4'b1001, 4'b1010};
            option.comment = "Tipos de forwarding";
        }
        
        // Tipos de stall/flush
        pipeline_controls: coverpoint {dut.c.stall, dut.c.flush} {
            bins normal = {2'b00};
            bins stall_only = {2'b10};
            bins flush_only = {2'b01};
            ignore_bins invalid = {2'b11};
            option.comment = "Controles do pipeline";
        }
    endgroup

    // Cobertura de branch prediction
    covergroup branch_prediction_cg @(posedge clk);
        option.per_instance = 1;
        option.comment = "Cobertura de predição de branches";
        
        prediction: coverpoint branch_prediction {
            bins taken = {1};
            bins not_taken = {0};
            option.comment = "Predições feitas";
        }
        
        actual: coverpoint branch_taken {
            bins taken = {1};
            bins not_taken = {0};
            option.comment = "Resultados reais";
        }
        
        pred_vs_actual: cross prediction, actual {
            option.comment = "Precisão das predições";
        }
    endgroup


    // Instâncias dos covergroups
    state_coverage state_cg;
    hazard_coverage hazard_cg;
    branch_prediction_cg branch_cg;

    // Instanciação do DUT
    top_pipeline dut(
        .clk(clk),
        .reset(reset),
        .writedata(writedata),
        .dataadr(dataadr),
        .memwrite(memwrite),
        .instruction_count(instruction_count),
        .cycle_count(cycle_count),
        .stall_count(stall_count),
        .branch_count(branch_count),
        .memory_access_count(memory_access_count),
        .processor_status(processor_status),
        .last_update_time(last_update_time)
    );
    
    // Mapeamento de sinais do branch predictor
    assign is_branch = dut.dp.is_branch;
    assign branch_prediction = dut.dp.prediction;
    assign branch_taken = dut.dp.branch_taken;
    assign branch_target = dut.dp.branch_target;
    
    // Mapeamento de status - ATUALIZAR ESTA SEÇÃO
    assign mem_status = dut.dmem.current_state;
    assign reg_status = dut.dp.id_stage.rf.current_state;
    assign ula_status = dut.dp.ex_stage.ula_status;

    always_comb begin
        correct_predictions = dut.branch_count - dut.branch_mispredict_count;
        total_predictions = dut.branch_count;
        ula_status = dut.dp.ex_stage.ula_status;
    end


    // Inicialização
    initial begin

        // Inicialização dos grupos de cobertura
        state_cg = new();
        hazard_cg = new();
        branch_cg = new();
        
        // Configuração do timestamp
        $timeformat(-9, 2, " ns", 20);
        
        // Iniciar simulação
        clk = 0;
        reset = 1;
        @(posedge clk);
        reset = 0;
        
        // Inicializar contadores
        stall_count = 0;
        flush_count = 0;
        branch_count = 0;
        branch_taken_count = 0;
        overflow_count = 0;
        memory_error_count = 0;
        register_error_count = 0;
        
        // Inicializar timestamps de acesso
        for (int i = 0; i < 5; i++)
            last_access_times[i] = current_time;
        
        // Mensagem de início
        $display("=================================================================");
        $display("%s - Testbench do Processador MIPS Pipeline - Início", format_timestamp(current_time));
        $display("Aluna: Jaqueline Brito");
        $display("=================================================================");
        
        // Inicializar registradores com proteção
        initialize_registers();
        
        // Inicializar memória com proteção
        initialize_memory();
        
        // Mostrar instruções carregadas
        display_loaded_instructions();
        
        // Inicializar grupos de cobertura
        initialize_coverage();
        
        // Desativar reset após 22 unidades de tempo
        #22; reset = 0;
    end

    // Geração de clock
    always begin
        #5 clk = ~clk;
    end



    // Inicialização protegida de registradores
    task initialize_registers();
        // Verificar se os registradores podem ser escritos
        if (dut.dp.id_stage.rf.access_error) begin
            $display("ERRO: Não foi possível inicializar os registradores!");
            $finish;
        end
        
        dut.dp.id_stage.rf.rf[2] = 32'h00000005; // $2 = 5
        dut.dp.id_stage.rf.rf[3] = 32'h0000000C; // $3 = 12
        
        $display("%s - Inicialização de Registradores:", format_timestamp(current_time));
        $display("  $2 = 5");
        $display("  $3 = 12");
    endtask

    // Inicialização protegida de memória
    task initialize_memory();
        // Verificar se a memória pode ser escrita
        if (dut.dmem.access_error) begin
            $display("ERRO: Não foi possível inicializar a memória!");
            $finish;
        end
        
        dut.dmem.RAM[20] = 32'h00000005; // Mem[80] = 5
        dut.dmem.RAM[21] = 32'h0000000C; // Mem[84] = 12
        
        $display("%s - Inicialização de Memória:", format_timestamp(current_time));
        $display("  Mem[80] = 5");
        $display("  Mem[84] = 12");
    endtask

    // Display de instruções carregadas
    task display_loaded_instructions();
        $display("\n%s - Instruções carregadas da memória:", format_timestamp(current_time));
        for(int i = 0; i < 10; i++) begin
            $display("  Endereço 0x%2h: 0x%8h", i*4, dut.imem.RAM[i]);
        end
    endtask

    

    // Monitoramento dos estágios do pipeline
    task monitor_pipeline_stages();
        // Monitor do estágio IF
        display_if_stage();
        
        // Monitor do estágio ID
        display_id_stage();
        
        // Monitor do estágio EX
        display_ex_stage();
        
        // Monitor do estágio MEM
        display_mem_stage();
        
        // Monitor do estágio WB
        display_wb_stage();
        
        // Monitor dos registradores
        display_registers();

        // Atualizar estatísticas
        perf_stats.total_cycles++;
        if (dut.dp.stall) stall_count++;
        if (dut.dp.flush) flush_count++;

    endtask

    // Monitor de hazards e erros
    task monitor_hazards_and_errors();
        // Monitorar stalls e flushes
        if (dut.c.stall) begin
            stall_count++;
            perf_stats.data_hazards++;
            display_error("STALL", "Detectado stall no pipeline", current_time);
        end
        
        if (dut.c.flush) begin
            flush_count++;
            perf_stats.control_hazards++;
            display_error("FLUSH", "Detectado flush no pipeline", current_time);
        end

        // Monitorar overflow da ULA
         if (dut.dp.ex_stage.alu_overflow) begin
            overflow_count++;
            display_error("ULA", "Overflow detectado", current_time);
        end

        // Monitorar erros de memória
        if (dut.dmem.access_error) begin
            memory_error_count++;
            display_error("MEMÓRIA", "Erro de acesso à memória", current_time);
        end

        // Monitorar erros de registrador
        if (dut.dp.id_stage.rf.access_error) begin
            register_error_count++;
            display_error("REGISTRADOR", "Erro de acesso ao registrador", current_time);
        end

        // Monitorar forwarding
        monitor_data_forwarding();
    endtask

    // Monitor de forwarding
    task monitor_data_forwarding();
        if (dut.c.forward_a != 2'b00) begin
            $display("%s - Forwarding A detectado:", format_timestamp(current_time));
            $display("  Tipo: %s", 
                    dut.c.forward_a == 2'b01 ? "WB->EX" : "MEM->EX");
            verify_forwarding_a();
        end

        if (dut.c.forward_b != 2'b00) begin
            $display("%s - Forwarding B detectado:", format_timestamp(current_time));
            $display("  Tipo: %s", 
                    dut.c.forward_b == 2'b01 ? "WB->EX" : "MEM->EX");
            verify_forwarding_b();
        end
    endtask

    // Verificação de forwarding
    task verify_forwarding_a();
        case (dut.c.forward_a)
            2'b01: begin
                if (dut.dp.ex_stage.ULA_srca !== dut.dp.result_wb)
                    display_error("FORWARDING", 
                                "Forwarding A (WB) incorreto", 
                                current_time);
            end
            2'b10: begin
                if (dut.dp.ex_stage.ULA_srca !== dut.dp.ULAout_mem)
                    display_error("FORWARDING", 
                                "Forwarding A (MEM) incorreto", 
                                current_time);
            end
        endcase
    endtask

    task verify_forwarding_b();
        case (dut.c.forward_b)
            2'b01: begin
                if (dut.dp.ex_stage.ULA_srcb_pre !== dut.dp.result_wb)
                    display_error("FORWARDING", 
                                "Forwarding B (WB) incorreto", 
                                current_time);
            end
            2'b10: begin
                if (dut.dp.ex_stage.ULA_srcb_pre !== dut.dp.ULAout_mem)
                    display_error("FORWARDING", 
                                "Forwarding B (MEM) incorreto", 
                                current_time);
            end
        endcase
    endtask

    // Display dos estágios do pipeline
    task display_if_stage();
        $display("\n-- Estágio IF --");
        $display("  PC=0x%h, Instr=0x%h", dut.dp.pc, dut.instr);
        display_stage_status("IF", dut.dp.if_stage_status);
        last_access_times[0] = current_time;
    endtask

    // Display do estágio ID
    task display_id_stage();
        $display("\n-- Estágio ID --");
        if (dut.dp.instr_id !== 32'b0) begin
            $display("  Instr=0x%h", dut.dp.instr_id);
            decode_instr(dut.dp.instr_id);
            $display("  RegData1=0x%h, RegData2=0x%h, SignImm=0x%h", 
                     dut.dp.reg_data1_id, dut.dp.reg_data2_id, 
                     dut.dp.signimm_id);
            $display("  Controle: RegWrite=%b, MemWrite=%b, Branch=%b", 
                     dut.dp.regwrite_id, dut.dp.memwrite_id, 
                     dut.dp.branch_id);
            display_stage_status("ID", dut.dp.id_stage_status);
        end else begin
            $display("  NOP (instrução inválida ou stall)");
        end
        last_access_times[1] = current_time;
    endtask

    // Display do estágio EX
    task display_ex_stage();
        $display("\n-- Estágio EX --");
        if (dut.dp.regwrite_ex || dut.dp.memwrite_ex) begin
            $display("  ULA: SrcA=0x%h, SrcB=0x%h, Result=0x%h, Zero=%b", 
                     dut.dp.ex_stage.ULA_srca, dut.dp.ex_stage.ULA_srcb,
                     dut.dp.ULAout_ex, dut.dp.zero_ex);
            $display("  Controle: RegWrite=%b, MemWrite=%b, ALUSrc=%b", 
                     dut.dp.regwrite_ex, dut.dp.memwrite_ex, 
                     dut.dp.ULAsrc_ex);
            $display("  Forwarding: ForwardA=%b, ForwardB=%b", 
                     dut.c.forward_a, dut.c.forward_b);
            
            // Monitoramento de overflow
            if (dut.dp.ex_stage.alu_overflow) begin
                $display("  AVISO: Overflow detectado!");
            end  // Faltava este end
            
            display_stage_status("EX", dut.dp.ex_stage_status);
        end else begin
            $display("  NOP (instrução inválida ou stall)");
        end
        
        $display("  EX: rs_ex=%d, rt_ex=%d, rd_ex=%d", 
                 dut.dp.rs_ex, dut.dp.rt_ex, dut.dp.rd_ex);
        last_access_times[2] = current_time;
    endtask

    task display_mem_stage();
        $display("\n-- Estágio MEM --");
    if (dut.dp.regwrite_mem || dut.dp.memwrite) begin
        $display("  ALUOut=0x%h, WriteData=0x%h", 
                 dut.dp.ULAout_mem, dut.dp.writedata_mem);
        $display("  Controle: RegWrite=%b, MemWrite=%b", 
                dut.dp.regwrite_mem, dut.dp.memwrite);
        
        if (dut.dp.branch_mem_reg && dut.dp.zero_mem) begin
            $display("  ** BRANCH TAKEN: target=0x%h **", 
                     dut.dp.pc_branch_mem);
        end
                
            // Monitoramento de proteção de memória
            if (dut.dmem.access_error) begin
                $display("  AVISO: Violação de proteção de memória!");
            end
                
            display_stage_status("MEM", dut.dp.mem_stage_status);
        end else begin
            $display("  NOP (instrução inválida ou stall)");
        end
        last_access_times[3] = current_time;
    endtask

    // Display do estágio WB
    task display_wb_stage();
        $display("\n-- Estágio WB --");
        if (dut.dp.regwrite_wb) begin
            $display("  WriteReg=%d, Result=0x%h", 
                     dut.dp.rd_wb, dut.dp.result_wb);
            $display("  Controle: RegWrite=%b, MemtoReg=%b", 
                     dut.dp.regwrite_wb, dut.dp.memtoreg_wb);
            display_stage_status("WB", dut.dp.wb_stage_status);
        end else begin
            $display("  NOP (sem escrita em registrador)");
        end
        last_access_times[4] = current_time;
    endtask

    // Display do estado dos registradores
    task display_registers();
        $display("\n-- Registradores --");
        for (int i = 0; i < 32; i += 4) begin
            $display("  $%2d=%0d ($%2d=%0d, $%2d=%0d, $%2d=%0d)", 
                    i, $signed(dut.dp.id_stage.rf.rf[i]),
                    i+1, $signed(dut.dp.id_stage.rf.rf[i+1]),
                    i+2, $signed(dut.dp.id_stage.rf.rf[i+2]),
                    i+3, $signed(dut.dp.id_stage.rf.rf[i+3]));
        end
    endtask

    // Monitor do branch predictor
    task monitor_branch_predictor();
        $display("\n-- Branch Predictor Status --");
        $display("  Predição: %b, Real: %b, Target: 0x%h", 
                 branch_prediction, branch_taken, branch_target);
        $display("  Acertos/Total: %0d/%0d (%.2f%%)", 
                 correct_predictions, total_predictions,
                 total_predictions > 0 ? 
                 100.0 * correct_predictions / total_predictions : 0);
        
        branch_count++;
        if (branch_taken) begin
            branch_taken_count++;
        end
        
        // Verificar predição
        if (branch_prediction == branch_taken) begin
            $display("  ACERTO na predição! PC=0x%h", dut.dp.pc);
        end else begin
            $display("  ERRO na predição! PC=0x%h, Pred=%b, Real=%b",
                    dut.dp.pc, branch_prediction, branch_taken);
        end
    endtask

    // Decodificação de instruções
    task decode_instr(input [31:0] instr);
        string instr_name;
        case (instr[31:26])
            6'b000000: begin // Tipo-R
                case (instr[5:0])
                    6'b100000: begin 
                        instr_name = "add";
                        $display("  %s $%0d, $%0d, $%0d", 
                                instr_name, instr[15:11], 
                                instr[25:21], instr[20:16]);
                    end
                    6'b100010: begin
                        instr_name = "sub";
                        $display("  %s $%0d, $%0d, $%0d", 
                                instr_name, instr[15:11], 
                                instr[25:21], instr[20:16]);
                    end
                    6'b100100: begin
                        instr_name = "and";
                        $display("  %s $%0d, $%0d, $%0d", 
                                instr_name, instr[15:11], 
                                instr[25:21], instr[20:16]);
                    end
                    6'b100101: begin
                        instr_name = "or";
                        $display("  %s $%0d, $%0d, $%0d", 
                                instr_name, instr[15:11], 
                                instr[25:21], instr[20:16]);
                    end
                    6'b101010: begin
                        instr_name = "slt";
                        $display("  %s $%0d, $%0d, $%0d", 
                                instr_name, instr[15:11], 
                                instr[25:21], instr[20:16]);
                    end
                    default: begin
                        instr_name = "unknown";
                        $display("  Instrução R-type desconhecida: %h", instr);
                    end
                endcase
            end
            6'b001000: begin
                instr_name = "addi";
                $display("  %s $%0d, $%0d, %0d", 
                        instr_name, instr[20:16], 
                        instr[25:21], $signed(instr[15:0]));
            end
            6'b100011: begin
                instr_name = "lw";
                $display("  %s $%0d, %0d($%0d)", 
                        instr_name, instr[20:16], 
                        $signed(instr[15:0]), instr[25:21]);
            end
            6'b101011: begin
                instr_name = "sw";
                $display("  %s $%0d, %0d($%0d)", 
                        instr_name, instr[20:16], 
                        $signed(instr[15:0]), instr[25:21]);
            end
            6'b000100: begin
                instr_name = "beq";
                $display("  %s $%0d, $%0d, %0d", 
                        instr_name, instr[25:21], 
                        instr[20:16], $signed(instr[15:0]));
            end
            default: begin
                instr_name = "unknown";
                $display("  Instrução desconhecida: %h", instr);
            end
        endcase
        
        // Log detalhado da instrução
        log_instruction(instr_name, instr);
    endtask

    // Log detalhado de instrução
    task log_instruction(input string instr_name, input logic [31:0] instr);
        $display("%s - Instrução Decodificada:", format_timestamp(current_time));
        $display("  User: jaquedebrito");
        $display("  Nome: %s", instr_name);
        $display("  Opcode: %b", instr[31:26]);
        $display("  RS: $%0d", instr[25:21]);
        $display("  RT: $%0d", instr[20:16]);
        $display("  RD: $%0d", instr[15:11]);
        $display("  Shamt: %0d", instr[10:6]);
        $display("  Funct: %b", instr[5:0]);
        $display("  Immediate: %0d", $signed(instr[15:0]));
    endtask

    // Verificações formais (Assertions)
    // synthesis translate_off
    
    // Verificação de predição de branch válida
    property check_branch_prediction_valid;
        @(posedge clk) disable iff (reset)
        is_branch |-> !$isunknown(branch_prediction);
    endproperty

    // Verificação de alvo de branch válido
    property check_branch_target_valid;
        @(posedge clk) disable iff (reset)
        is_branch |-> !$isunknown(branch_target);
    endproperty

    // Verificação de timing de predição
    property check_prediction_timing;
        @(posedge clk) disable iff (reset)
        is_branch |-> ##[1:3] !$isunknown(branch_taken);
    endproperty

    // Verificação de stall e flush simultâneos
    property check_no_simultaneous_stall_flush;
        @(posedge clk) disable iff (reset)
        not (dut.c.stall && dut.c.flush);
    endproperty

    // Verificação de proteção do registrador zero
    property check_zero_register_protection;
        @(posedge clk) disable iff (reset)
        dut.dp.id_stage.rf.we3 && (dut.dp.id_stage.rf.wa3 == 0) |-> 
        dut.dp.id_stage.rf.rf[0] == 0;
    endproperty

    // Verificação de latência de memória
    property check_memory_latency;
        @(posedge clk) disable iff (reset)
        dut.dmem.we |-> ##[1:5] !dut.c.stall;
    endproperty

    // Implementação das assertions
    assert property (check_branch_prediction_valid)
        else display_error("ASSERTION", "Predição inválida detectada", current_time);

    assert property (check_branch_target_valid)
        else display_error("ASSERTION", "Target de branch inválido detectado", current_time);

    assert property (check_prediction_timing)
        else display_error("ASSERTION", "Timing incorreto na predição de branch", current_time);

    assert property (check_no_simultaneous_stall_flush)
        else display_error("ASSERTION", "Stall e flush simultâneos detectados", current_time);

    assert property (check_zero_register_protection)
        else display_error("ASSERTION", "Violação de proteção do registrador zero", current_time);

    assert property (check_memory_latency)
        else display_error("ASSERTION", "Latência de memória excedida", current_time);

    // Coverage para assertions
    cover property (check_branch_prediction_valid);
    cover property (check_branch_target_valid);
    cover property (check_prediction_timing);
    cover property (check_no_simultaneous_stall_flush);
    cover property (check_zero_register_protection);
    cover property (check_memory_latency);
    
    // synthesis translate_on

    // Atualização de estatísticas de performance
    task update_performance_stats();
        // Atualizar CPI
        perf_stats.cpi = real'(perf_stats.total_cycles) / 
                        real'(perf_stats.instruction_count);
        
        // Atualizar taxa de acerto do branch predictor
        perf_stats.branch_accuracy = (total_predictions > 0) ? 
            (real'(correct_predictions) / real'(total_predictions)) * 100.0 : 0.0;
        
        // Atualizar taxas de stall e flush
        perf_stats.stall_rate = (real'(stall_count) / 
                                real'(perf_stats.total_cycles)) * 100.0;
        perf_stats.flush_rate = (real'(flush_count) / 
                                real'(perf_stats.total_cycles)) * 100.0;
    endtask

    // Display de status de estágio
    task display_stage_status(
        input string stage_name, 
        input logic [1:0] status
    );
        string status_str;
        case (status)
            2'b00: status_str = "Normal";
            2'b01: status_str = "Stall";
            2'b10: status_str = "Error";
            2'b11: status_str = "Invalid";
            default: status_str = "Unknown";
        endcase
        $display("  Status do %s: %s", stage_name, status_str);
    endtask

    // Display de erro formatado
    task display_error(
        input string error_type,
        input string message,
        input logic [63:0] timestamp
    );
        $display("\n%s - ERRO: %s", format_timestamp(timestamp), error_type);
        $display("  User: jaquedebrito");
        $display("  Mensagem: %s", message);
        $display("  Ciclo: %0d", perf_stats.total_cycles);
        $display("  PC: 0x%h", dut.dp.pc);
    endtask

    // Verificação de término
    task check_termination();
        // Verificar condição de sucesso
        if (memwrite && dataadr === 32'h54 && writedata === 32'h1) begin
            $display("\n=================================================================");
            $display("%s - SUCESSO! Teste concluído após %0d ciclos.", 
                    format_timestamp(current_time), perf_stats.total_cycles);
            dump_final_state();
            $finish;
        end
        
        // Verificar timeout
        if (perf_stats.total_cycles >= 200) begin
            $display("\n=================================================================");
            $display("%s - TIMEOUT após %0d ciclos!", 
                    format_timestamp(current_time), perf_stats.total_cycles);
            dump_final_state();
            $finish;
        end
    endtask

    // Função auxiliar para converter status em string
    function string get_status_string(input logic [1:0] status);
        case (status)
            2'b00: return "Normal";
            2'b01: return "Stall/Busy";
            2'b10: return "Error";
            2'b11: return "Invalid/reserved";
            default: return "Unknown";
        endcase
    endfunction

    function void dump_final_state();
        $display("\n[%s] Final Pipeline State - User: jaquedebrito", TIMESTAMP);
        display_pipeline_status();
        display_performance_metrics();
    endfunction

    // Adicionar junto com as outras funções de display (próximo a display_stage_status)
    function void display_pipeline_status();
        $display("\nEstado do Pipeline:");
        $display("  IF: PC=0x%h", dut.dp.pc);
        $display("  ID: Instr=0x%h", dut.dp.instr_id);
        $display("  EX: ALUOut=0x%h", dut.dp.ULAout_ex);
        $display("  MEM: Data=0x%h", dut.dp.writedata_mem);
        $display("  WB: Result=0x%h", dut.dp.result_wb);
    endfunction

        // Adicionar junto com as outras funções auxiliares
    function string format_timestamp(input logic [63:0] time_value);
        return $sformatf("%s", TIMESTAMP);
    endfunction

    function void display_performance_metrics();
        $display("\nMétricas de Performance:");
        $display("  Ciclos totais: %0d", perf_stats.total_cycles);
        $display("  Instruções: %0d", perf_stats.instruction_count);
        $display("  CPI: %.2f", perf_stats.cpi);
        $display("  Taxa de acerto branch: %.2f%%", perf_stats.branch_accuracy);
        $display("  Taxa de stall: %.2f%%", perf_stats.stall_rate);
        $display("  Taxa de flush: %.2f%%", perf_stats.flush_rate);
    endfunction

    function void initialize_coverage();
        state_cg = new();
        hazard_cg = new();
        branch_cg = new();
        
        // Inicializar contadores
        stall_count = 0;
        flush_count = 0;
        branch_count = 0;
        overflow_count = 0;
        
        // Inicializar estrutura de performance
        perf_stats.total_cycles = 0;
        perf_stats.instruction_count = 0;
        perf_stats.cpi = 0.0;
        perf_stats.branch_accuracy = 0.0;
        perf_stats.stall_rate = 0.0;
        perf_stats.flush_rate = 0.0;
        perf_stats.data_hazards = 0;
        perf_stats.control_hazards = 0;
    endfunction

        // Bloco final
    final begin
        $display("\n=================================================================");
        $display("%s - Fim da Simulação", format_timestamp(current_time));
        $display("User: jaquedebrito");
        
        if (perf_stats.total_cycles < MAX_CYCLES) begin
            $display("\nATENÇÃO: Simulação terminada sem atingir condição de sucesso!");
            
            // Código movido da task dump_final_state() para cá
            $display("\n%s - Estado Final do Processador", format_timestamp(current_time));
            $display("User: jaquedebrito");
            $display("=================================================================");
            
            // Estatísticas do pipeline
            $display("\nEstatísticas do Pipeline:");
            $display("  Total de ciclos: %0d", perf_stats.total_cycles);
            $display("  Instruções executadas: %0d", perf_stats.instruction_count);
            $display("  CPI: %.2f", perf_stats.cpi);
            $display("  Stalls detectados: %0d (%.2f%%)", 
                    stall_count, perf_stats.stall_rate);
            $display("  Flushes detectados: %0d (%.2f%%)", 
                    flush_count, perf_stats.flush_rate);
            
            // Estatísticas de branches
            $display("\nEstatísticas de Branch:");
            $display("  Branches encontrados: %0d", branch_count);
            $display("  Branches tomados: %0d (%.2f%%)", 
                    branch_taken_count,
                    branch_count > 0 ? 100.0 * branch_taken_count / branch_count : 0);
            $display("  Precisão do predictor: %.2f%%", perf_stats.branch_accuracy);
            $display("  Penalidade média: %.2f ciclos", 
                    branch_taken_count > 0 ? real'(flush_count) / branch_taken_count : 0);
            
            // Estatísticas de erros
            $display("\nEstatísticas de Erros:");
            $display("  Overflows ULA: %0d", overflow_count);
            $display("  Erros de memória: %0d", memory_error_count);
            $display("  Erros de registrador: %0d", register_error_count);
            $display("  Data hazards: %0d", perf_stats.data_hazards);
            $display("  Control hazards: %0d", perf_stats.control_hazards);
            
            // Estado dos registradores
            $display("\nEstado Final dos Registradores:");
            for (int i = 0; i < 32; i++) begin
                if (dut.dp.id_stage.rf.rf[i] !== 0) begin
                    $display("  $%0d = %0d (0x%h)", 
                            i, 
                            $signed(dut.dp.id_stage.rf.rf[i]), 
                            dut.dp.id_stage.rf.rf[i]);
                end
            end
            
            // Estado do pipeline
            $display("\nEstado Final do Pipeline:");
            $display("  IF/ID: PC=%h, Instr=%h", 
                    dut.dp.pc, dut.dp.instr_id);
            $display("  ID/EX: RegWrite=%b, MemWrite=%b", 
                    dut.dp.regwrite_ex, dut.dp.memwrite_ex);
            $display("  EX/MEM: ALUOut=%h, WriteData=%h", 
                    dut.dp.ULAout_mem, dut.dp.writedata_mem);
            $display("  MEM/WB: Result=%h, WriteReg=%d", 
                    dut.dp.result_wb, dut.dp.rd_wb);
            
            // Estado dos módulos
            $display("\nEstado dos Módulos:");
            $display("  ULA Status: %s", get_status_string(ula_status));
            $display("  Memória Status: %s", get_status_string(mem_status));
            $display("  Registrador Status: %s", get_status_string(reg_status));
            
            // Últimos acessos
            $display("\nÚltimos Acessos:");
            for (int i = 0; i < 5; i++) begin
                $display("  %s: %s", 
                        stage_names[i], 
                        format_timestamp(last_access_times[i]));
            end
        end

        // Coverage Report
        $display("\n[%s] Coverage Report - User: jaquedebrito", TIMESTAMP);
        $display("Coverage Summary:");
        $display("  State Coverage: Configured");
        $display("  Hazard Coverage: Configured");
        $display("  Branch Prediction Coverage: Configured");
        
        $display("=================================================================\n");
    end
endmodule 