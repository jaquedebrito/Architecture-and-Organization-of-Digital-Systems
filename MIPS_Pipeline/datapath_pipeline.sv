module datapath_pipeline (
    // Sinais básicos
    input  logic        clk, reset,
    
    // Sinais de controle do ID
    input  logic        memtoreg_id, memwrite_id, memread_id,
    input  logic        ULAsrc_id, regdst_id,
    input  logic        regwrite_id, branch_id,
    input  logic [2:0]  ULAcontrol_id,
    
    // Interface com memórias
    input  logic [31:0] instr,           // Da memória de instruções
    input  logic [31:0] readdata,        // Da memória de dados
    
    // Sinais para hazards
    input  logic        stall,
    input  logic [1:0]  forward_a, forward_b,
    input  logic        clear_if_id,
    input  logic        clear_id_ex,
    input  logic        clear_ex_mem,
    input  logic        stall_if,
    input  logic        stall_id,
    
    // Saídas principais
    output logic [31:0] pc,              // Para memória de instruções
    output logic [31:0] ULAout_mem,      // Para memória de dados (endereço)
    output logic [31:0] writedata_mem,   // Para memória de dados (dado)
    output logic        zero_ex,         // Flag zero da ULA
    
    // Sinais para detecção de hazards
    output logic [4:0]  rs_id, rt_id,
    output logic [4:0]  rs_ex, rt_ex, rd_ex,
    output logic [4:0]  rd_mem, rd_wb,
    output logic        regwrite_ex, regwrite_mem, regwrite_wb,
    output logic        memwrite,
    output logic        memread_ex,
    
    // Sinais de branch prediction
    output logic        is_branch,
    output logic        branch_taken,
    output logic        prediction,
    output logic        branch_mispredicted,
    output logic [31:0] branch_target,
    output logic [31:0] pc_next,
    
    // Novas saídas para monitoramento
    output logic [31:0] hazard_count,          // Contador de hazards
    output logic [31:0] stall_count,           // Contador de stalls
    output logic [31:0] branch_mispredict_count, // Contador de mispredictions
    output logic [31:0] instruction_count,      // Contador de instruções
    output logic [1:0]  pipeline_status,        // Status do pipeline
    output logic [63:0] last_update_time        // Timestamp da última atualização
);
    // Definições de estado
    typedef enum logic[1:0] {
        PIPE_NORMAL = 2'b00,
        PIPE_STALL  = 2'b01,
        PIPE_FLUSH  = 2'b10,
        PIPE_ERROR  = 2'b11
    } pipe_state_t;

    // Sinais internos
    logic [31:0] pc_plus4, pc_plus4_id, pc_plus4_ex;
    logic [31:0] instr_id;
    logic [31:0] reg_data1_id, reg_data2_id;
    logic [31:0] signimm_id, signimm_ex;
    logic [31:0] ULAout_ex;
    logic [31:0] writedata_ex;
    logic [31:0] result_wb;
    logic [31:0] readdata_wb;
    logic [31:0] ULAout_wb;
    logic        memtoreg_ex, memwrite_ex;
    logic        ULAsrc_ex, regdst_ex;
    logic [2:0]  ULAcontrol_ex;
    logic        branch_ex, branch_mem_reg;
    logic        zero_mem;
    logic [31:0] pc_branch_mem;
    logic        pcsrc;
    logic [31:0] branch_target_early;
    logic        early_compare_result;
    logic        branch_detected;
    logic        flush;
    logic [4:0]  rd_id;
    logic [4:0]  write_reg_ex;
    logic        memtoreg_mem;
    logic        memread_mem;
    logic [1:0] if_stage_status;
    logic [1:0] id_stage_status;
    logic [1:0] ex_stage_status;
    logic [1:0] mem_stage_status;
    logic [1:0] wb_stage_status;
    logic fetch_ready_reg;
    logic instr_valid_reg;
    logic data_valid_reg;
    logic alu_ready_reg;
    logic mem_busy_reg;
    logic wb_valid_reg;
    logic [31:0] mem_latency_reg;
    logic data_valid_reg;
    
    // Timestamp e estado
    logic [63:0] current_time;
    pipe_state_t current_state;

    // Inicialização
    initial begin
        fetch_ready_reg = 1'b1;
        instr_valid_reg = 1'b1;
        data_valid_reg = 1'b1;
        alu_ready_reg = 1'b1;
        mem_busy_reg = 1'b0;
        wb_valid_reg = 1'b1;
        current_state = PIPE_NORMAL;
        hazard_count = 32'h0;
        stall_count = 32'h0;
        branch_mispredict_count = 32'h0;
        instruction_count = 32'h0;
    end

    // Lógica de flush
    assign flush = branch_mispredicted || (branch_mem_reg && pcsrc);

    // Estágio IF
     if_stage if_stage(
        .clk(clk),
        .reset(reset),
        .stall(stall),
        .branch_id(branch_id),
        .pc_branch(pc_branch_mem),
        .pcsrc(pcsrc),
        .prediction(prediction),
        .pc_predict(branch_target_early),
        .pc(pc),
        .pc_plus4(pc_plus4),
        .instr(instr),
        .current_instr(instr),
        .id_is_branch(is_branch),
        .id_branch_taken(branch_taken),
        // Novas conexões de monitoramento
        .fetch_cycles(instruction_count),
        .branch_misses(branch_mispredict_count),
        .stall_cycles(stall_count),
        .prediction_valid(prediction),
        .fetch_state(pipeline_status),
        .fetch_ready(fetch_ready_reg)  // Sempre pronto
    );

    // Registrador IF/ID
    if_id_reg if_id_reg(
        .clk(clk),
        .reset(reset),
        .clear(clear_if_id),
        .stall(stall_if),
        .flush(flush),
        // Remover a linha com .en()
        .pc_plus4_in(pc_plus4),
        .instr_in(instr),
        .pc_plus4_out(pc_plus4_id),
        .instr_out(instr_id),
        // Monitoramento
        .stall_count(stall_count),
        .flush_count(branch_mispredict_count),
        .clear_count(hazard_count),
        .reg_status(pipeline_status),
        .instr_valid(instr_valid_reg),
        .last_update_time(last_update_time),
        .bubble_count(stall_count)
    );

    // Estágio ID
    id_stage id_stage(
        .clk(clk),
        .reset(reset),
        .stall(stall),
        .flush(flush),
        .instr(instr_id),
        .pc_plus4(pc_plus4_id),
        .regwrite_wb(regwrite_wb),
        .write_reg_wb(rd_wb),
        .result_wb(result_wb),
        .alu_out_mem(ULAout_mem),
        .forward_a(forward_a),
        .forward_b(forward_b),
        .forward_a_id(forward_a),  
        .forward_b_id(forward_b),  
        .reg_data1(reg_data1_id),
        .reg_data2(reg_data2_id),
        .signimm(signimm_id),
        .rs(rs_id),
        .rt(rt_id),
        .rd(rd_id),
        .is_branch(is_branch),
        .branch_target_early(branch_target_early),
        .branch_detected(branch_detected),
        .branch_taken(branch_taken),
        .early_compare_result(early_compare_result),
        // Novas conexões de monitoramento
        .forward_cycles(forward_count),
        .branch_stall_needed(branch_mispredict_count)
    );

        // Registrador ID/EX
     id_ex_reg id_ex_reg(
        // Conexões básicas
        .clk(clk),
        .reset(reset),
        .flush(flush),
        .clear(clear_id_ex),
        .stall(stall_id),
        .en(~stall_id),  // Enable ativo baixo durante stall
        // Entradas
        .pc_plus4_in(pc_plus4_id),
        .reg_data1_in(reg_data1_id),
        .reg_data2_in(reg_data2_id),
        .signimm_in(signimm_id),
        .rs_in(rs_id),
        .rt_in(rt_id),
        .rd_in(rd_id),
        .regwrite_in(regwrite_id),
        .memtoreg_in(memtoreg_id),
        .memwrite_in(memwrite_id),
        .memread_in(memread_id),
        .ULAsrc_in(ULAsrc_id),
        .regdst_in(regdst_id),
        .ULAcontrol_in(ULAcontrol_id),
        .branch_in(branch_id),
        // Saídas
        .pc_plus4_out(pc_plus4_ex),
        .reg_data1_out(reg_data1_ex),
        .reg_data2_out(reg_data2_ex),
        .signimm_out(signimm_ex),
        .rs_out(rs_ex),
        .rt_out(rt_ex),
        .rd_out(rd_ex),
        .regwrite_out(regwrite_ex),
        .memtoreg_out(memtoreg_ex),
        .memwrite_out(memwrite_ex),
        .memread_out(memread_ex),
        .ULAsrc_out(ULAsrc_ex),
        .regdst_out(regdst_ex),
        .ULAcontrol_out(ULAcontrol_ex),
        .branch_out(branch_ex),
        // Monitoramento
        .instr_ex(instr_id),
        .stall_count(stall_count),
        .flush_count(branch_mispredict_count),
        .pipeline_status(pipeline_status),
        .data_valid(data_valid_reg),
        .last_update_time(last_update_time)
    );

    // Estágio EX
    ex_stage ex_stage(
        // Conexões básicas
        .clk(clk),
        .reset(reset),
        .pc_plus4(pc_plus4_ex),
        .reg_data1(reg_data1_ex),
        .reg_data2(reg_data2_ex),
        .signimm(signimm_ex),
        .rt(rt_ex),
        .rd(rd_ex),
        .ULAsrc(ULAsrc_ex),
        .regdst(regdst_ex),
        .ULAcontrol(ULAcontrol_ex),
        .forward_a(forward_a),
        .forward_b(forward_b),
        .ULAout_mem(ULAout_mem),
        .result_wb(result_wb),
        .ULAout(ULAout_ex),
        .zero(zero_ex),
        .pc_branch(pc_branch_mem),
        .write_data(writedata_ex),
        .write_reg(write_reg_ex),
        // Monitoramento
        .alu_ready(alu_ready_reg),
        .forward_count(forward_count),
        .alu_overflow(alu_overflow),
        .hazard_type(pipeline_status[1:0]),
        .execution_cycles(instruction_count)
    );

    // Registrador EX/MEM
    ex_mem_reg ex_mem_reg(
        // Conexões básicas
        .clk(clk),
        .reset(reset),
        .ULAout_in(ULAout_ex),
        .write_data_in(writedata_ex),
        .write_reg_in(write_reg_ex),
        .zero_in(zero_ex),
        .pc_branch_in(pc_branch_mem),
        .regwrite_in(regwrite_ex),
        .memtoreg_in(memtoreg_ex),
        .memwrite_in(memwrite_ex),
        .memread_in(memread_ex),
        .branch_in(branch_ex),
        // Saídas
        .ULAout_out(ULAout_mem),
        .write_data_out(writedata_mem),
        .write_reg_out(rd_mem),
        .zero_out(zero_mem),
        .pc_branch_out(pc_branch_mem),
        .regwrite_out(regwrite_mem),
        .memtoreg_out(memtoreg_mem),
        .memwrite_out(memwrite),
        .memread_out(memread_mem),
        .branch_out(branch_mem_reg),
        // Monitoramento
        .transfer_count(instruction_count),
        .branch_count(branch_count),
        .mem_access_count(memory_access_count),
        .reg_status(pipeline_status),
        .data_valid(data_valid_reg),
        .last_update_time(last_update_time)
    );

    // Estágio MEM
    mem_stage mem_stage(
        // Conexões básicas
        .clk(clk),
        .reset(reset),
        .branch(branch_mem_reg),
        .zero(zero_mem),
        .pcsrc(pcsrc),
        .memwrite(memwrite),
        .memread(memread_mem),
        .alu_result(ULAout_mem),
        .write_data(writedata_mem),
        .read_data(readdata),
        // Monitoramento
        .mem_access_count(memory_access_count),
        .branch_taken_count(branch_count),
        .mem_latency(32'h0),
        .mem_busy(mem_busy_reg),
        .mem_status(pipeline_status),
        .last_access_time(last_update_time)
    );

    // Registrador MEM/WB
    mem_wb_reg mem_wb_reg(
        // Conexões básicas
        .clk(clk),
        .reset(reset),
        .readdata_in(readdata),
        .ULAout_in(ULAout_mem),
        .write_reg_in(rd_mem),
        .regwrite_in(regwrite_mem),
        .memtoreg_in(memtoreg_mem),
        .readdata_out(readdata_wb),
        .ULAout_out(ULAout_wb),
        .write_reg_out(rd_wb),
        .regwrite_out(regwrite_wb),
        .memtoreg_out(memtoreg_wb),
        // Monitoramento
        .wb_count(instruction_count),
        .mem_read_count(memory_access_count),
        .alu_result_count(instruction_count),
        .reg_status(pipeline_status),
        .data_valid(1'b1),
        .last_update_time(last_update_time)
    );

    // Estágio WB
     wb_stage wb_stage(
        // Conexões básicas
        .clk(clk),
        .reset(reset),
        .readdata(readdata_wb),
        .ULAout(ULAout_wb),
        .memtoreg(memtoreg_wb),
        .result(result_wb),
        // Monitoramento
        .wb_cycles(instruction_count),
        .mem_reads(memory_access_count),
        .alu_uses(instruction_count),
        .wb_valid(wb_valid_reg),
        .timestamp(last_update_time),
        .last_values(result_wb)
    );

    // Lógica de branch prediction
    assign branch_mispredicted = branch_mem_reg && (prediction != pcsrc);
    assign branch_target = pc_branch_mem;
    assign pc_next = pc_plus4;

    // Monitoramento e contadores
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            hazard_count <= 32'h0;
            stall_count <= 32'h0;
            branch_mispredict_count <= 32'h0;
            instruction_count <= 32'h0;
            current_time <= 64'd1711800577; // 2025-03-20 12:09:37
            current_state <= PIPE_NORMAL;
        end else begin
            current_time <= current_time + 1;
            
            // Contagem de instruções
            if (!stall)
                instruction_count <= instruction_count + 1;
            
            // Detecção de hazards
            if (forward_a != 2'b00 || forward_b != 2'b00)
                hazard_count <= hazard_count + 1;
                
            // Contagem de stalls
            if (stall)
                stall_count <= stall_count + 1;
                
            // Contagem de branch mispredictions
            if (branch_mispredicted)
                branch_mispredict_count <= branch_mispredict_count + 1;
                
            // Atualização do estado do pipeline
            if (stall)
                current_state <= PIPE_STALL;
            else if (flush)
                current_state <= PIPE_FLUSH;
            else if (branch_mispredicted)
                current_state <= PIPE_ERROR;
            else
                current_state <= PIPE_NORMAL;
        end
    end

        // Debug logging
    `ifdef DEBUG
        always @(posedge clk) begin
            $display("%s - Pipeline Status:", format_timestamp(current_time));
            $display("  User: jaquedebrito");
            $display("  Pipeline State: %s", get_state_name(current_state));
            
            // Status dos estágios
            $display("  IF Stage:");
            $display("    PC: 0x%8h", pc);
            $display("    Next Instruction: 0x%8h", instr);
            
            $display("  ID Stage:");
            $display("    Instruction: 0x%8h", instr_id);
            $display("    Rs: %d, Rt: %d, Rd: %d", rs_id, rt_id, rd_id);
            
            $display("  EX Stage:");
            $display("    Operation: %s", get_ula_operation(ULAcontrol_ex));
            $display("    ALU Result: 0x%8h", ULAout_ex);
            $display("    Forward A: %b, Forward B: %b", forward_a, forward_b);
            
            $display("  MEM Stage:");
            $display("    Address: 0x%8h", ULAout_mem);
            $display("    MemWrite: %b, MemRead: %b", memwrite, memread_mem);
            
            $display("  WB Stage:");
            $display("    Write Reg: %d", rd_wb);
            $display("    Write Data: 0x%8h", result_wb);
            
            // Eventos especiais
            if (stall)
                $display("  WARNING: Pipeline stalled");
            if (branch_mispredicted)
                $display("  WARNING: Branch mispredicted");
            if (forward_a != 2'b00 || forward_b != 2'b00)
                $display("  INFO: Data forwarding active");
                
            // Estatísticas
            $display("  Statistics:");
            $display("    Instructions: %d", instruction_count);
            $display("    Hazards: %d", hazard_count);
            $display("    Stalls: %d", stall_count);
            $display("    Branch Mispredictions: %d", branch_mispredict_count);
        end
        
        // Função para formatação do timestamp
        function string format_timestamp(input logic [63:0] unix_time);
            return $sformatf("2025-03-20 12:11:%02d", unix_time % 60);
        endfunction
        
        // Função para converter estado em string
        function string get_state_name(input pipe_state_t state);
            case (state)
                PIPE_NORMAL: return "Normal";
                PIPE_STALL:  return "Stalled";
                PIPE_FLUSH:  return "Flushing";
                PIPE_ERROR:  return "Error";
                default:     return "Unknown";
            endcase
        endfunction
        
        // Função para converter operação da ULA em string
        function string get_ula_operation(input logic [2:0] ula_control);
            case (ula_control)
                3'b000: return "AND";
                3'b001: return "OR";
                3'b010: return "ADD";
                3'b110: return "SUB";
                3'b111: return "SLT";
                default: return "Unknown";
            endcase
        endfunction
    `endif

    // Assertions para verificação
    `ifdef FORMAL
        // Verificar consistência do pipeline
        property valid_pipeline_state;
            @(posedge clk) disable iff (reset)
            !(stall && flush);  // Stall e flush não podem ocorrer simultaneamente
        endproperty

        // Verificar forwarding válido
        property valid_forwarding;
            @(posedge clk) disable iff (reset)
            (forward_a != 2'b11) && (forward_b != 2'b11);  // Valores inválidos de forwarding
        endproperty

        // Verificar hazards estruturais
        property no_structural_hazards;
            @(posedge clk) disable iff (reset)
            !(memread_ex && memwrite);  // Não pode ler e escrever simultaneamente
        endproperty

        // Verificar branch prediction
        property valid_branch_prediction;
            @(posedge clk) disable iff (reset)
            branch_mispredicted |-> ##1 flush;  // Mispredição deve causar flush
        endproperty

        // Verificar stalls
        property valid_stall_behavior;
            @(posedge clk) disable iff (reset)
            stall |-> $stable(pc);  // PC deve permanecer estável durante stall
        endproperty

        // Verificar escrita no banco de registradores
        property valid_register_write;
            @(posedge clk) disable iff (reset)
            regwrite_wb |-> (rd_wb != 5'b0);  // Não escrever no registrador zero
        endproperty

        assert property (valid_pipeline_state)
            else $error("Invalid pipeline state: concurrent stall and flush");
        assert property (valid_forwarding)
            else $error("Invalid forwarding value detected");
        assert property (no_structural_hazards)
            else $error("Structural hazard: concurrent memory access");
        assert property (valid_branch_prediction)
            else $error("Invalid branch prediction behavior");
        assert property (valid_stall_behavior)
            else $error("Invalid stall behavior");
        assert property (valid_register_write)
            else $error("Invalid register write");

        // Coverage
        cover property (valid_pipeline_state);
        cover property (valid_forwarding);
        cover property (no_structural_hazards);
        cover property (valid_branch_prediction);
        cover property (valid_stall_behavior);
        cover property (valid_register_write);
    `endif

    // Status do pipeline
    assign pipeline_status = current_state;
    assign last_update_time = current_time;

    // Monitor de performance
    always_ff @(posedge clk) begin
        if (!stall && !reset) begin
            if (instruction_count % 1000 == 0) begin
                $display("%s - Performance Metrics:", format_timestamp(current_time));
                $display("  User: jaquedebrito");
                $display("  Instructions executed: %d", instruction_count);
                $display("  Hazard rate: %f%%", 100.0 * hazard_count / instruction_count);
                $display("  Stall rate: %f%%", 100.0 * stall_count / instruction_count);
                $display("  Branch misprediction rate: %f%%", 
                    100.0 * branch_mispredict_count / instruction_count);
            end
        end
    end

endmodule