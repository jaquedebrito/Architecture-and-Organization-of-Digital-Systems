// Aluna: Jaqueline Ferreira de Brito
// Módulo top para o processador MIPS pipeline
import types_pkg::*;

module top_pipeline (
    // Interface básica
    input  logic        clk, reset,
    output logic [31:0] writedata, dataadr,
    output logic        memwrite,
    
    // Novas saídas para monitoramento
    output logic [31:0] instruction_count,    // Contador de instruções
    output logic [31:0] cycle_count,          // Contador de ciclos
    output logic [31:0] stall_count,          // Contador de stalls
    output logic [31:0] branch_count,         // Contador de branches
    output logic [31:0] memory_access_count,  // Contador de acessos à memória
    output logic [1:0]  processor_status,     // Status do processador
    output logic [63:0] last_update_time      // Timestamp da última atualização
);

    // Sinais básicos do pipeline
    logic [31:0] pc, instr, readdata;
    logic        zero_ex;
    
    // Sinais de controle gerados no ID
    logic        memtoreg_id, memwrite_id, memread_id;
    logic        ULAsrc_id, regdst_id;
    logic        regwrite_id, branch_id;
    logic [2:0]  ULAcontrol_id;

    // Sinais para hazards
    logic        stall, flush;
    logic [1:0]  forward_a, forward_b;
    logic        clear_if_id, clear_id_ex, clear_ex_mem;
    logic        stall_if, stall_id;
    
    // Sinais para detecção de hazards
    logic [4:0]  rs_id, rt_id;
    logic [4:0]  rs_ex, rt_ex, rd_ex;
    logic [4:0]  rd_mem, rd_wb;
    logic        regwrite_ex, regwrite_mem, regwrite_wb;
    logic        memread_ex;
    logic        memwrite_mem;

    // Sinais de branch prediction
    logic        is_branch;
    logic        branch_taken;
    logic        prediction;
    logic        branch_mispredicted;
    logic [31:0] branch_target;
    logic [31:0] pc_next;
    logic        flush_pipeline;

    // Sinais de monitoramento
    proc_state_t current_state;
    logic [63:0] current_time;
    logic [31:0] instruction_type_count[6];  // R-type, Load, Store, Branch, Jump, Other
    logic [31:0] hazard_count;
    logic [31:0] branch_mispredict_count;
    logic        pipeline_error;

    // Apenas os sinais que não são outputs
    logic [31:0] control_hazard_count;
    logic [31:0] data_hazard_count;
    logic [31:0] forward_count;
    logic [1:0]  controller_status;

    // Inicialização
    initial begin
        current_state = PROC_NORMAL;
        cycle_count = 32'h0;
        instruction_count = 32'h0;
        stall_count = 32'h0;
        branch_count = 32'h0;
        memory_access_count = 32'h0;
        hazard_count = 32'h0;
        branch_mispredict_count = 32'h0;
        pipeline_error = 1'b0;
        
        for (int i = 0; i < 6; i++)
            instruction_type_count[i] = 32'h0;
    end

    // Instância do controlador
    controller_pipeline c(
        // Sinais básicos
        .clk(clk),
        .reset(reset),
        .op(instr[31:26]),
        .funct(instr[5:0]),
        .zero_ex(zero_ex),
        .pcsrc(dp.mem_stage.pcsrc),

        // IDs dos registradores
        .rs_id(rs_id),
        .rt_id(rt_id),
        .rs_ex(rs_ex),
        .rt_ex(rt_ex),
        .rd_ex(rd_ex),
        .rd_mem(rd_mem),
        .rd_wb(rd_wb),

        // Sinais de controle
        .regwrite_ex(regwrite_ex),
        .regwrite_mem(regwrite_mem),
        .regwrite_wb(regwrite_wb),
        .memread_ex(memread_ex),
        .memtoreg_id(memtoreg_id),
        .memwrite_id(memwrite_id),
        .memread_id(memread_id),
        .branch_id(branch_id),
        .ULAsrc_id(ULAsrc_id),
        .regdst_id(regdst_id),
        .regwrite_id(regwrite_id),
        .ULAcontrol_id(ULAcontrol_id),

        // Forwarding e branch
        .forward_a(forward_a),
        .forward_b(forward_b),
        .is_branch(is_branch),
        .branch_mispredicted(branch_mispredicted),
        .branch_predicted(prediction),
        .branch_actual(branch_taken),
        .branch_target(branch_target),
        .jump_id(jump_id),
        .branch_taken(branch_taken),

        // Sinais de controle de pipeline
        .clear_if_id(clear_if_id),
        .clear_id_ex(clear_id_ex),
        .clear_ex_mem(clear_ex_mem),
        .stall_if(stall_if),
        .stall_id(stall_id),

        // Contadores e monitoramento
        .control_hazard_count(control_hazard_count),  // Esta é a conexão correta
        .data_hazard_count(data_hazard_count),
        .stall_count(stall_count),
        .forward_count(forward_count),
        .controller_status(controller_status),
        .last_update_time(last_update_time)
    );

    // Instância do datapath
    datapath_pipeline dp(
        .clk(clk),
        .reset(reset),
        .memtoreg_id(memtoreg_id),
        .memwrite_id(memwrite_id),
        .memread_id(memread_id),
        .ULAsrc_id(ULAsrc_id),
        .regdst_id(regdst_id),
        .regwrite_id(regwrite_id),
        .branch_id(branch_id),
        .ULAcontrol_id(ULAcontrol_id),
        .zero_ex(zero_ex),
        .pc(pc),
        .instr(instr),
        .ULAout_mem(dataadr),
        .writedata_mem(writedata),
        .readdata(readdata),
        .stall(stall),
        .forward_a(forward_a),
        .forward_b(forward_b),
        .rs_id(rs_id),
        .rt_id(rt_id),
        .rs_ex(rs_ex),
        .rt_ex(rt_ex),
        .rd_ex(rd_ex),
        .rd_mem(rd_mem),
        .rd_wb(rd_wb),
        .regwrite_ex(regwrite_ex),
        .regwrite_mem(regwrite_mem),
        .regwrite_wb(regwrite_wb),
        .memread_ex(memread_ex),
        .is_branch(is_branch),
        .branch_taken(branch_taken),
        .prediction(prediction),
        .branch_mispredicted(branch_mispredicted),
        .branch_target(branch_target),
        .pc_next(pc_next),
        .clear_if_id(clear_if_id),
        .clear_id_ex(clear_id_ex),
        .clear_ex_mem(clear_ex_mem),
        .memwrite(memwrite),
        .stall_if(stall_if),                  // Nova conexão
        .stall_id(stall_id),                  // Nova conexão
        .hazard_count(hazard_count),          // Nova conexão
        .stall_count(stall_count),            // Nova conexão
        .branch_mispredict_count(branch_mispredict_count), // Nova conexão
        .instruction_count(instruction_count), // Nova conexão
        .pipeline_status(processor_status),    // Nova conexão
        .last_update_time(last_update_time)    // Nova conexão
    );

    // Memória de instruções com proteção
    instruction_memory imem(
        .addr(pc[7:2]),
        .instr(instr),
        .fetch_count(instruction_count),
        .error_count(),
        .mem_status(),
        .load_success(),
        .last_access_time(last_update_time)
    );

    // Memória de dados com proteção
    data_memory dmem(
        .clk(clk),
        .reset(reset),                        // Nova conexão
        .we(memwrite_mem),
        .re(memread_id),
        .addr(dataadr[7:2]),
        .wd(writedata),
        .rd(readdata),
        .read_count(),                        // Opcional
        .write_count(),                       // Opcional
        .error_count(),                       // Opcional
        .mem_status(),                        // Opcional
        .access_valid(),                      // Opcional
        .last_access_time(last_update_time),  // Nova conexão
        .last_addr_accessed()                 // Opcional
    );

    // Monitoramento e contadores
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            cycle_count <= 32'h0;
            instruction_count <= 32'h0;
            stall_count <= 32'h0;
            branch_count <= 32'h0;
            memory_access_count <= 32'h0;
            hazard_count <= 32'h0;
            branch_mispredict_count <= 32'h0;
            current_time <= 64'd1711801507; // 2025-03-20 12:25:07
            current_state <= PROC_NORMAL;
            pipeline_error <= 1'b0;
            
            for (int i = 0; i < 6; i++)
                instruction_type_count[i] <= 32'h0;
        end else begin
            current_time <= current_time + 1;
            cycle_count <= cycle_count + 1;
            
            // Contagem de instruções por tipo
            if (!stall) begin
                instruction_count <= instruction_count + 1;
                case (instr[31:26])
                    6'b000000: instruction_type_count[0] <= instruction_type_count[0] + 1; // R-type
                    6'b100011: instruction_type_count[1] <= instruction_type_count[1] + 1; // Load
                    6'b101011: instruction_type_count[2] <= instruction_type_count[2] + 1; // Store
                    6'b000100: instruction_type_count[3] <= instruction_type_count[3] + 1; // Branch
                    6'b000010: instruction_type_count[4] <= instruction_type_count[4] + 1; // Jump
                    default:   instruction_type_count[5] <= instruction_type_count[5] + 1; // Other
                endcase
            end
            
            // Contadores de eventos
            if (stall)
                stall_count <= stall_count + 1;
            if (is_branch)
                branch_count <= branch_count + 1;
            if (memwrite_mem || memread_id)
                memory_access_count <= memory_access_count + 1;
            if (forward_a != 2'b00 || forward_b != 2'b00)
                hazard_count <= hazard_count + 1;
            if (branch_mispredicted)
                branch_mispredict_count <= branch_mispredict_count + 1;
                
            // Atualização de estado
            case ({stall, flush, pipeline_error})
                3'b100: current_state <= PROC_STALL;
                3'b010: current_state <= PROC_FLUSH;
                3'b001: current_state <= PROC_ERROR;
                3'b000: current_state <= PROC_NORMAL;
                default: current_state <= PROC_ERROR;
            endcase
        end
    end

    // Debug logging
    `ifdef DEBUG
        always @(posedge clk) begin
            $display("%s - Processor Status:", format_timestamp(current_time));
            $display("  User: jaquedebrito");
            $display("  State: %s", get_state_name(current_state));
            
            if (!stall) begin
                $display("  Current Instruction:");
                $display("    PC: 0x%h", pc);
                $display("    Instruction: 0x%h", instr);
                $display("    Type: %s", get_instruction_type(instr[31:26]));
            end
            
            if (stall)
                $display("  WARNING: Pipeline stalled");
            if (branch_mispredicted)
                $display("  WARNING: Branch mispredicted");
            if (pipeline_error)
                $display("  ERROR: Pipeline error detected");
            
            $display("  Statistics:");
            $display("    Cycles: %d", cycle_count);
            $display("    Instructions: %d", instruction_count);
            $display("    IPC: %f", $itor(instruction_count) / $itor(cycle_count));
            $display("    Stalls: %d", stall_count);
            $display("    Hazards: %d", hazard_count);
            $display("    Branch Mispredictions: %d", branch_mispredict_count);
        end
        
        function string format_timestamp(input logic [63:0] unix_time);
            return $sformatf("2025-03-20 12:25:%02d", unix_time % 60);
        endfunction
        
        function string get_state_name(input proc_state_t state);
            case (state)
                PROC_NORMAL: return "Normal";
                PROC_STALL:  return "Stalled";
                PROC_FLUSH:  return "Flushing";
                PROC_ERROR:  return "Error";
                default:     return "Unknown";
            endcase
        endfunction
        
        function string get_instruction_type(input logic [5:0] opcode);
            case (opcode)
                6'b000000: return "R-type";
                6'b100011: return "Load";
                6'b101011: return "Store";
                6'b000100: return "Branch";
                6'b000010: return "Jump";
                default:   return "Other";
            endcase
        endfunction

        function string get_state_name(input [1:0] state);
            case (state)
                2'b00: return "NORMAL";
                2'b01: return "STALL";
                2'b10: return "FLUSH";
                2'b11: return "ERROR";
                default: return "UNKNOWN";
            endcase
        endfunction

    `endif

    // Assertions formais aprimoradas
    `ifdef FORMAL
        // Verificações básicas
        property valid_pipeline_state;
            @(posedge clk) disable iff (reset)
            !(stall && flush);
        endproperty

        property valid_branch_prediction;
            @(posedge clk) disable iff (reset)
            branch_mispredicted |-> flush;
        endproperty

        property valid_branch_target;
            @(posedge clk) disable iff (reset)
            is_branch |-> |branch_target;
        endproperty

        // Verificações avançadas
        property valid_memory_access;
            @(posedge clk) disable iff (reset)
            !(memwrite_mem && memread_id && (dataadr[7:2] == pc[7:2]));
        endproperty

        property valid_instruction_flow;
            @(posedge clk) disable iff (reset)
            !stall |-> (pc_next != pc);
        endproperty

        property valid_hazard_handling;
            @(posedge clk) disable iff (reset)
            (forward_a != 2'b00 || forward_b != 2'b00) |-> !stall;
        endproperty

        assert property (valid_pipeline_state)
            else $error("Invalid pipeline state detected");
        assert property (valid_branch_prediction)
            else $error("Invalid branch prediction behavior");
        assert property (valid_branch_target)
            else $error("Invalid branch target");
        assert property (valid_memory_access)
            else $error("Invalid memory access pattern");
        assert property (valid_instruction_flow)
            else $error("Invalid instruction flow");
        assert property (valid_hazard_handling)
            else $error("Invalid hazard handling");

        // Coverage
        cover property (valid_pipeline_state);
        cover property (valid_branch_prediction);
        cover property (valid_branch_target);
        cover property (valid_memory_access);
        cover property (valid_instruction_flow);
        cover property (valid_hazard_handling);
    `endif

        // Atribuições finais
    assign memwrite = memwrite_mem;
    assign processor_status = current_state;
    assign last_update_time = current_time;

    // Performance Monitor
    performance_monitor #(
        .WINDOW_SIZE(1000)  // Janela de monitoramento em ciclos
    ) perf_monitor (
        .clk(clk),
        .reset(reset),
        .current_time(current_time),
        .instruction_count(instruction_count),
        .cycle_count(cycle_count),
        .stall_count(stall_count),
        .branch_count(branch_count),
        .branch_mispredict_count(branch_mispredict_count),
        .hazard_count(hazard_count),
        .memory_access_count(memory_access_count),
        .instruction_type_counts(instruction_type_count),
        .current_state(current_state)
    );

    // Error Detection and Handling
    always_ff @(posedge clk) begin
        if (pipeline_error) begin
            $display("%s - CRITICAL ERROR detected in pipeline!", 
                    format_timestamp(current_time));
            $display("  User: jaquedebrito");
            $display("  PC: 0x%h", pc);
            $display("  Instruction: 0x%h", instr);
            $display("  Current State: %s", get_state_name(current_state));
            $display("  Error Details:");
            $display("    Stall: %b", stall);
            $display("    Flush: %b", flush);
            $display("    Branch Mispredicted: %b", branch_mispredicted);
            $display("    Memory Write: %b", memwrite_mem);
            $display("    Memory Read: %b", memread_id);
            $finish;
        end
    end

    // Performance Statistics Logger
    `ifdef PERFORMANCE_LOGGING
        always @(posedge clk) begin
            if (cycle_count % 10000 == 0) begin  // Log a cada 10000 ciclos
                $fwrite(perf_log, "%s - Performance Report\n", 
                       format_timestamp(current_time));
                $fwrite(perf_log, "  User: jaquedebrito\n");
                $fwrite(perf_log, "  Cycles: %d\n", cycle_count);
                $fwrite(perf_log, "  Instructions: %d\n", instruction_count);
                $fwrite(perf_log, "  IPC: %f\n", 
                       $itor(instruction_count) / $itor(cycle_count));
                $fwrite(perf_log, "  Stall Rate: %f%%\n", 
                       100.0 * $itor(stall_count) / $itor(cycle_count));
                $fwrite(perf_log, "  Branch Prediction Accuracy: %f%%\n",
                       100.0 * (1.0 - $itor(branch_mispredict_count) / 
                       $itor(branch_count)));
                $fwrite(perf_log, "  Instruction Mix:\n");
                $fwrite(perf_log, "    R-type: %f%%\n", 
                       100.0 * $itor(instruction_type_count[0]) / 
                       $itor(instruction_count));
                $fwrite(perf_log, "    Load: %f%%\n", 
                       100.0 * $itor(instruction_type_count[1]) / 
                       $itor(instruction_count));
                $fwrite(perf_log, "    Store: %f%%\n", 
                       100.0 * $itor(instruction_type_count[2]) / 
                       $itor(instruction_count));
                $fwrite(perf_log, "    Branch: %f%%\n", 
                       100.0 * $itor(instruction_type_count[3]) / 
                       $itor(instruction_count));
                $fwrite(perf_log, "    Jump: %f%%\n", 
                       100.0 * $itor(instruction_type_count[4]) / 
                       $itor(instruction_count));
                $fwrite(perf_log, "    Other: %f%%\n", 
                       100.0 * $itor(instruction_type_count[5]) / 
                       $itor(instruction_count));
                $fwrite(perf_log, "\n");
            end
        end

        initial begin
            perf_log = $fopen("pipeline_performance.log", "w");
            $fwrite(perf_log, "Pipeline Performance Log\n");
            $fwrite(perf_log, "Started at: %s\n", 
                   format_timestamp(current_time));
            $fwrite(perf_log, "User: jaquedebrito\n\n");
        end

        final begin
            $fwrite(perf_log, "\nFinal Statistics:\n");
            $fwrite(perf_log, "Total Cycles: %d\n", cycle_count);
            $fwrite(perf_log, "Total Instructions: %d\n", instruction_count);
            $fwrite(perf_log, "Average IPC: %f\n", 
                   $itor(instruction_count) / $itor(cycle_count));
            $fwrite(perf_log, "Total Stalls: %d\n", stall_count);
            $fwrite(perf_log, "Total Branch Mispredictions: %d\n", 
                   branch_mispredict_count);
            $fclose(perf_log);
        end
    `endif

    // Pipeline Status Monitor
    `ifdef PIPELINE_MONITOR
        always @(posedge clk) begin
            if (!stall) begin
                $display("%s - Pipeline Status:", format_timestamp(current_time));
                $display("  User: jaquedebrito");
                $display("  IF Stage:");
                $display("    PC: 0x%h", pc);
                $display("    Next Instruction: 0x%h", instr);
                
                $display("  ID Stage:");
                $display("    Rs: %d", rs_id);
                $display("    Rt: %d", rt_id);
                $display("    Control Signals:");
                $display("      RegWrite: %b", regwrite_id);
                $display("      MemRead: %b", memread_id);
                $display("      MemWrite: %b", memwrite_id);
                
                $display("  EX Stage:");
                $display("    Rs: %d", rs_ex);
                $display("    Rt: %d", rt_ex);
                $display("    Rd: %d", rd_ex);
                $display("    Forward A: %b", forward_a);
                $display("    Forward B: %b", forward_b);
                
                $display("  MEM Stage:");
                $display("    Address: 0x%h", dataadr);
                $display("    Write Data: 0x%h", writedata);
                $display("    MemWrite: %b", memwrite_mem);
                
                $display("  WB Stage:");
                $display("    Rd: %d", rd_wb);
                $display("    RegWrite: %b", regwrite_wb);
            end
        end
    `endif
endmodule