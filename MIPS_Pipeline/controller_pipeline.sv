module controller_pipeline (
    // Sinais básicos
    input  logic        clk, reset,
    input  logic [5:0]  op, funct,
    input  logic        zero_ex,
    input  logic        pcsrc,
    input  logic        branch_id,
    input  logic        jump_id,
    input  logic        branch_taken,
    input  logic [4:0]  rs_id, rt_id,
    input  logic [4:0]  rs_ex, rt_ex, rd_ex,
    input  logic [4:0]  rd_mem, rd_wb,
    input  logic        regwrite_ex, regwrite_mem, regwrite_wb,
    input  logic        memread_ex,
    input  logic        branch_predicted,
    input  logic        branch_actual,
    
    // Saídas de controle
    output logic        memtoreg_id, memwrite_id, memread_id,
    output logic        ULAsrc_id, regdst_id,
    output logic        regwrite_id,
    output logic [2:0]  ULAcontrol_id,
    output logic        clear_if_id, clear_id_ex, clear_ex_mem,
    output logic        stall_if, stall_id,
    output logic        is_branch,
    output logic [1:0]  forward_a, forward_b,
    output logic        branch_mispredicted,
    output logic [31:0] branch_target,
    
    // Novas saídas para monitoramento
    output logic [31:0] control_hazard_count,    // Contador de hazards de controle
    output logic [31:0] data_hazard_count,       // Contador de hazards de dados
    output logic [31:0] stall_count,             // Contador de stalls
    output logic [31:0] forward_count,           // Contador de forwarding
    output logic [1:0]  controller_status,       // Status do controlador
    output logic [63:0] last_update_time         // Timestamp da última atualização

);
    // Definições de estado
    typedef enum logic[1:0] {
        CTRL_NORMAL = 2'b00,
        CTRL_STALL  = 2'b01,
        CTRL_HAZARD = 2'b10,
        CTRL_ERROR  = 2'b11
    } ctrl_state_t;

    // Sinais internos
    logic [1:0]  ULAop_id;
    logic        load_hazard;
    logic        branch_hazard;
    logic        jump_taken;
    logic        control_hazard;
    logic        memread_mem;
    logic        memread_wb;
    logic        forward_mem;
    logic stall, flush;
    
    // Monitoramento
    ctrl_state_t current_state;
    logic [63:0] current_time;
    logic [31:0] instruction_type_count[6];  // Contador por tipo de instrução
    logic        invalid_operation;

    // Inicialização
    initial begin
        current_time = 64'd1711800777; // 2025-03-20 12:12:57
        current_state = CTRL_NORMAL;
        control_hazard_count = 32'h0;
        data_hazard_count = 32'h0;
        stall_count = 32'h0;
        forward_count = 32'h0;
        invalid_operation = 1'b0;
        
        for (int i = 0; i < 6; i++)
            instruction_type_count[i] = 32'h0;
    end

    // Unidade de controle principal
    main_control mc(
        .op(op),
        .memread(memread_id),
        .memtoreg(memtoreg_id),
        .memwrite(memwrite_id),
        .branch(branch_id),
        .ULAsrc(ULAsrc_id),
        .regdst(regdst_id),
        .regwrite(regwrite_id),
        .ULAop(ULAop_id)
    );

    // Unidade de controle da ULA
    ula_control uc(
        .funct(funct),
        .ULAop(ULAop_id),
        .ULAcontrol(ULAcontrol_id)
    );
    
    // Unidade de forwarding
    forwarding_unit fu(
        .clk(clk),
        .rst_n(!reset),
        .rs_ex(rs_ex),
        .rt_ex(rt_ex),
        .rd_mem(rd_mem),
        .rd_wb(rd_wb),
        .regwrite_mem(regwrite_mem),
        .regwrite_wb(regwrite_wb),
        .forward_a(forward_a),
        .forward_b(forward_b),
        .memread_mem(memread_mem),
        .memread_wb(memread_wb),
        .forward_mem(forward_mem),
        .forward_count_a(forward_count),          // Conectar ao contador global
        .forward_count_b(forward_count),          // Conectar ao contador global
        .forward_count_mem(forward_count),        // Conectar ao contador global
        .forward_status(controller_status),       // Conectar ao status
        .last_update_time(last_update_time)       // Conectar
    );

    // Unidade de detecção de hazards
    hazard_detection_unit hdu(
        .rs_id(rs_id),
        .rt_id(rt_id),
        .rt_ex(rt_ex),
        .rd_ex(rd_ex),
        .rd_mem(rd_mem),
        .memread_ex(memread_ex),
        .regwrite_ex(regwrite_ex),
        .branch_id(branch_id),
        .branch_taken(branch_taken),
        .jump_id(jump_id),
        .load_hazard(load_hazard),
        .branch_hazard(branch_hazard),
        .control_hazard(control_hazard),
        .load_hazard_count(data_hazard_count),    // Conectar
        .branch_hazard_count(branch_count),       // Conectar
        .control_hazard_count(control_hazard_count), // Conectar
        .hazard_status(controller_status),        // Conectar
        .last_update_time(last_update_time)       // Conectar
    );

    assign stall = stall_if || stall_id;
    assign flush = clear_if_id || clear_id_ex || clear_ex_mem;

    // Lógica de controle com monitoramento
    always_comb begin
        // Lógica básica
        jump_taken = jump_id;
        is_branch = (op == 6'b000100);
        branch_mispredicted = branch_id && (branch_predicted != branch_actual);
        
        // Sinais de controle
        clear_if_id = branch_mispredicted || jump_taken;
        stall_if = load_hazard || branch_hazard;
        stall_id = load_hazard;
        
        // Verificação de operação válida
        invalid_operation = 0;
        case (op)
            6'b000000: ; // R-type
            6'b100011: ; // lw
            6'b101011: ; // sw
            6'b000100: ; // beq
            6'b001000: ; // addi
            default: invalid_operation = 1;
        endcase
    end

    // Monitoramento e contadores
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            control_hazard_count <= 32'h0;
            data_hazard_count <= 32'h0;
            stall_count <= 32'h0;
            forward_count <= 32'h0;
            current_time <= 64'd1711800777; // 2025-03-20 12:12:57
            current_state <= CTRL_NORMAL;
            
            for (int i = 0; i < 6; i++)
                instruction_type_count[i] <= 32'h0;
        end else begin
            current_time <= current_time + 1;
            
            // Contagem de hazards
            if (control_hazard)
                control_hazard_count <= control_hazard_count + 1;
            if (load_hazard || branch_hazard)
                data_hazard_count <= data_hazard_count + 1;
                
            // Contagem de stalls
            if (stall_if || stall_id)
                stall_count <= stall_count + 1;
                
            // Contagem de forwarding
            if (forward_a != 2'b00 || forward_b != 2'b00)
                forward_count <= forward_count + 1;
                
            // Contagem por tipo de instrução
            case (op)
                6'b000000: instruction_type_count[0] <= instruction_type_count[0] + 1; // R-type
                6'b100011: instruction_type_count[1] <= instruction_type_count[1] + 1; // lw
                6'b101011: instruction_type_count[2] <= instruction_type_count[2] + 1; // sw
                6'b000100: instruction_type_count[3] <= instruction_type_count[3] + 1; // beq
                6'b001000: instruction_type_count[4] <= instruction_type_count[4] + 1; // addi
                default:   instruction_type_count[5] <= instruction_type_count[5] + 1; // outros
            endcase
            
            // Atualização de estado
            if (invalid_operation)
                current_state <= CTRL_ERROR;
            else if (load_hazard || branch_hazard)
                current_state <= CTRL_HAZARD;
            else if (stall_if || stall_id)
                current_state <= CTRL_STALL;
            else
                current_state <= CTRL_NORMAL;
        end
    end

    // Debug logging
    `ifdef DEBUG
        always @(posedge clk) begin
            $display("%s - Controller Status:", format_timestamp(current_time));
            $display("  User: jaquedebrito");
            $display("  State: %s", get_state_name(current_state));
            
            // Instruções
            $display("  Current Instruction:");
            $display("    Opcode: 0x%h", op);
            $display("    Type: %s", get_instruction_type(op));
            
            // Hazards e Forwarding
            if (load_hazard || branch_hazard)
                $display("  WARNING: Data hazard detected");
            if (control_hazard)
                $display("  WARNING: Control hazard detected");
            if (forward_a != 2'b00 || forward_b != 2'b00)
                $display("  INFO: Forwarding active");
                
            // Estatísticas
            $display("  Statistics:");
            $display("    Control Hazards: %d", control_hazard_count);
            $display("    Data Hazards: %d", data_hazard_count);
            $display("    Stalls: %d", stall_count);
            $display("    Forwarding: %d", forward_count);
        end
        
        function string format_timestamp(input logic [63:0] unix_time);
            return $sformatf("2025-03-20 12:12:%02d", unix_time % 60);
        endfunction
        
        function string get_state_name(input ctrl_state_t state);
            case (state)
                CTRL_NORMAL: return "Normal";
                CTRL_STALL:  return "Stalled";
                CTRL_HAZARD: return "Hazard";
                CTRL_ERROR:  return "Error";
                default:     return "Unknown";
            endcase
        endfunction
        
        function string get_instruction_type(input logic [5:0] opcode);
            case (opcode)
                6'b000000: return "R-type";
                6'b100011: return "Load";
                6'b101011: return "Store";
                6'b000100: return "Branch";
                6'b001000: return "Immediate";
                default:   return "Unknown";
            endcase
        endfunction
    `endif

    // Assertions para verificação
    `ifdef FORMAL
        // Verificar operações válidas
        property valid_operation;
            @(posedge clk) disable iff (reset)
            !invalid_operation;
        endproperty

        // Verificar hazards mútuos
        property exclusive_hazards;
            @(posedge clk) disable iff (reset)
            !(load_hazard && branch_hazard);
        endproperty

        // Verificar forwarding válido
        property valid_forwarding;
            @(posedge clk) disable iff (reset)
            (forward_a != 2'b11) && (forward_b != 2'b11);
        endproperty

        // Verificar stalls
        property valid_stall;
            @(posedge clk) disable iff (reset)
            stall_if |-> stall_id;
        endproperty

        assert property (valid_operation)
            else $error("Invalid operation detected");
        assert property (exclusive_hazards)
            else $error("Multiple hazards detected");
        assert property (valid_forwarding)
            else $error("Invalid forwarding value");
        assert property (valid_stall)
            else $error("Invalid stall behavior");

        // Coverage
        cover property (valid_operation);
        cover property (exclusive_hazards);
        cover property (valid_forwarding);
        cover property (valid_stall);
    `endif

    // Status do controlador
    assign controller_status = current_state;
    assign last_update_time = current_time;

endmodule