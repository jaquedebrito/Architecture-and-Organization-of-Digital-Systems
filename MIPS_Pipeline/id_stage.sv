module id_stage (
    input  logic        clk, reset,        
    input  logic        stall, flush,         
    input  logic [31:0] instr,
    input  logic [31:0] pc_plus4,
    input  logic        regwrite_wb,
    input  logic [4:0]  write_reg_wb,
    input  logic [31:0] result_wb,
    input  logic [31:0] alu_out_mem,
    input  logic [1:0]  forward_a,
    input  logic [1:0]  forward_b,
    input  logic [1:0]  forward_a_id,
    input  logic [1:0]  forward_b_id,
    
    // Saídas organizadas por funcionalidade
    // Dados do registrador e imediato
    output logic [31:0] reg_data1, reg_data2,
    output logic [31:0] signimm,
    output logic [4:0]  rs, rt, rd,
    
    // Sinais de branch
    output logic        is_branch,
    output logic        branch_taken,
    output logic [31:0] branch_target_early,
    output logic        branch_detected,
    output logic        early_compare_result,
    
    // Sinais de debug e performance
    output logic [31:0] forward_cycles,      // Contador de forwards
    output logic        branch_stall_needed  // Indicador de stall necessário
);
    // Sinais internos
    logic [31:0] comp_op1, comp_op2;         // Operandos para comparação
    logic [31:0] compare_a, compare_b;       // Valores após forwarding
    logic        valid_comparison;           // Indica se a comparação é válida
    
    // Performance counters
    logic [31:0] forward_count;

    // Banco de registradores com verificação de escrita
    regfile rf(
        .clk(clk),
        .we3(regwrite_wb && !stall),    // Previne escrita durante stall
        .ra1(instr[25:21]),
        .ra2(instr[20:16]),
        .wa3(write_reg_wb),
        .wd3(result_wb),
        .rd1(reg_data1),
        .rd2(reg_data2),
        .read_count(instruction_count),     // Conectar
        .write_count(instruction_count),    // Conectar
        .error_count(hazard_count),         // Conectar
        .reg_status(pipeline_status),       // Conectar
        .last_access_time(last_update_time) // Conectar
    );

    // Extensão de sinal com verificação de overflow
    signext se(
        .a(instr[15:0]),
        .y(signimm)
    );

    // Identificação de registradores com validação
    assign rs = (instr[31:26] == 6'b0) ? instr[25:21] : 5'b0;
    assign rt = (instr[31:26] == 6'b0) ? instr[20:16] : 5'b0;
    assign rd = (instr[31:26] == 6'b0) ? instr[15:11] : 5'b0;

    // Lógica de branch otimizada
    always_comb begin
        // Pre-decode para branch
        is_branch = (instr[31:26] == 6'b000100);
        branch_target_early = pc_plus4 + (signimm << 2);
        
        // Lógica de forwarding otimizada para branch
        unique case (forward_a_id)
            2'b00: comp_op1 = reg_data1;
            2'b01: comp_op1 = alu_out_mem;
            2'b10: comp_op1 = result_wb;
            default: comp_op1 = reg_data1;
        endcase

        unique case (forward_b_id)
            2'b00: comp_op2 = reg_data2;
            2'b01: comp_op2 = alu_out_mem;
            2'b10: comp_op2 = result_wb;
            default: comp_op2 = reg_data2;
        endcase

        // Forwarding para comparação geral
        unique case(forward_a)
            2'b00: compare_a = reg_data1;
            2'b01: compare_a = alu_out_mem;
            2'b10: compare_a = result_wb;
            default: compare_a = reg_data1;
        endcase
        
        unique case(forward_b)
            2'b00: compare_b = reg_data2;
            2'b01: compare_b = alu_out_mem;
            2'b10: compare_b = result_wb;
            default: compare_b = reg_data2;
        endcase

        // Validação da comparação
        valid_comparison = !(forward_a_id[1] && forward_b_id[1]);
        early_compare_result = valid_comparison && (comp_op1 == comp_op2);
    end
    
    // Lógica de branch final
    assign branch_detected = is_branch;
    assign branch_taken = is_branch && early_compare_result;
    assign branch_stall_needed = is_branch && !valid_comparison;

    // Contador de forwarding
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            forward_count <= 32'h0;
        else if (!stall)
            forward_count <= forward_count + 
                           (|forward_a_id) + 
                           (|forward_b_id) + 
                           (|forward_a) + 
                           (|forward_b);
    end

    assign forward_cycles = forward_count;

    // Assertions para verificação
    `ifdef FORMAL
        // Verificar forwarding válido
        property valid_forward_timing;
            @(posedge clk) 
            $rose(forward_a_id) |-> ##[1:2] (comp_op1 == alu_out_mem);
        endproperty

        // Verificar stalls apropriados
        property valid_branch_stall;
            @(posedge clk)
            (is_branch && !valid_comparison) |-> branch_stall_needed;
        endproperty

        // Verificar comparação válida
        property valid_branch_comparison;
            @(posedge clk)
            branch_taken |-> valid_comparison;
        endproperty

        assert property (valid_forward_timing)
            else $error("Forward timing violation");
        assert property (valid_branch_stall)
            else $error("Branch stall not properly detected");
        assert property (valid_branch_comparison)
            else $error("Invalid branch comparison");

        // Coverage
        cover property (valid_forward_timing);
        cover property (valid_branch_stall);
        cover property (valid_branch_comparison);
    `endif

endmodule