module ex_stage(
    // Clock e Reset
    input  logic        clk, reset,
    
    // Dados de entrada
    input  logic [31:0] pc_plus4,
    input  logic [31:0] reg_data1, reg_data2,
    input  logic [31:0] signimm,
    input  logic [4:0]  rt, rd,
    
    // Sinais de controle
    input  logic        ULAsrc, regdst,
    input  logic [2:0]  ULAcontrol,
    
    // Sinais de forwarding
    input  logic [1:0]  forward_a, forward_b,
    input  logic [31:0] ULAout_mem, result_wb,
    
    // Saídas principais
    output logic [31:0] ULAout,
    output logic        zero,
    output logic [31:0] pc_branch,
    output logic [31:0] write_data,
    output logic [4:0]  write_reg,
    output logic        alu_ready,
    
    // Novas saídas para monitoramento e debug
    output logic [31:0] forward_count,     // Contador de forwards realizados
    output logic        alu_overflow,      // Indicador de overflow
    output logic [1:0]  hazard_type,      // Tipo de hazard detectado
    output logic [31:0] execution_cycles   // Contador de ciclos de execução
);
    // Sinais internos atualizados
    logic [31:0] signimmsh;
    logic [31:0] ULA_srca, ULA_srcb, ULA_srcb_pre;
    logic        forward_occurred;
    logic        alu_valid;
    logic [31:0] cycle_counter;
    logic [31:0] op_count[8];         // Adicionar para corresponder à ULA
    logic [31:0] overflow_count;      // Adicionar para corresponder à ULA
    logic [31:0] error_count;         // Adicionar para corresponder à ULA
    logic [63:0] last_op_time;        // Adicionar para corresponder à ULA
    logic [1:0]  ula_status;          // Já existe
    // Detecção de forwarding ativo
    assign forward_occurred = (|forward_a) || (|forward_b);

    // Deslocamento do imediato com verificação de overflow
    sl2 immsh(
        .a(signimm),
        .y(signimmsh)
    );

    // Cálculo do endereço de branch com validação
    adder pcadd(
        .a(pc_plus4),
        .b(signimmsh),
        .y(pc_branch)
    );

    // Lógica de forwarding otimizada
    mux3 #(32) forwardamux(
        .d0(reg_data1),
        .d1(result_wb),
        .d2(ULAout_mem),
        .s(forward_a),
        .y(ULA_srca)
    );

    mux3 #(32) forwardbmux(
        .d0(reg_data2),
        .d1(result_wb),
        .d2(ULAout_mem),
        .s(forward_b),
        .y(ULA_srcb_pre)
    );

    // Seleção do segundo operando da ULA com verificação
    mux2 #(32) srcbmux(
        .d0(ULA_srcb_pre),
        .d1(signimm),
        .s(ULAsrc),
        .y(ULA_srcb)
    );

    // ULA com detecção de overflow
    ula the_ula(
        .a(ULA_srca),
        .b(ULA_srcb),
        .ULAcontrol(ULAcontrol),
        .result(ULAout),
        .zero(zero),
        // Sinais de monitoramento
        .op_count(op_count),           // Conectar ao array de contadores
        .overflow_count(overflow_count), // Conectar ao contador de overflow
        .error_count(error_count),      // Conectar ao contador de erros
        .ula_status(ula_status),        // Já estava conectado
        .last_op_time(last_op_time)     // Conectar ao timestamp

    );

    // Seleção do registrador destino com validação
    mux2 #(5) wrmux(
        .d0(rt),
        .d1(rd),
        .s(regdst),
        .y(write_reg)
    );

    // Contadores de performance e monitoramento
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            cycle_counter <= 32'h0;
            forward_count <= 32'h0;
        end else begin
            cycle_counter <= cycle_counter + 1;
            if (forward_occurred)
                forward_count <= forward_count + 1;
        end
    end

    // Lógica de hazard detection
        // Lógica de hazard detection atualizada
    always_comb begin
        hazard_type = 2'b00; // No hazard
        if (forward_occurred)
            hazard_type = 2'b01; // RAW hazard
        if (ula_status == 2'b01)  // ULA_OVERFLOW
            hazard_type = 2'b10; // Overflow hazard
    end

    // Atualizar a lógica de validação
    always_comb begin
        alu_valid = 1'b1;
        
        // Verificar condições que invalidam a operação
        if (ula_status == 2'b01 || ula_status == 2'b10) // ULA_OVERFLOW ou ULA_ERROR
            alu_valid = 1'b0;
        if (ULAcontrol == 3'b111 && error_count > 0) // Operação inválida detectada
            alu_valid = 1'b0;
    end

    // Atribuir a saída de overflow
    assign alu_overflow = (ula_status == 2'b01); // TRUE quando ULA_OVERFLOW

    // Atribuições finais
    assign alu_ready = alu_valid;
    assign execution_cycles = cycle_counter;
    assign write_data = ULA_srcb_pre;

    // Assertions para verificação
    `ifdef FORMAL
        // Verificar forwarding válido
        property valid_forward_mux;
            @(posedge clk)
            forward_occurred |-> (!$isunknown(ULA_srca) && !$isunknown(ULA_srcb));
        endproperty

        // Verificar operação válida da ULA
        property valid_ula_operation;
            @(posedge clk)
            alu_ready |-> !alu_overflow;
        endproperty

        // Verificar escrita válida
        property valid_write_reg;
            @(posedge clk)
            regdst |-> write_reg == rd;
        endproperty

        assert property (valid_forward_mux)
            else $error("Invalid forward mux values");
        assert property (valid_ula_operation)
            else $error("Invalid ULA operation");
        assert property (valid_write_reg)
            else $error("Invalid write register selection");

        // Coverage
        cover property (valid_forward_mux);
        cover property (valid_ula_operation);
        cover property (valid_write_reg);
    `endif

endmodule