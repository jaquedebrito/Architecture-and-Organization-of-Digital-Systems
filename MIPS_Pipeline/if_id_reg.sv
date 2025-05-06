module if_id_reg (
    // Sinais básicos
    input  logic        clk, reset,
    input  logic        flush,
    input  logic        clear,
    input  logic        stall,
    input  logic [31:0] pc_plus4_in,
    input  logic [31:0] instr_in,
    output logic [31:0] pc_plus4_out,
    output logic [31:0] instr_out,
    
    // Novas saídas para monitoramento
    output logic [31:0] stall_count,         // Contador de stalls
    output logic [31:0] flush_count,         // Contador de flushes
    output logic [31:0] clear_count,         // Contador de clears
    output logic [1:0]  reg_status,          // Status do registrador
    output logic        instr_valid,         // Validade da instrução
    output logic [63:0] last_update_time,    // Timestamp da última atualização
    output logic [31:0] bubble_count         // Contador de bolhas no pipeline
);
    // Definições de estado e timestamp
    typedef enum logic[1:0] {
        REG_NORMAL = 2'b00,
        REG_STALL  = 2'b01,
        REG_FLUSH  = 2'b10,
        REG_ERROR  = 2'b11
    } reg_state_t;

    // Sinais internos
    reg_state_t     current_state;
    logic [63:0]    current_time;
    logic [31:0]    consecutive_stalls;
    logic           is_bubble;
    logic [31:0]    last_valid_instr;

    // Inicialização do timestamp
    initial current_time = 64'd1711799796; // 2025-03-20 11:56:36

    // Verificação de instrução válida
    always_comb begin
        is_bubble = (instr_in == 32'h0) || (instr_in == 32'h4); // NOP instruction
        instr_valid = !$isunknown(instr_in) && !is_bubble;
    end

    // Registrador principal com monitoramento
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            // Reset de dados
            pc_plus4_out <= 32'b0;
            instr_out <= 32'b0;
            current_state <= REG_NORMAL;
            consecutive_stalls <= 32'h0;
            current_time <= 64'd1711799796; // 2025-03-20 11:56:36
            last_valid_instr <= 32'h0;
        end
        else if (clear || flush) begin
            // Clear/flush de dados
            pc_plus4_out <= 32'b0;
            instr_out <= 32'b0;
            current_state <= flush ? REG_FLUSH : REG_NORMAL;
            consecutive_stalls <= 32'h0;
            current_time <= current_time + 1;
        end
        else if (!stall) begin
            // Atualização normal
            pc_plus4_out <= pc_plus4_in;
            instr_out <= instr_in;
            current_state <= REG_NORMAL;
            consecutive_stalls <= 32'h0;
            current_time <= current_time + 1;
            
            if (instr_valid)
                last_valid_instr <= instr_in;
        end
        else begin
            // Durante stall
            current_state <= REG_STALL;
            consecutive_stalls <= consecutive_stalls + 1;
            current_time <= current_time + 1;
        end
    end

    // Contadores de performance
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            stall_count <= 32'h0;
            flush_count <= 32'h0;
            clear_count <= 32'h0;
            bubble_count <= 32'h0;
        end else begin
            if (stall)
                stall_count <= stall_count + 1;
            if (flush)
                flush_count <= flush_count + 1;
            if (clear)
                clear_count <= clear_count + 1;
            if (is_bubble && !stall)
                bubble_count <= bubble_count + 1;
        end
    end

    // Debug logging
    `ifdef DEBUG
        always @(posedge clk) begin
            if (!stall && instr_valid) begin
                $display("%s - IF/ID Register Update:", format_timestamp(current_time));
                $display("  User: jaquedebrito");
                $display("  PC+4: 0x%8h", pc_plus4_in);
                $display("  Instruction: 0x%8h", instr_in);
                if (consecutive_stalls > 5)
                    $display("  WARNING: High stall count: %d", consecutive_stalls);
            end
        end
        
        function string format_timestamp(input logic [63:0] unix_time);
            return $sformatf("2025-03-20 11:56:%02d", unix_time % 60);
        endfunction
    `endif

    // Status e timestamp
    assign reg_status = current_state;
    assign last_update_time = current_time;

    // Assertions para verificação
    `ifdef FORMAL
        // Verificar stalls excessivos
        property max_consecutive_stalls;
            @(posedge clk) disable iff (reset)
            consecutive_stalls <= 32'd10;
        endproperty

        // Verificar clear/flush mutuamente exclusivos
        property exclusive_clear_flush;
            @(posedge clk) disable iff (reset)
            !(clear && flush);
        endproperty

        // Verificar transição válida de dados
        property valid_data_transition;
            @(posedge clk) disable iff (reset)
            !stall && !clear && !flush |-> 
                ##1 (pc_plus4_out == $past(pc_plus4_in));
        endproperty

        // Verificar comportamento durante stall
        property valid_stall_behavior;
            @(posedge clk) disable iff (reset)
            stall |-> ##1 (pc_plus4_out == $past(pc_plus4_out));
        endproperty

        assert property (max_consecutive_stalls)
            else $error("Excessive consecutive stalls");
        assert property (exclusive_clear_flush)
            else $error("Clear and flush active simultaneously");
        assert property (valid_data_transition)
            else $error("Invalid data transition");
        assert property (valid_stall_behavior)
            else $error("Invalid stall behavior");

        // Coverage
        cover property (max_consecutive_stalls);
        cover property (exclusive_clear_flush);
        cover property (valid_data_transition);
        cover property (valid_stall_behavior);
    `endif

endmodule