module wb_stage (
    // Sinais básicos
    input  logic        clk, reset,          // Adicionados para monitoramento
    input  logic [31:0] readdata,
    input  logic [31:0] ULAout,
    input  logic        memtoreg,
    
    // Saídas principais
    output logic [31:0] result,
    
    // Novas saídas para monitoramento e debug
    output logic [31:0] wb_cycles,          // Contador de escritas
    output logic [31:0] mem_reads,          // Contador de leituras da memória
    output logic [31:0] alu_uses,           // Contador de usos da ALU
    output logic        wb_valid,           // Indicador de writeback válido
    output logic [63:0] timestamp,          // Timestamp da operação
    output logic [31:0] last_values         // Buffer circular dos últimos valores
);
    // Sinais internos
    logic [31:0] result_pre;
    logic        valid_data;
    logic [1:0]  value_index;
    
    // Timestamp do sistema
    logic [63:0] current_time;
    initial current_time = 64'd1711799553; // 2025-03-20 11:52:33 em Unix timestamp

    // Mux para seleção do resultado com verificação
    mux2 #(32) resmux(
        .d0(ULAout),
        .d1(readdata),
        .s(memtoreg),
        .y(result_pre)
    );

    // Verificação de dados válidos
    always_comb begin
        valid_data = 1'b1;
        
        // Verificar valores não-indefinidos
        if ($isunknown(result_pre))
            valid_data = 1'b0;
            
        // Verificar range válido para instruções específicas
        if (memtoreg && $isunknown(readdata))
            valid_data = 1'b0;
    end

    // Registro circular dos últimos valores
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            for (int i = 0; i < 4; i++)
                last_values[i] <= 32'h0;
            value_index <= 2'b00;
        end else if (valid_data) begin
            last_values[value_index] <= result_pre;
            value_index <= value_index + 1;
        end
    end

    // Contadores de performance
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            wb_cycles <= 32'h0;
            mem_reads <= 32'h0;
            alu_uses <= 32'h0;
            current_time <= 64'd1711799553; // 2025-03-20 11:52:33
        end else begin
            wb_cycles <= wb_cycles + 1;
            
            if (memtoreg && valid_data)
                mem_reads <= mem_reads + 1;
            else if (!memtoreg && valid_data)
                alu_uses <= alu_uses + 1;
                
            current_time <= current_time + 1; // Incrementa timestamp
        end
    end

    // Log de operações (simulação apenas)
    `ifdef SIMULATION
        always @(posedge clk) begin
            if (valid_data) begin
                $display("%s - WB Stage Operation:", format_timestamp(current_time));
                $display("  User: jaquedebrito");
                $display("  Operation: %s", memtoreg ? "Memory Read" : "ALU Result");
                $display("  Value: 0x%8h", result_pre);
            end
        end
        
        // Função para formatação do timestamp
        function string format_timestamp(input logic [63:0] unix_time);
            // Implementação básica para exemplo
            return $sformatf("2025-03-20 11:52:%02d", unix_time % 60);
        endfunction
    `endif

    // Atribuições finais
    assign result = valid_data ? result_pre : 32'h0;
    assign wb_valid = valid_data;
    assign timestamp = current_time;

    // Assertions para verificação
    `ifdef FORMAL
        // Verificar dados válidos
        property valid_result;
            @(posedge clk) disable iff (reset)
            wb_valid |-> !$isunknown(result);
        endproperty

        // Verificar contadores
        property valid_counters;
            @(posedge clk) disable iff (reset)
            wb_cycles > 0 |-> (mem_reads + alu_uses) <= wb_cycles;
        endproperty

        // Verificar buffer circular
        property valid_buffer;
            @(posedge clk) disable iff (reset)
            wb_valid |-> ##1 (last_values[value_index] == $past(result));
        endproperty

        assert property (valid_result)
            else $error("Invalid result detected");
        assert property (valid_counters)
            else $error("Invalid counter values");
        assert property (valid_buffer)
            else $error("Invalid buffer operation");

        // Coverage
        cover property (valid_result);
        cover property (valid_counters);
        cover property (valid_buffer);
    `endif

endmodule