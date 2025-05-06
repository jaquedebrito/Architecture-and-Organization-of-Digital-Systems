module mem_wb_reg (
    // Sinais básicos
    input  logic        clk, reset,
    
    // Dados de entrada
    input  logic [31:0] readdata_in,
    input  logic [31:0] ULAout_in,
    input  logic [4:0]  write_reg_in,
    
    // Sinais de controle de entrada
    input  logic        regwrite_in, memtoreg_in,
    
    // Dados de saída
    output logic [31:0] readdata_out,
    output logic [31:0] ULAout_out,
    output logic [4:0]  write_reg_out,
    
    // Sinais de controle de saída
    output logic        regwrite_out, memtoreg_out,
    
    // Novas saídas para monitoramento
    output logic [31:0] wb_count,           // Contador de writebacks
    output logic [31:0] mem_read_count,     // Contador de leituras de memória
    output logic [31:0] alu_result_count,   // Contador de resultados da ALU
    output logic [1:0]  reg_status,         // Status do registrador
    output logic        data_valid,         // Indicador de dados válidos
    output logic [63:0] last_update_time    // Timestamp da última atualização
);
    // Definições de estado e timestamp
    typedef enum logic[1:0] {
        REG_NORMAL = 2'b00,
        REG_MEM_READ = 2'b01,
        REG_ALU_RESULT = 2'b10,
        REG_ERROR = 2'b11
    } reg_state_t;

    // Sinais internos
    reg_state_t  current_state;
    logic [63:0] current_time;
    logic        valid_data;
    logic [31:0] last_valid_data;
    
    // Inicialização do timestamp
    initial current_time = 64'd1711799935; // 2025-03-20 11:58:55

    // Verificação de dados válidos
    always_comb begin
        valid_data = 1'b1;
        
        // Verificar valores indefinidos
        if (memtoreg_in && $isunknown(readdata_in))
            valid_data = 1'b0;
        if (!memtoreg_in && $isunknown(ULAout_in))
            valid_data = 1'b0;
        if ($isunknown(write_reg_in))
            valid_data = 1'b0;
    end

    // Registrador principal com proteção e monitoramento
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            // Reset de dados
            readdata_out <= 32'b0;
            ULAout_out <= 32'b0;
            write_reg_out <= 5'b0;
            
            // Reset de controle
            regwrite_out <= 1'b0;
            memtoreg_out <= 1'b0;
            
            // Reset de estado
            current_state <= REG_NORMAL;
            current_time <= 64'd1711799935; // 2025-03-20 11:58:55
            last_valid_data <= 32'b0;
        end
        else begin
            if (valid_data) begin
                // Atualização de dados
                readdata_out <= readdata_in;
                ULAout_out <= ULAout_in;
                write_reg_out <= write_reg_in;
                
                // Atualização de controle
                regwrite_out <= regwrite_in;
                memtoreg_out <= memtoreg_in;
                
                // Atualização de estado
                current_state <= memtoreg_in ? REG_MEM_READ : REG_ALU_RESULT;
                last_valid_data <= memtoreg_in ? readdata_in : ULAout_in;
            end else begin
                current_state <= REG_ERROR;
            end
            
            current_time <= current_time + 1;
        end
    end

    // Contadores de performance
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            wb_count <= 32'h0;
            mem_read_count <= 32'h0;
            alu_result_count <= 32'h0;
        end else if (valid_data && regwrite_in) begin
            wb_count <= wb_count + 1;
            
            if (memtoreg_in)
                mem_read_count <= mem_read_count + 1;
            else
                alu_result_count <= alu_result_count + 1;
        end
    end

    // Debug logging
    `ifdef DEBUG
        always @(posedge clk) begin
            if (valid_data && regwrite_in) begin
                $display("%s - MEM/WB Register Update:", format_timestamp(current_time));
                $display("  User: jaquedebrito");
                $display("  Write Register: %d", write_reg_in);
                $display("  Data Source: %s", memtoreg_in ? "Memory" : "ALU");
                $display("  Value: 0x%8h", memtoreg_in ? readdata_in : ULAout_in);
            end
        end
        
        function string format_timestamp(input logic [63:0] unix_time);
            return $sformatf("2025-03-20 11:58:%02d", unix_time % 60);
        endfunction
    `endif

    // Status e timestamp
    assign reg_status = current_state;
    assign data_valid = valid_data;
    assign last_update_time = current_time;

    // Assertions para verificação
    `ifdef FORMAL
        // Verificar dados válidos durante writeback
        property valid_wb_data;
            @(posedge clk) disable iff (reset)
            regwrite_out |-> !$isunknown(memtoreg_out ? readdata_out : ULAout_out);
        endproperty

        // Verificar registro destino válido
        property valid_write_reg;
            @(posedge clk) disable iff (reset)
            regwrite_out |-> (write_reg_out != 5'b0);
        endproperty

        // Verificar transições de estado válidas
        property valid_state_transition;
            @(posedge clk) disable iff (reset)
            valid_data |-> ##1 (current_state != REG_ERROR);
        endproperty

        assert property (valid_wb_data)
            else $error("Invalid writeback data");
        assert property (valid_write_reg)
            else $error("Invalid write register");
        assert property (valid_state_transition)
            else $error("Invalid state transition");

        // Coverage
        cover property (valid_wb_data);
        cover property (valid_write_reg);
        cover property (valid_state_transition);
    `endif

endmodule