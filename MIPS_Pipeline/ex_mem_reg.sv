module ex_mem_reg (
    // Sinais básicos
    input  logic        clk, reset,
    
    // Dados de entrada
    input  logic [31:0] ULAout_in,
    input  logic [31:0] write_data_in,
    input  logic        zero_in,
    input  logic [31:0] pc_branch_in,
    input  logic [4:0]  write_reg_in,
    
    // Sinais de controle de entrada
    input  logic        regwrite_in, memtoreg_in,
    input  logic        memwrite_in, memread_in,
    input  logic        branch_in,
    
    // Dados de saída
    output logic [31:0] ULAout_out,
    output logic [31:0] write_data_out,
    output logic        zero_out,
    output logic [31:0] pc_branch_out,
    output logic [4:0]  write_reg_out,
    
    // Sinais de controle de saída
    output logic        regwrite_out, memtoreg_out,
    output logic        memwrite_out, memread_out,
    output logic        branch_out,
    
    // Novas saídas para monitoramento
    output logic [31:0] transfer_count,      // Contador de transferências
    output logic [31:0] branch_count,        // Contador de branches
    output logic [31:0] mem_access_count,    // Contador de acessos à memória
    output logic [1:0]  reg_status,          // Status do registrador
    output logic        data_valid,          // Indicador de dados válidos
    output logic [63:0] last_update_time     // Timestamp da última atualização
);
    // Definições de estado e timestamp
    typedef enum logic[1:0] {
        REG_NORMAL = 2'b00,
        REG_HAZARD = 2'b01,
        REG_ERROR  = 2'b10,
        REG_IDLE   = 2'b11
    } reg_state_t;

    // Sinais internos
    reg_state_t  current_state;
    logic [63:0] current_time;
    logic        hazard_detected;
    logic [31:0] last_valid_ULAout;
    
    // Inicialização do timestamp
    initial current_time = 64'd1711799860; // 2025-03-20 11:57:40

    // Detecção de hazards e validação de dados
    always_comb begin
        hazard_detected = 1'b0;
        data_valid = 1'b1;

        // Verificar dados válidos
        if ($isunknown(ULAout_in) || $isunknown(write_data_in))
            data_valid = 1'b0;

        // Detectar hazards de memória
        if (memread_in && memwrite_in)
            hazard_detected = 1'b1;
    end

    // Registrador principal com proteção e monitoramento
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            // Reset de dados
            ULAout_out <= 32'b0;
            write_data_out <= 32'b0;
            zero_out <= 1'b0;
            pc_branch_out <= 32'b0;
            write_reg_out <= 5'b0;
            
            // Reset de controle
            regwrite_out <= 1'b0;
            memtoreg_out <= 1'b0;
            memwrite_out <= 1'b0;
            memread_out <= 1'b0;
            branch_out <= 1'b0;
            
            // Reset de estado
            current_state <= REG_IDLE;
            current_time <= 64'd1711799860; // 2025-03-20 11:57:40
            last_valid_ULAout <= 32'b0;
        end
        else begin
            // Atualização com verificação
            if (data_valid) begin
                ULAout_out <= ULAout_in;
                write_data_out <= write_data_in;
                zero_out <= zero_in;
                pc_branch_out <= pc_branch_in;
                write_reg_out <= write_reg_in;
                last_valid_ULAout <= ULAout_in;
                
                // Controle com proteção contra hazards
                regwrite_out <= regwrite_in && !hazard_detected;
                memtoreg_out <= memtoreg_in;
                memwrite_out <= memwrite_in && !hazard_detected;
                memread_out <= memread_in && !hazard_detected;
                branch_out <= branch_in;
                
                current_state <= hazard_detected ? REG_HAZARD : REG_NORMAL;
            end else begin
                current_state <= REG_ERROR;
            end
            
            current_time <= current_time + 1;
        end
    end

    // Contadores de performance
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            transfer_count <= 32'h0;
            branch_count <= 32'h0;
            mem_access_count <= 32'h0;
        end else if (data_valid) begin
            transfer_count <= transfer_count + 1;
            
            if (branch_in)
                branch_count <= branch_count + 1;
                
            if (memread_in || memwrite_in)
                mem_access_count <= mem_access_count + 1;
        end
    end

    // Debug logging
    `ifdef DEBUG
        always @(posedge clk) begin
            if (data_valid) begin
                $display("%s - EX/MEM Register Update:", format_timestamp(current_time));
                $display("  User: jaquedebrito");
                $display("  ALU Result: 0x%8h", ULAout_in);
                $display("  Write Data: 0x%8h", write_data_in);
                if (hazard_detected)
                    $display("  WARNING: Memory hazard detected!");
            end
        end
        
        function string format_timestamp(input logic [63:0] unix_time);
            return $sformatf("2025-03-20 11:57:%02d", unix_time % 60);
        endfunction
    `endif

    // Status e timestamp
    assign reg_status = current_state;
    assign last_update_time = current_time;

    // Assertions para verificação
    `ifdef FORMAL
        // Verificar dados válidos
        property valid_data_transfer;
            @(posedge clk) disable iff (reset)
            data_valid |-> !$isunknown(ULAout_out);
        endproperty

        // Verificar hazards de memória
        property valid_memory_access;
            @(posedge clk) disable iff (reset)
            !(memread_out && memwrite_out);
        endproperty

        // Verificar transições de estado válidas
        property valid_state_transition;
            @(posedge clk) disable iff (reset)
            $rose(hazard_detected) |-> ##1 (current_state == REG_HAZARD);
        endproperty

        assert property (valid_data_transfer)
            else $error("Invalid data transfer detected");
        assert property (valid_memory_access)
            else $error("Invalid memory access combination");
        assert property (valid_state_transition)
            else $error("Invalid state transition");

        // Coverage
        cover property (valid_data_transfer);
        cover property (valid_memory_access);
        cover property (valid_state_transition);
    `endif

endmodule