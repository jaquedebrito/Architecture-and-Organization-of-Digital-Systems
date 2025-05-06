module id_ex_reg (
    // Sinais básicos
    input  logic        clk, reset, flush,
    input  logic        stall,
    input  logic        clear,        // Sinal de clear
    input  logic        en,           // Enable
    // Entradas de dados
    input  logic [31:0] pc_plus4_in,
    input  logic [31:0] reg_data1_in, reg_data2_in,
    input  logic [31:0] signimm_in,
    input  logic [4:0]  rs_in, rt_in, rd_in,
    
    // Entradas de controle
    input  logic        regwrite_in, memtoreg_in,
    input  logic        memwrite_in, memread_in,
    input  logic        ULAsrc_in, regdst_in,
    input  logic [2:0]  ULAcontrol_in,
    input  logic        branch_in,
    
    // Saídas de dados
    output logic [31:0] instr_ex,
    output logic [31:0] pc_plus4_out,
    output logic [31:0] reg_data1_out, reg_data2_out,
    output logic [31:0] signimm_out,
    output logic [4:0]  rs_out, rt_out, rd_out,
    
    // Saídas de controle
    output logic        regwrite_out, memtoreg_out,
    output logic        memwrite_out, memread_out,
    output logic        ULAsrc_out, regdst_out,
    output logic [2:0]  ULAcontrol_out,
    output logic        branch_out,
    
    // Novas saídas para monitoramento
    output logic [31:0] stall_count,        // Contador de stalls
    output logic [31:0] flush_count,        // Contador de flushes
    output logic [1:0]  pipeline_status,    // Status do pipeline
    output logic        data_valid,         // Indicador de dados válidos
    output logic [63:0] last_update_time    // Timestamp da última atualização
);
    // Timestamp do sistema
    logic [63:0] current_time;
    initial current_time = 64'd1711799713; // 2025-03-20 11:55:13

    // Tipos e parâmetros
    typedef enum logic[1:0] {
        PIPE_NORMAL = 2'b00,
        PIPE_STALL  = 2'b01,
        PIPE_FLUSH  = 2'b10,
        PIPE_ERROR  = 2'b11
    } pipe_state_t;

    pipe_state_t current_state;
    logic        data_hazard_detected;
    logic [31:0] consecutive_stalls;

    // Verificação de dados válidos
    always_comb begin
        data_hazard_detected = 1'b0;
        data_valid = 1'b1;

        // Detectar hazards
        if (memread_out && ((rt_out == rs_in) || (rt_out == rt_in)))
            data_hazard_detected = 1'b1;

        // Verificar dados válidos
        if ($isunknown(reg_data1_in) || $isunknown(reg_data2_in))
            data_valid = 1'b0;
    end

    // Registrador principal com proteção e monitoramento
    always_ff @(posedge clk or posedge reset) begin
        if (reset || flush) begin
            // Reset de dados
            pc_plus4_out <= 32'b0;
            reg_data1_out <= 32'b0;
            reg_data2_out <= 32'b0;
            signimm_out <= 32'b0;
            rs_out <= 5'b0;
            rt_out <= 5'b0;
            rd_out <= 5'b0;
            
            // Reset de controle
            regwrite_out <= 1'b0;
            memtoreg_out <= 1'b0;
            memwrite_out <= 1'b0;
            memread_out <= 1'b0;
            ULAsrc_out <= 1'b0;
            regdst_out <= 1'b0;
            ULAcontrol_out <= 3'b0;
            branch_out <= 1'b0;
            
            // Reset de estado
            current_state <= PIPE_NORMAL;
            consecutive_stalls <= 32'h0;
            
            if (reset)
                current_time <= 64'd1711799713; // 2025-03-20 11:55:13
        end
        else if (!stall) begin
            // Atualização de dados com verificação
            pc_plus4_out <= pc_plus4_in;
            reg_data1_out <= data_valid ? reg_data1_in : 32'b0;
            reg_data2_out <= data_valid ? reg_data2_in : 32'b0;
            signimm_out <= signimm_in;
            rs_out <= rs_in;
            rt_out <= rt_in;
            rd_out <= rd_in;
            
            // Atualização de controle com proteção
            regwrite_out <= regwrite_in && data_valid;
            memtoreg_out <= memtoreg_in;
            memwrite_out <= memwrite_in && data_valid;
            memread_out <= memread_in;
            ULAsrc_out <= ULAsrc_in;
            regdst_out <= regdst_in;
            ULAcontrol_out <= ULAcontrol_in;
            branch_out <= branch_in && data_valid;
            
            // Atualização de estado
            current_state <= data_hazard_detected ? PIPE_STALL : PIPE_NORMAL;
            consecutive_stalls <= 32'h0;
            current_time <= current_time + 1;
        end
        else begin
            // Contagem de stalls consecutivos
            consecutive_stalls <= consecutive_stalls + 1;
            current_state <= PIPE_STALL;
            current_time <= current_time + 1;
        end
    end

    // Contadores de performance
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            stall_count <= 32'h0;
            flush_count <= 32'h0;
        end else begin
            if (stall)
                stall_count <= stall_count + 1;
            if (flush)
                flush_count <= flush_count + 1;
        end
    end

    // Debug logging
    `ifdef DEBUG
        always @(posedge clk) begin
            if (!stall && data_valid) begin
                $display("%s - ID/EX Register Update:", format_timestamp(current_time));
                $display("  User: jaquedebrito");
                $display("  PC+4: 0x%8h", pc_plus4_in);
                $display("  Registers: rs=%d, rt=%d, rd=%d", rs_in, rt_in, rd_in);
                if (data_hazard_detected)
                    $display("  WARNING: Data hazard detected!");
            end
        end
        
        function string format_timestamp(input logic [63:0] unix_time);
            return $sformatf("2025-03-20 11:55:%02d", unix_time % 60);
        endfunction
    `endif

    // Status e timestamp
    assign pipeline_status = current_state;
    assign last_update_time = current_time;

    // Assertions para verificação
    `ifdef FORMAL
        // Verificar stalls excessivos
        property max_consecutive_stalls;
            @(posedge clk) disable iff (reset)
            consecutive_stalls <= 32'd10;
        endproperty

        // Verificar dados válidos durante transferência
        property valid_data_transfer;
            @(posedge clk) disable iff (reset)
            !stall && !flush |-> data_valid;
        endproperty

        // Verificar reset/flush
        property valid_reset_flush;
            @(posedge clk)
            (reset || flush) |-> ##1 (regwrite_out == 1'b0);
        endproperty

        assert property (max_consecutive_stalls)
            else $error("Excessive consecutive stalls");
        assert property (valid_data_transfer)
            else $error("Invalid data transfer");
        assert property (valid_reset_flush)
            else $error("Invalid reset/flush behavior");

        // Coverage
        cover property (max_consecutive_stalls);
        cover property (valid_data_transfer);
        cover property (valid_reset_flush);
    `endif

endmodule