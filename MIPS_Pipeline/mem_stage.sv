module mem_stage (
    // Clock e Reset
    input  logic        clk,
    input  logic        reset,
    
    // Sinais de branch
    input  logic        branch, zero,
    output logic        pcsrc,
    
    // Sinais de memória
    input  logic        memwrite, memread,
    input  logic [31:0] alu_result,
    input  logic [31:0] write_data,
    output logic [31:0] read_data,
    
    // Novas saídas para monitoramento
    output logic [31:0] mem_access_count,    // Contador de acessos à memória
    output logic [31:0] branch_taken_count,  // Contador de branches tomados
    output logic [31:0] mem_latency,         // Latência média de memória
    output logic        mem_busy,            // Indicador de memória ocupada
    output logic [1:0]  mem_status,          // Status da operação de memória
    output logic [63:0] last_access_time     // Timestamp do último acesso
);
    // Tipos e parâmetros
    typedef enum logic[1:0] {
        MEM_IDLE    = 2'b00,
        MEM_READ    = 2'b01,
        MEM_WRITE   = 2'b10,
        MEM_ERROR   = 2'b11
    } mem_state_t;

    // Sinais internos
    logic [31:0] access_latency;
    logic [31:0] total_latency;
    logic [31:0] access_count;
    logic        mem_violation;
    logic [63:0] current_time;
    mem_state_t  current_state;

    // Proteção de memória
    logic        is_valid_address;
    logic        is_aligned;
    logic        is_protected_region;

    // Verificações de endereço
    assign is_valid_address = (alu_result < 32'h10000000);  // Exemplo de limite
    assign is_aligned = (alu_result[1:0] == 2'b00);         // Alinhamento em word
    assign is_protected_region = (alu_result >= 32'h1000 && alu_result < 32'h2000);

    // Timestamp do sistema
    initial current_time = 64'd1711799625; // 2025-03-20 11:53:45

    // Lógica de branch melhorada
    always_comb begin
        pcsrc = branch & zero;
        if (branch && !is_valid_address)
            pcsrc = 1'b0;  // Previne branches para endereços inválidos
    end

    // Máquina de estados da memória
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            current_state <= MEM_IDLE;
            mem_busy <= 1'b0;
            access_latency <= 32'h0;
        end else begin
            case (current_state)
                MEM_IDLE: begin
                    if (memread && !mem_violation)
                        current_state <= MEM_READ;
                    else if (memwrite && !mem_violation)
                        current_state <= MEM_WRITE;
                    access_latency <= 32'h0;
                end
                
                MEM_READ, MEM_WRITE: begin
                    if (access_latency >= 3) begin  // Exemplo: 3 ciclos de latência
                        current_state <= MEM_IDLE;
                        mem_busy <= 1'b0;
                    end else begin
                        access_latency <= access_latency + 1;
                        mem_busy <= 1'b1;
                    end
                end
                
                MEM_ERROR: begin
                    current_state <= MEM_IDLE;
                    mem_busy <= 1'b0;
                end
            endcase
        end
    end

    // Interface com memória de dados com proteção
    data_memory dmem (
        .clk(clk),
        .reset(reset),                      
        .we(memwrite),
        .re(memread),
        .addr(alu_result[7:2]),      
        .wd(write_data),            
        .rd(read_data), 
        .read_count(memory_access_count),   
        .write_count(memory_access_count),  
        .error_count(hazard_count),         
        .mem_status(pipeline_status),       
        .access_valid(1'b1),                
        .last_access_time(last_update_time), 
        .last_addr_accessed(addr)           
    );

    // Verificação de violações de memória
    always_comb begin
        mem_violation = 1'b0;
        
        if (!is_valid_address || !is_aligned)
            mem_violation = 1'b1;
        
        if (is_protected_region && memwrite)
            mem_violation = 1'b1;
    end

    // Contadores de performance e monitoramento
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            mem_access_count <= 32'h0;
            branch_taken_count <= 32'h0;
            total_latency <= 32'h0;
            current_time <= 64'd1711799625; // 2025-03-20 11:53:45
        end else begin
            current_time <= current_time + 1;
            
            if (memread || memwrite)
                mem_access_count <= mem_access_count + 1;
                
            if (pcsrc)
                branch_taken_count <= branch_taken_count + 1;
                
            if (mem_busy)
                total_latency <= total_latency + 1;
        end
    end

    // Cálculo de latência média
    assign mem_latency = (mem_access_count > 0) ? 
                        (total_latency / mem_access_count) : 32'h0;

    // Status e timestamp
    assign mem_status = current_state;
    assign last_access_time = current_time;

    // Log de operações
    `ifdef DEBUG
        always @(posedge clk) begin
            if (memread || memwrite) begin
                $display("%s - Memory Operation:", format_timestamp(current_time));
                $display("  User: jaquedebrito");
                $display("  Operation: %s", memread ? "Read" : "Write");
                $display("  Address: 0x%8h", alu_result);
                if (mem_violation)
                    $display("  WARNING: Memory violation detected!");
            end
        end
        
        function string format_timestamp(input logic [63:0] unix_time);
            return $sformatf("2025-03-20 11:53:%02d", unix_time % 60);
        endfunction
    `endif

    // Assertions para verificação
    `ifdef FORMAL
        // Verificar acesso válido à memória
        property valid_mem_access;
            @(posedge clk) disable iff (reset)
            (memread || memwrite) |-> is_valid_address && is_aligned;
        endproperty

        // Verificar proteção de memória
        property protected_mem_access;
            @(posedge clk) disable iff (reset)
            (memwrite && is_protected_region) |-> mem_violation;
        endproperty

        // Verificar latência máxima
        property max_latency;
            @(posedge clk) disable iff (reset)
            mem_busy |-> (access_latency <= 32'd10);
        endproperty

        assert property (valid_mem_access)
            else $error("Invalid memory access detected");
        assert property (protected_mem_access)
            else $error("Protected memory violation");
        assert property (max_latency)
            else $error("Excessive memory latency");

        // Coverage
        cover property (valid_mem_access);
        cover property (protected_mem_access);
        cover property (max_latency);
    `endif

endmodule