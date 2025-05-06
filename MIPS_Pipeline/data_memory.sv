module data_memory (
    // Sinais básicos
    input  logic        clk,
    input  logic        reset,              // Novo: reset síncrono
    input  logic        we,                 // Write enable
    input  logic        re,                 // Read enable
    input  logic [5:0]  addr,              // Endereço
    input  logic [31:0] wd,                // Write data
    output logic [31:0] rd,                // Read data
    
    // Novas saídas para monitoramento
    output logic [31:0] read_count,        // Contador de leituras
    output logic [31:0] write_count,       // Contador de escritas
    output logic [31:0] error_count,       // Contador de erros
    output logic [1:0]  mem_status,        // Status da memória
    output logic        access_valid,      // Indicador de acesso válido
    output logic [63:0] last_access_time,  // Timestamp do último acesso
    output logic [5:0]  last_addr_accessed // Último endereço acessado
);
    // Memória principal
    logic [31:0] RAM[63:0];
    
    // Definições de estado
    typedef enum logic[1:0] {
        MEM_IDLE    = 2'b00,
        MEM_READ    = 2'b01,
        MEM_WRITE   = 2'b10,
        MEM_ERROR   = 2'b11
    } mem_state_t;

    // Sinais internos
    mem_state_t  current_state;
    logic [63:0] current_time;
    logic        access_error;
    logic [31:0] error_data;
    logic [5:0]  protected_start = 6'd0;   // Início da região protegida
    logic [5:0]  protected_end   = 6'd16;  // Fim da região protegida

    // Inicialização do timestamp
    initial current_time = 64'd1711799994; // 2025-03-20 11:59:54

    // Verificação de acesso válido
    always_comb begin
        access_error = 1'b0;
        
        // Verificar acesso simultâneo
        if (we && re)
            access_error = 1'b1;
            
        // Verificar região protegida
        if (we && (addr >= protected_start && addr <= protected_end))
            access_error = 1'b1;
            
        // Verificar dados válidos
        if (we && $isunknown(wd))
            access_error = 1'b1;
    end

    // Leitura com proteção
    always_comb begin
        rd = 32'h0;
        if (re && !access_error) begin
            rd = RAM[addr];
            if ($isunknown(rd))
                rd = 32'h0;
        end
    end

    // Escrita com proteção e monitoramento
    always_ff @(posedge clk) begin
        if (reset) begin
            // Inicialização da memória
            for (int i = 0; i < 64; i++)
                RAM[i] <= 32'h0;
                
            // Valores iniciais para teste
            RAM[20] <= 32'h00000005;
            RAM[21] <= 32'h0000000c;
            
            // Reset de estado
            current_state <= MEM_IDLE;
            current_time <= 64'd1711799994; // 2025-03-20 11:59:54
        end
        else begin
            current_time <= current_time + 1;
            
            if (we && !access_error) begin
                RAM[addr] <= wd;
                current_state <= MEM_WRITE;
                last_addr_accessed <= addr;
            end
            else if (re && !access_error) begin
                current_state <= MEM_READ;
                last_addr_accessed <= addr;
            end
            else if (access_error) begin
                current_state <= MEM_ERROR;
            end
            else begin
                current_state <= MEM_IDLE;
            end
        end
    end

    // Contadores de performance
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            read_count <= 32'h0;
            write_count <= 32'h0;
            error_count <= 32'h0;
        end
        else begin
            if (re && !access_error)
                read_count <= read_count + 1;
            if (we && !access_error)
                write_count <= write_count + 1;
            if (access_error)
                error_count <= error_count + 1;
        end
    end

    // Debug logging
    `ifdef DEBUG
        always @(posedge clk) begin
            if (we || re) begin
                $display("%s - Memory Access:", format_timestamp(current_time));
                $display("  User: jaquedebrito");
                $display("  Operation: %s", we ? "Write" : "Read");
                $display("  Address: 0x%h", addr);
                if (we) $display("  Write Data: 0x%h", wd);
                if (re) $display("  Read Data: 0x%h", rd);
                if (access_error)
                    $display("  WARNING: Memory access error!");
            end
        end
        
        function string format_timestamp(input logic [63:0] unix_time);
            return $sformatf("2025-03-20 11:59:%02d", unix_time % 60);
        endfunction
    `endif

    // Atribuições de saída
    assign mem_status = current_state;
    assign access_valid = !access_error;
    assign last_access_time = current_time;

    // Assertions para verificação
    `ifdef FORMAL
        // Verificar acesso válido
        property valid_access;
            @(posedge clk) disable iff (reset)
            (we || re) |-> !access_error;
        endproperty

        // Verificar proteção de memória
        property protected_region;
            @(posedge clk) disable iff (reset)
            we && (addr >= protected_start && addr <= protected_end) |-> ##1 (current_state == MEM_ERROR);
        endproperty

        // Verificar dados estáveis
        property stable_data;
            @(posedge clk) disable iff (reset)
            we |=> $stable(RAM[addr]);
        endproperty

        assert property (valid_access)
            else $error("Invalid memory access");
        assert property (protected_region)
            else $error("Protected memory violation");
        assert property (stable_data)
            else $error("Unstable memory data");

        // Coverage
        cover property (valid_access);
        cover property (protected_region);
        cover property (stable_data);
    `endif

endmodule