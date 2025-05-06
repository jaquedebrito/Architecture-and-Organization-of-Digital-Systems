// Aluna: Jaqueline Ferreira de Brito
// Memória de instruções do processador MIPS

/*
 * Módulo: instruction_memory
 * Função: Armazena e disponibiliza as instruções do programa para execução
 *
 * Características:
 * - Capacidade: 64 palavras de 32 bits (256 bytes)
 * - Tipo: ROM (apenas leitura durante a execução)
 * - Acesso: assíncrono (combinacional)
 * - Inicialização: carregada a partir do arquivo "memfile.dat"
 *
 * No contexto do MIPS:
 * - Os endereços são divididos por 4, pois cada instrução ocupa 4 bytes
 * - Para acessar a instrução no endereço físico 0x10, usa-se o índice 4 (0x10/4)
 */

module instruction_memory (
    // Sinais básicos
    input  logic [5:0]  addr,          // PC/4 (índice na memória)
    output logic [31:0] instr,         // Instrução lida
    
    // Novas saídas para monitoramento
    output logic [31:0] fetch_count,   // Contador de fetches
    output logic [31:0] error_count,   // Contador de erros de acesso
    output logic [1:0]  mem_status,    // Status da memória
    output logic        load_success,   // Status do carregamento do arquivo
    output logic [63:0] last_access_time // Timestamp do último acesso
);
    // Memória principal
    logic [31:0] RAM[63:0];           // Memória principal
    
    // Definições de estado
    typedef enum logic[1:0] {
        MEM_IDLE    = 2'b00,
        MEM_FETCH   = 2'b01,
        MEM_ERROR   = 2'b10,
        MEM_LOADING = 2'b11
    } mem_state_t;

    // Sinais internos
    mem_state_t  current_state;
    logic [63:0] current_time;
    logic        access_error;
    logic [31:0] instr_count;
    
    // Inicialização do timestamp
    initial current_time = 64'd1711800183; // 2025-03-20 12:03:03

    // Verificação de arquivo e carregamento
    initial begin
        // Reset inicial
        current_state = MEM_LOADING;
        load_success = 1'b0;
        instr_count = 32'h0;
        access_error = 1'b0;
        
        // Verificar existência do arquivo
        if (!$fopen("memfile.dat", "r")) begin
            $display("%s - ERROR: memfile.dat not found!", format_timestamp(current_time));
            $display("  User: jaquedebrito");
            current_state = MEM_ERROR;
            access_error = 1'b1;
        end else begin
            // Carregar arquivo
            $readmemh("memfile.dat", RAM);
            load_success = 1'b1;
            current_state = MEM_IDLE;
            
            // Log de carregamento bem-sucedido
            $display("%s - Memory Initialization:", format_timestamp(current_time));
            $display("  User: jaquedebrito");
            $display("  Status: Instructions loaded successfully");
        end
    end

    // Verificação de acesso válido
    always_comb begin
        access_error = 1'b0;
        
        // Verificar endereço válido
        if (addr >= 64)  // Limite fixo de 64 palavras
            access_error = 1'b1;
            
        // Verificar dados válidos
        if ($isunknown(RAM[addr]))
            access_error = 1'b1;
    end

    // Lógica de fetch simples e direta
    always_comb begin
        if (!access_error) begin
            instr = RAM[addr];
            current_state = MEM_FETCH;
        end else begin
            instr = 32'h0;  // NOP em caso de erro
            current_state = MEM_ERROR;
        end
    end

    // Contadores de performance e timestamp
    always @(addr) begin
        if (!access_error) begin
            fetch_count = fetch_count + 1;
            current_time = current_time + 1;
            last_access_time = current_time;
        end else begin
            error_count = error_count + 1;
        end
    end

    // Debug logging
    `ifdef DEBUG
        always @(addr) begin
            if (!access_error) begin
                $display("%s - Instruction Fetch:", format_timestamp(current_time));
                $display("  User: jaquedebrito");
                $display("  Address: 0x%h", addr);
                $display("  Instruction: 0x%h", instr);
            end
        end
        
        function string format_timestamp(input logic [63:0] unix_time);
            return $sformatf("2025-03-20 12:03:%02d", unix_time % 60);
        endfunction
    `endif

    // Status
    assign mem_status = current_state;

    // Assertions para verificação
    `ifdef FORMAL
        // Verificar acesso válido
        property valid_access;
            @(addr) 
            addr < 64 |-> !access_error;
        endproperty

        // Verificar dados válidos
        property valid_instruction;
            @(addr) 
            !access_error |-> !$isunknown(instr);
        endproperty

        assert property (valid_access)
            else $error("Invalid memory access");
        assert property (valid_instruction)
            else $error("Invalid instruction data");

        // Coverage
        cover property (valid_access);
        cover property (valid_instruction);
    `endif

endmodule