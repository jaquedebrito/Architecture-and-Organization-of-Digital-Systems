module dcache #(
    parameter CACHE_SIZE = 2048,    // 2KB (em bytes)
    parameter BLOCK_SIZE = 4,       // 4 bytes por bloco (1 palavra MIPS)
    parameter ASSOCIATIVITY = 2     // 2-way set associative
)(
    input  logic        clk, reset,
    input  logic [31:0] addr,        // Endereço de memória solicitado
    input  logic [31:0] write_data,  // Dados para escrita
    input  logic        read,        // Sinal de leitura
    input  logic        write,       // Sinal de escrita
    output logic [31:0] read_data,   // Dados lidos
    output logic        hit,         // Cache hit
    
    // Interface com memória principal
    input  logic [31:0] mem_read_data,  // Dados lidos da memória
    output logic [31:0] mem_addr,       // Endereço para memória principal
    output logic [31:0] mem_write_data, // Dados para escrita na memória
    output logic        mem_read,       // Sinal de leitura para memória
    output logic        mem_write       // Sinal de escrita para memória
);
    // Definição dos parâmetros da cache
    localparam NUM_BLOCKS = CACHE_SIZE / BLOCK_SIZE;
    localparam NUM_SETS = NUM_BLOCKS / ASSOCIATIVITY;
    localparam INDEX_BITS = $clog2(NUM_SETS);
    localparam TAG_BITS = 32 - INDEX_BITS - 2; // -2 devido ao byte offset

    // Estruturas da cache
    logic [TAG_BITS-1:0] tag_array [NUM_SETS-1:0][ASSOCIATIVITY-1:0];
    logic [31:0] data_array [NUM_SETS-1:0][ASSOCIATIVITY-1:0];
    logic valid_array [NUM_SETS-1:0][ASSOCIATIVITY-1:0];
    logic dirty_array [NUM_SETS-1:0][ASSOCIATIVITY-1:0];  // Bit "dirty" para write-back
    logic [ASSOCIATIVITY-1:0] lru_bits [NUM_SETS-1:0];    // LRU bits

    // Extração dos campos de endereço
    logic [TAG_BITS-1:0] addr_tag;
    logic [INDEX_BITS-1:0] addr_index;
    
    assign addr_tag = addr[31:INDEX_BITS+2];
    assign addr_index = addr[INDEX_BITS+1:2];

    // Sinais internos
    logic cache_hit;
    logic [ASSOCIATIVITY-1:0] hit_way;
    logic [ASSOCIATIVITY-1:0] replace_way;
    
    // Estados para máquina de estados
    typedef enum {IDLE, READ_MEM, WRITE_BACK} state_t;
    state_t state, next_state;

    // Lógica de hit
    always_comb begin
        cache_hit = 0;
        hit_way = 0;
        
        for (int i = 0; i < ASSOCIATIVITY; i++) begin
            if (valid_array[addr_index][i] && tag_array[addr_index][i] == addr_tag) begin
                cache_hit = 1;
                hit_way[i] = 1;
            end
        end
    end

    // Decisão de substituição (LRU simples)
    always_comb begin
        // Escolhe o bloco menos recentemente usado para substituição
        replace_way = ~lru_bits[addr_index];
    end
    
    // Máquina de estados para controle de cache
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            state <= IDLE;
        else
            state <= next_state;
    end
    
    always_comb begin
        next_state = state;
        
        case(state)
            IDLE: begin
                if ((read || write) && !cache_hit) begin
                    if (dirty_array[addr_index][replace_way])
                        next_state = WRITE_BACK;
                    else
                        next_state = READ_MEM;
                end
            end
            
            WRITE_BACK: begin
                // Após write-back, prossegue para leitura da memória
                next_state = READ_MEM;
            end
            
            READ_MEM: begin
                // Após leitura da memória, retorna para estado IDLE
                next_state = IDLE;
            end
        endcase
    end

    // Lógica de operação da cache
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            for (int i = 0; i < NUM_SETS; i++) begin
                for (int j = 0; j < ASSOCIATIVITY; j++) begin
                    valid_array[i][j] <= 0;
                    dirty_array[i][j] <= 0;
                end
                lru_bits[i] <= 0;
            end
            hit <= 0;
            read_data <= 0;
            mem_read <= 0;
            mem_write <= 0;
        end
        else begin
            case(state)
                IDLE: begin
                    hit <= cache_hit;
                    mem_read <= 0;
                    mem_write <= 0;
                    
                    if (read && cache_hit) begin
                        // Cache hit para leitura
                        for (int i = 0; i < ASSOCIATIVITY; i++) begin
                            if (hit_way[i]) begin
                                read_data <= data_array[addr_index][i];
                                lru_bits[addr_index] <= i;  // Atualiza LRU
                            end
                        end
                    end
                    else if (write && cache_hit) begin
                        // Cache hit para escrita (write-through)
                        for (int i = 0; i < ASSOCIATIVITY; i++) begin
                            if (hit_way[i]) begin
                                data_array[addr_index][i] <= write_data;
                                dirty_array[addr_index][i] <= 1;  // Marca como dirty
                                lru_bits[addr_index] <= i;  // Atualiza LRU
                            end
                        end
                        
                        // Implementação write-through (opcional)
                        // mem_addr <= {addr[31:2], 2'b00};
                        // mem_write_data <= write_data;
                        // mem_write <= 1;
                    end
                    else if ((read || write) && !cache_hit) begin
                        // Cache miss, preparação para acesso à memória
                        mem_addr <= {addr[31:2], 2'b00};
                    end
                end
                
                WRITE_BACK: begin
                    // Escreve bloco dirty na memória
                    mem_addr <= {tag_array[addr_index][replace_way], addr_index, 2'b00};
                    mem_write_data <= data_array[addr_index][replace_way];
                    mem_write <= 1;
                end
                
                READ_MEM: begin
                    // Lê novo bloco da memória
                    mem_addr <= {addr[31:2], 2'b00};
                    mem_read <= 1;
                    mem_write <= 0;
                    
                    // Atualiza cache com os dados lidos da memória
                    if (mem_read) begin
                        data_array[addr_index][replace_way] <= mem_read_data;
                        tag_array[addr_index][replace_way] <= addr_tag;
                        valid_array[addr_index][replace_way] <= 1;
                        dirty_array[addr_index][replace_way] <= 0;
                        lru_bits[addr_index] <= replace_way;
                        
                        if (read)
                            read_data <= mem_read_data;
                    end
                end
            endcase
            
            // Se for operação de escrita após leitura da memória
            if (state == READ_MEM && write && next_state == IDLE) begin
                data_array[addr_index][replace_way] <= write_data;
                dirty_array[addr_index][replace_way] <= 1;
            end
        end
    end
endmodule