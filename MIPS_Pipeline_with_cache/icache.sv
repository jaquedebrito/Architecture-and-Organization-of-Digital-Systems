module icache #(
    parameter CACHE_SIZE = 1024,    // 1KB (em bytes)
    parameter BLOCK_SIZE = 4,       // 4 bytes por bloco (1 instrução MIPS)
    parameter ASSOCIATIVITY = 2     // 2-way set associative
)(
    input  logic        clk, reset,
    input  logic [31:0] addr,        // Endereço de instrução solicitado
    output logic [31:0] instr,       // Instrução retornada
    output logic        hit,         // Cache hit
    input  logic [31:0] mem_instr,   // Instrução da memória principal
    output logic [31:0] mem_addr,    // Endereço para memória principal
    output logic        mem_read     // Sinal de leitura para memória principal
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
    logic [ASSOCIATIVITY-1:0] lru_bits [NUM_SETS-1:0]; // LRU bits

    // Extração dos campos de endereço
    logic [TAG_BITS-1:0] addr_tag;
    logic [INDEX_BITS-1:0] addr_index;
    
    assign addr_tag = addr[31:INDEX_BITS+2];
    assign addr_index = addr[INDEX_BITS+1:2];

    // Sinais internos
    logic cache_hit;
    logic [ASSOCIATIVITY-1:0] hit_way;
    logic [ASSOCIATIVITY-1:0] replace_way;

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
        replace_way = ~lru_bits[addr_index];
    end
    
    // Leitura da cache
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            for (int i = 0; i < NUM_SETS; i++) begin
                for (int j = 0; j < ASSOCIATIVITY; j++) begin
                    valid_array[i][j] <= 0;
                end
                lru_bits[i] <= 0;
            end
            hit <= 0;
            instr <= 0;
            mem_read <= 0;
        end
        else begin
            hit <= cache_hit;
            
            if (cache_hit) begin
                // Cache hit: lê a instrução da cache
                for (int i = 0; i < ASSOCIATIVITY; i++) begin
                    if (hit_way[i]) begin
                        instr <= data_array[addr_index][i];
                        lru_bits[addr_index] <= i;  // Atualiza LRU
                    end
                end
                mem_read <= 0;
            end
            else begin
                // Cache miss: solicita leitura da memória principal
                mem_addr <= {addr[31:2], 2'b00};
                mem_read <= 1;
                
                // Na próxima borda de clock, atualiza a cache com dados da memória
                data_array[addr_index][replace_way] <= mem_instr;
                tag_array[addr_index][replace_way] <= addr_tag;
                valid_array[addr_index][replace_way] <= 1;
                lru_bits[addr_index] <= replace_way;
                
                instr <= mem_instr;  // Passa a instrução diretamente
            end
        end
    end
endmodule