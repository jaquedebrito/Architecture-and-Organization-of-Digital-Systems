module cache_controller(
    input  logic        clk, reset,
    
    // Interface com o processador (instruções)
    input  logic [31:0] i_addr,
    output logic [31:0] i_data,
    input  logic        i_read,
    output logic        i_ready,
    
    // Interface com o processador (dados)
    input  logic [31:0] d_addr,
    input  logic [31:0] d_write_data,
    output logic [31:0] d_read_data,
    input  logic        d_read,
    input  logic        d_write,
    output logic        d_ready,
    
    // Interface com a memória principal
    output logic [31:0] mem_addr,
    output logic [31:0] mem_write_data,
    input  logic [31:0] mem_read_data,
    output logic        mem_read,
    output logic        mem_write,
    input  logic        mem_ready
);
    // Sinais internos para arbitragem
    logic i_requesting, d_requesting;
    logic i_grant, d_grant;
    logic [31:0] i_mem_addr, d_mem_addr;
    logic [31:0] d_mem_write_data;
    logic i_mem_read, d_mem_read, d_mem_write;

    // Detecta requisições de cache
    assign i_requesting = i_read && !i_ready;
    assign d_requesting = (d_read || d_write) && !d_ready;

    // Arbitragem simples: prioridade para dados sobre instruções
    assign d_grant = d_requesting;
    assign i_grant = i_requesting && !d_requesting;

    // Multiplexação para acesso à memória
    always_comb begin
        if (d_grant) begin
            mem_addr = d_mem_addr;
            mem_write_data = d_mem_write_data;
            mem_read = d_mem_read;
            mem_write = d_mem_write;
        end else if (i_grant) begin
            mem_addr = i_mem_addr;
            mem_write_data = 32'h0;
            mem_read = i_mem_read;
            mem_write = 1'b0;
        end else begin
            mem_addr = 32'h0;
            mem_write_data = 32'h0;
            mem_read = 1'b0;
            mem_write = 1'b0;
        end
    end

    // Instância da cache de instruções
    icache #(
        .CACHE_SIZE(1024),
        .BLOCK_SIZE(4),
        .ASSOCIATIVITY(2)
    ) instr_cache (
        .clk(clk),
        .reset(reset),
        .addr(i_addr),
        .instr(i_data),
        .hit(i_ready),
        .mem_instr(mem_read_data),
        .mem_addr(i_mem_addr),
        .mem_read(i_mem_read)
    );

    // Instância da cache de dados
    dcache #(
        .CACHE_SIZE(2048),
        .BLOCK_SIZE(4),
        .ASSOCIATIVITY(2)
    ) data_cache (
        .clk(clk),
        .reset(reset),
        .addr(d_addr),
        .write_data(d_write_data),
        .read(d_read),
        .write(d_write),
        .read_data(d_read_data),
        .hit(d_ready),
        .mem_read_data(mem_read_data),
        .mem_addr(d_mem_addr),
        .mem_write_data(d_mem_write_data),
        .mem_read(d_mem_read),
        .mem_write(d_mem_write)
    );
endmodule