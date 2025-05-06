module cache_monitor(
    input logic         clk, reset,
    input logic         i_read, d_read, d_write,
    input logic         i_hit, d_hit,
    input logic         i_ready, d_ready,
    
    // Estatísticas
    output logic [31:0] i_accesses,
    output logic [31:0] i_hits,
    output logic [31:0] d_reads,
    output logic [31:0] d_writes,
    output logic [31:0] d_read_hits,
    output logic [31:0] d_write_hits,
    output logic [31:0] total_stall_cycles
);
    // Contadores de acessos e hits
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            i_accesses <= 0;
            i_hits <= 0;
            d_reads <= 0;
            d_writes <= 0;
            d_read_hits <= 0;
            d_write_hits <= 0;
            total_stall_cycles <= 0;
        end else begin
            // Contagem de acessos à cache de instrução
            if (i_read) begin
                i_accesses <= i_accesses + 1;
                if (i_hit) i_hits <= i_hits + 1;
            end
            
            // Contagem de acessos à cache de dados
            if (d_read) begin
                d_reads <= d_reads + 1;
                if (d_hit) d_read_hits <= d_read_hits + 1;
            end
            
            if (d_write) begin
                d_writes <= d_writes + 1;
                if (d_hit) d_write_hits <= d_write_hits + 1;
            end
            
            // Ciclos de stall devido à cache
            if (!i_ready || !d_ready) begin
                total_stall_cycles <= total_stall_cycles + 1;
            end
        end
    end
    
    // Calcular taxa de hit ao final da simulação
    final begin
        $display("======= ESTATÍSTICAS DE CACHE =======");
        $display("Cache de Instruções:");
        $display("  Total de acessos: %0d", i_accesses);
        $display("  Total de hits: %0d", i_hits);
        $display("  Taxa de hit: %0.2f%%", 100.0 * i_hits / i_accesses);
        
        $display("Cache de Dados:");
        $display("  Total de leituras: %0d", d_reads);
        $display("  Hits em leituras: %0d", d_read_hits);
        $display("  Taxa de hit em leituras: %0.2f%%", 100.0 * d_read_hits / d_reads);
        
        $display("  Total de escritas: %0d", d_writes);
        $display("  Hits em escritas: %0d", d_write_hits);
        $display("  Taxa de hit em escritas: %0.2f%%", 100.0 * d_write_hits / d_writes);
        
        $display("Ciclos de stall devido à cache: %0d", total_stall_cycles);
        $display("====================================");
    end
endmodule