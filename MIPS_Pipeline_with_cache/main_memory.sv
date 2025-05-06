module main_memory #(
    parameter MEM_SIZE = 65536   // 64KB de memória
)(
    input  logic        clk, reset,
    input  logic [31:0] addr,
    input  logic [31:0] write_data,
    output logic [31:0] read_data,
    input  logic        read,
    input  logic        write,
    output logic        ready
);
    // Memória RAM
    logic [7:0] ram[MEM_SIZE-1:0];
    
    // Contador para simular latência de acesso à memória
    logic [2:0] latency_counter;
    logic       operation_pending;
    logic [31:0] pending_addr;
    logic        pending_read, pending_write;
    
    // Simulação de latência de memória
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            latency_counter <= 0;
            operation_pending <= 0;
            pending_addr <= 0;
            pending_read <= 0;
            pending_write <= 0;
            ready <= 0;
            
            // Inicialização da memória com arquivo de programa
            $readmemh("memfile.dat", ram);
        end
        else begin
            if (!operation_pending && (read || write)) begin
                // Novo acesso à memória iniciado
                operation_pending <= 1;
                pending_addr <= addr;
                pending_read <= read;
                pending_write <= write;
                latency_counter <= 0;
                ready <= 0;
            end
            else if (operation_pending) begin
                if (latency_counter < 4) begin
                    // Simula latência de 5 ciclos para acesso à memória
                    latency_counter <= latency_counter + 1;
                    ready <= 0;
                end
                else begin
                    // Operação completa
                    if (pending_write) begin
                        // Escrita na memória (word-aligned)
                        ram[pending_addr]   <= write_data[7:0];
                        ram[pending_addr+1] <= write_data[15:8];
                        ram[pending_addr+2] <= write_data[23:16];
                        ram[pending_addr+3] <= write_data[31:24];
                    end
                    
                    if (pending_read) begin
                        // Leitura da memória (word-aligned)
                        read_data[7:0]   <= ram[pending_addr];
                        read_data[15:8]  <= ram[pending_addr+1];
                        read_data[23:16] <= ram[pending_addr+2];
                        read_data[31:24] <= ram[pending_addr+3];
                    end
                    
                    ready <= 1;
                    operation_pending <= 0;
                end
            end
            else begin
                ready <= 0;
            end
        end
    end
endmodule