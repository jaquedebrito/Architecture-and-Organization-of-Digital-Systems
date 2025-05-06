module multicycle_alu(
    input  logic        clk, reset,
    input  logic [31:0] a, b,
    input  logic [3:0]  op,
    output logic [31:0] result,
    output logic        busy,      // ALU está ocupada executando
    output logic        done       // Operação concluída
);
    // Contadores e estados para operações multi-ciclo
    logic [3:0] cycle_count;
    logic [63:0] mult_result;
    
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            cycle_count <= 0;
            busy <= 0;
            done <= 0;
            result <= 0;
        end
        else begin
            if (op == 4'b0000) begin  // ADD/SUB - 1 ciclo
                result <= (op[3]) ? a - b : a + b;
                busy <= 0;
                done <= 1;
            end
            else if (op == 4'b0001 && !busy) begin  // MULT - Iniciar
                mult_result <= 0;
                cycle_count <= 1;
                busy <= 1;
                done <= 0;
            end
            else if (op == 4'b0001 && busy) begin  // MULT - Continuar
                if (cycle_count < 4) begin
                    // Algoritmo de multiplicação sequencial simplificado
                    mult_result <= mult_result + (a << (8 * (cycle_count-1))) * ((b >> (8 * (cycle_count-1))) & 8'hFF);
                    cycle_count <= cycle_count + 1;
                end
                else begin
                    result <= mult_result[31:0];
                    busy <= 0;
                    done <= 1;
                end
            end
            // Implementar outras operações multi-ciclo
        end
    end
endmodule