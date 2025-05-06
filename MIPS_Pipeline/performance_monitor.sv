// Módulo de monitoramento de performance
import types_pkg::*;

    module performance_monitor #(
        parameter WINDOW_SIZE = 1000
    )(
        input  logic        clk,
        input  logic        reset,
        input  logic [63:0] current_time,
        input  logic [31:0] instruction_count,
        input  logic [31:0] cycle_count,
        input  logic [31:0] stall_count,
        input  logic [31:0] branch_count,
        input  logic [31:0] branch_mispredict_count,
        input  logic [31:0] hazard_count,
        input  logic [31:0] memory_access_count,
        input  logic [31:0] instruction_type_counts[6],
        input  proc_state_t current_state
    );
        // Métricas de janela deslizante
        logic [31:0] window_instructions;
        logic [31:0] window_cycles;
        logic [31:0] window_stalls;
        real         window_ipc;
        
        always_ff @(posedge clk or posedge reset) begin
            if (reset) begin
                window_instructions <= 32'h0;
                window_cycles <= 32'h0;
                window_stalls <= 32'h0;
                window_ipc <= 0.0;
            end
            else begin
                // Atualizar métricas da janela
                if (cycle_count % WINDOW_SIZE == 0) begin
                    window_instructions <= instruction_count;
                    window_cycles <= cycle_count;
                    window_stalls <= stall_count;
                    window_ipc <= $itor(instruction_count) / $itor(cycle_count);
                    
                    // Log de performance da janela
                    $display("%s - Window Performance Metrics:", 
                            format_timestamp(current_time));
                    $display("  User: jaquedebrito");
                    $display("  Window Size: %d cycles", WINDOW_SIZE);
                    $display("  IPC: %f", window_ipc);
                    $display("  Stall Rate: %f%%", 
                            100.0 * $itor(window_stalls) / WINDOW_SIZE);
                end
            end
        end
    endmodule