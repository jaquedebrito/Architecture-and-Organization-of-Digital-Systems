module branch_predictor #(
    parameter BHT_SIZE = 256,
    parameter HIST_LEN = 2,
    parameter BTB_WAYS = 2,
    // Novos parâmetros
    parameter ENABLE_TOURNAMENT = 1,    // Habilita preditor torneio (combinando local e global)
    parameter ENABLE_TAGE = 0           // Habilita preditor TAGE (mais avançado)
)(
    // Interfaces mantidas iguais para compatibilidade
    input  logic        clk, reset,
    input  logic [31:0] pc,
    input  logic        branch,
    input  logic        taken,
    
    input  logic        clear_btb,
    input  logic [31:0] correct_target,
    output logic        btb_hit,
    output logic [31:0] predicted_target,
    output logic        prediction,
    
    output logic [31:0] prediction_accuracy,
    output logic [31:0] btb_hit_rate,
    output logic [31:0] branch_frequency,
    output logic [1:0]  predictor_status,
    output logic [63:0] last_update_time
);

    // Definições de estado
    typedef enum logic[1:0] {
        PRED_IDLE    = 2'b00,
        PRED_PREDICT = 2'b01,
        PRED_UPDATE  = 2'b10,
        PRED_ERROR   = 2'b11
    } pred_state_t;

    // Estruturas internas otimizadas
    logic [1:0]  branch_history_table [BHT_SIZE-1:0];
    logic [HIST_LEN-1:0] global_history;
    logic [HIST_LEN-1:0] local_history [BHT_SIZE-1:0];  // Nova tabela de histórico local
    logic [1:0]  local_prediction_table [BHT_SIZE-1:0]; // Tabela para predições locais
    logic [1:0]  global_prediction_table [2**HIST_LEN-1:0]; // Predições baseadas em histórico global
    logic [1:0]  choice_predictor [2**HIST_LEN-1:0];    // Escolhe entre preditor local e global
    
    logic [7:0]  index;
    logic [7:0]  local_index;
    logic [HIST_LEN-1:0] global_index;
    
    logic [31:0] correct_predictions;
    logic [31:0] total_predictions;
    
    // BTB otimizado com tags completos para reduzir colisões
    typedef struct packed {
        logic        valid;
        logic [31:0] tag;
        logic [31:0] target;
        logic [1:0]  lru;
        logic        confidence;    // Bit de confiança adicional
    } btb_entry_t;
    
    btb_entry_t btb [BHT_SIZE-1:0][BTB_WAYS-1:0];
    
    // Contadores e estatísticas
    logic [31:0] total_branches;
    logic [31:0] btb_hits;
    logic [31:0] btb_accesses;
    logic [31:0] branch_pattern[4];
    
    // Métricas por tipo de preditor
    logic [31:0] local_correct;
    logic [31:0] global_correct;
    logic [31:0] tournament_correct;
    
    // Sinais internos
    pred_state_t current_state;
    logic [63:0] current_time;
    logic        prediction_error;
    logic [31:0] last_pc;
    logic        last_prediction;
    logic [BTB_WAYS-1:0] way_hit;
    logic        local_pred;
    logic        global_pred;
    logic        final_pred;

    // Inicialização
    initial begin
        current_time = 64'd1711801273; // 2025-03-20 12:21:13
        current_state = PRED_IDLE;
        prediction_error = 1'b0;
        
        // Inicializar tabelas com valores neutros
        for (int i = 0; i < BHT_SIZE; i++) begin
            branch_history_table[i] = 2'b01;  // Inicialmente fracamente não tomado
            local_history[i] = '0;
            local_prediction_table[i] = 2'b01;
            
            for (int j = 0; j < BTB_WAYS; j++) begin
                btb[i][j].valid = 1'b0;
                btb[i][j].lru = 2'b00;
                btb[i][j].confidence = 1'b0;
            end
        end
        
        // Inicializar tabelas de predição global
        for (int i = 0; i < 2**HIST_LEN; i++) begin
            global_prediction_table[i] = 2'b01;
            choice_predictor[i] = 2'b01; // Neutro entre preditor local e global
        end
    end

    // Cálculo dos índices com proteção contra aliasing
    assign index = pc[9:2] ^ {6'b0, global_history};
    assign local_index = pc[9:2]; // Index baseado apenas no PC
    assign global_index = global_history;

    // Lógica do BTB otimizada para reduzir falsos hits
    always_comb begin
        btb_hit = 1'b0;
        predicted_target = 32'h0;
        way_hit = {BTB_WAYS{1'b0}};
        
        // Verificar todas as vias do BTB
        for (int i = 0; i < BTB_WAYS; i++) begin
            if (btb[index][i].valid && btb[index][i].tag == pc) begin
                btb_hit = 1'b1;
                predicted_target = btb[index][i].target;
                way_hit[i] = 1'b1;
            end
        end
    end

    // Lógica de predição multi-nível
    always_comb begin
        // Predição local baseada no histórico local
        local_pred = branch & local_prediction_table[local_index][1];
        
        // Predição global baseada no histórico global
        global_pred = branch & global_prediction_table[global_index][1];
        
        // Seleção baseada no preditor de escolha (tournament)
        if (ENABLE_TOURNAMENT) begin
            final_pred = choice_predictor[global_index][1] ? global_pred : local_pred;
        end else begin
            final_pred = global_pred; // Usar apenas preditor global se tournament desabilitado
        end
        
        // Final prediction também leva em conta BTB hit
        prediction = final_pred & btb_hit;
    end

    // Atualização do histórico global e local
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            correct_predictions <= 0;
            total_predictions <= 0;
            global_history <= '0;
            local_history[local_index] <= '0;
            last_pc <= 32'h0;
            last_prediction <= 1'b0;
        end 
        else if (branch) begin
            // Atualizar histórico global
            global_history <= {global_history[HIST_LEN-2:0], taken};
            
            // Atualizar histórico local
            local_history[local_index] <= {local_history[local_index][HIST_LEN-2:0], taken};
            
            last_pc <= pc;
            last_prediction <= prediction;
        end
    end

    // Atualização da BHT, tabelas de predição e BTB
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            // Reset completo
            for (int i = 0; i < BHT_SIZE; i++) begin
                branch_history_table[i] <= 2'b01;
                local_prediction_table[i] <= 2'b01;
                local_history[i] <= '0;
                
                for (int j = 0; j < BTB_WAYS; j++) begin
                    btb[i][j].valid <= 1'b0;
                    btb[i][j].lru <= 2'b00;
                    btb[i][j].confidence <= 1'b0;
                end
            end
            
            for (int i = 0; i < 2**HIST_LEN; i++) begin
                global_prediction_table[i] <= 2'b01;
                choice_predictor[i] <= 2'b01;
            end
            
            current_state <= PRED_IDLE;
        end 
        else if (clear_btb) begin
            // Limpar apenas BTB
            for (int i = 0; i < BHT_SIZE; i++)
                for (int j = 0; j < BTB_WAYS; j++)
                    btb[i][j].valid <= 1'b0;
        end
        else if (branch) begin
            current_state <= PRED_UPDATE;
            
            // Atualizar tabelas de predição com saturação
            
            // 1. Atualizar preditor local
            if (taken) begin
                // Incrementar contador com saturação
                if (local_prediction_table[local_index] != 2'b11)
                    local_prediction_table[local_index] <= local_prediction_table[local_index] + 1;
            end else begin
                // Decrementar contador com saturação
                if (local_prediction_table[local_index] != 2'b00)
                    local_prediction_table[local_index] <= local_prediction_table[local_index] - 1;
            end
            
            // 2. Atualizar preditor global
            if (taken) begin
                if (global_prediction_table[global_index] != 2'b11)
                    global_prediction_table[global_index] <= global_prediction_table[global_index] + 1;
            end else begin
                if (global_prediction_table[global_index] != 2'b00)
                    global_prediction_table[global_index] <= global_prediction_table[global_index] - 1;
            end
            
            // 3. Atualizar preditor de escolha (tournament)
            if (ENABLE_TOURNAMENT && (local_pred != global_pred)) begin
                // Quando os preditores discordam, atualizar o preditor de escolha
                if ((taken == local_pred) && choice_predictor[global_index] != 2'b00) begin
                    // Local estava certo, favor local
                    choice_predictor[global_index] <= choice_predictor[global_index] - 1;
                end
                else if ((taken == global_pred) && choice_predictor[global_index] != 2'b11) begin
                    // Global estava certo, favor global
                    choice_predictor[global_index] <= choice_predictor[global_index] + 1;
                end
            end
            
            // 4. Atualizar BHT (manter para compatibilidade)
            case (branch_history_table[index])
                2'b00: branch_history_table[index] <= taken ? 2'b01 : 2'b00;
                2'b01: branch_history_table[index] <= taken ? 2'b11 : 2'b00;
                2'b10: branch_history_table[index] <= taken ? 2'b11 : 2'b00;
                2'b11: branch_history_table[index] <= taken ? 2'b11 : 2'b10;
            endcase
            
            // 5. Atualizar BTB com política LRU aprimorada
            if (taken) begin
                logic [BTB_WAYS-1:0] way_selected;
                logic found_empty = 0;
                logic found_match = 0;
                
                // Primeira prioridade: atualizar entrada existente
                for (int i = 0; i < BTB_WAYS; i++) begin
                    if (btb[index][i].valid && btb[index][i].tag == pc) begin
                        way_selected = i;
                        found_match = 1;
                        break;
                    end
                end
                
                // Segunda prioridade: usar entrada vazia
                if (!found_match) begin
                    for (int i = 0; i < BTB_WAYS; i++) begin
                        if (!btb[index][i].valid && !found_empty) begin
                            way_selected = i;
                            found_empty = 1;
                            break;
                        end
                    end
                end
                
                // Terceira prioridade: usar LRU
                if (!found_match && !found_empty) begin
                    logic [1:0] min_lru = 2'b11;
                    for (int i = 0; i < BTB_WAYS; i++) begin
                        if (btb[index][i].lru < min_lru) begin
                            min_lru = btb[index][i].lru;
                            way_selected = i;
                        end
                    end
                }
                
                // Atualizar entrada selecionada
                btb[index][way_selected].valid <= 1'b1;
                btb[index][way_selected].tag <= pc;
                btb[index][way_selected].target <= correct_target;
                btb[index][way_selected].lru <= 2'b11;
                
                // Incrementar confiança se alvo correto, zerar se incorreto
                if (found_match && btb[index][way_selected].target != correct_target)
                    btb[index][way_selected].confidence <= 1'b0;
                else
                    btb[index][way_selected].confidence <= 1'b1;
                
                // Atualizar contadores LRU
                for (int i = 0; i < BTB_WAYS; i++) begin
                    if (i != way_selected && btb[index][i].valid && btb[index][i].lru > 2'b00)
                        btb[index][i].lru <= btb[index][i].lru - 1;
                end
            end
        end
    end

    // Monitoramento e estatísticas
    always_ff @(posedge clk) begin
        current_time <= current_time + 1;
        
        if (branch) begin
            btb_accesses <= btb_accesses + 1;
            total_branches <= total_branches + 1;
            
            if (btb_hit) btb_hits <= btb_hits + 1;
            
            // Atualizar estatísticas
            if (local_pred == taken) local_correct <= local_correct + 1;
            if (global_pred == taken) global_correct <= global_correct + 1;
            if (final_pred == taken) tournament_correct <= tournament_correct + 1;
            
            // Atualizar padrões de branch
            case ({last_prediction, taken})
                2'b00: branch_pattern[0] <= branch_pattern[0] + 1; // NT->NT
                2'b01: branch_pattern[1] <= branch_pattern[1] + 1; // NT->T
                2'b10: branch_pattern[2] <= branch_pattern[2] + 1; // T->NT
                2'b11: branch_pattern[3] <= branch_pattern[3] + 1; // T->T
            endcase
            
            // Atualizar contadores de predição
            total_predictions <= total_predictions + 1;
            if (prediction == taken) correct_predictions <= correct_predictions + 1;
            
            // Verificar erro de predição
            prediction_error <= (prediction != taken);
        end
    end

    // Saídas de monitoramento
    assign prediction_accuracy = (total_predictions > 0) ? 
                               (correct_predictions * 100) / total_predictions : 0;
    assign btb_hit_rate = (btb_accesses > 0) ? 
                         (btb_hits * 100) / btb_accesses : 0;
    assign branch_frequency = (current_time > 0) ? 
                            (total_branches * 100) / current_time : 0;
    assign predictor_status = current_state;
    assign last_update_time = current_time;

endmodule