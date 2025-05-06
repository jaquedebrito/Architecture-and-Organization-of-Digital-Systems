`timescale 1ns/1ps

module branch_predictor_tb;
    // Parâmetros do testbench
    localparam CLK_PERIOD = 10;
    localparam BHT_SIZE = 256;
    localparam HIST_LEN = 2;
    localparam BTB_WAYS = 2;
    localparam NUM_TESTS = 1000;
    localparam NUM_PATTERN_TESTS = 100;
    
    // Sinais para o DUT
    logic        clk;
    logic        reset;
    logic [31:0] pc;
    logic        branch;
    logic        taken;
    logic        clear_btb;
    logic [31:0] correct_target;
    logic        btb_hit;
    logic [31:0] predicted_target;
    logic        prediction;
    
    // Sinais de monitoramento
    logic [31:0] prediction_accuracy;
    logic [31:0] btb_hit_rate;
    logic [31:0] branch_frequency;
    logic [1:0]  predictor_status;
    logic [63:0] last_update_time;
    
    // Sinais do testbench
    int correct_predictions;
    int total_predictions;
    int btb_hits;
    int btb_accesses;
    
    // Tipos e estruturas para teste
    typedef struct {
        logic [31:0] pc;
        logic        is_branch;
        logic        is_taken;
        logic [31:0] target;
    } branch_test_t;
    
    // Instantiating the DUT
    branch_predictor #(
        .BHT_SIZE(BHT_SIZE),
        .HIST_LEN(HIST_LEN),
        .BTB_WAYS(BTB_WAYS)
    ) dut (
        .clk(clk),
        .reset(reset),
        .pc(pc),
        .branch(branch),
        .taken(taken),
        .clear_btb(clear_btb),
        .correct_target(correct_target),
        .btb_hit(btb_hit),
        .predicted_target(predicted_target),
        .prediction(prediction),
        .prediction_accuracy(prediction_accuracy),
        .btb_hit_rate(btb_hit_rate),
        .branch_frequency(branch_frequency),
        .predictor_status(predictor_status),
        .last_update_time(last_update_time)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // Test sequences and arrays
    branch_test_t branch_sequence[$];
    branch_test_t loop_pattern[$];
    branch_test_t if_else_pattern[$];
    branch_test_t switch_case_pattern[$];
    branch_test_t random_pattern[$];
    
    // Function to generate random address
    function logic [31:0] random_address();
        logic [31:0] addr;
        addr = $urandom_range(32'h0000_1000, 32'h0001_0000);
        addr = {addr[31:2], 2'b00}; // Align to 4 bytes
        return addr;
    endfunction
    
    // Task to initialize test data
    task initialize_test_data();
        // Inicialização de padrões de teste típicos
        
        // 1. Padrão de loop - previsível
        for (int i = 0; i < 20; i++) begin
            branch_test_t test;
            test.pc = 32'h0000_1000 + (i * 4);
            test.is_branch = (i == 19); // Branch no final do loop
            test.is_taken = (i == 19);  // Taken quando for branch
            test.target = 32'h0000_1000; // Volta para o início do loop
            loop_pattern.push_back(test);
        end
        
        // 2. Padrão de if-else - alternados
        for (int i = 0; i < 20; i++) begin
            branch_test_t test;
            test.pc = 32'h0000_2000 + (i * 4);
            test.is_branch = (i % 5 == 0); // Branch a cada 5 instruções
            test.is_taken = (i % 10 == 0); // Tomado a cada 10 instruções
            test.target = 32'h0000_2100 + (i * 8); // Target diferente para cada branch
            if_else_pattern.push_back(test);
        end
        
        // 3. Padrão de switch-case - várias opções
        for (int i = 0; i < 30; i++) begin
            branch_test_t test;
            test.pc = 32'h0000_3000 + (i * 4);
            test.is_branch = (i % 6 == 0); // Branch a cada 6 instruções
            test.is_taken = 1'b1; // Todos tomados (típico de switch)
            
            // Diferentes targets de acordo com o caso
            case (i % 5)
                0: test.target = 32'h0000_3100;
                1: test.target = 32'h0000_3200;
                2: test.target = 32'h0000_3300;
                3: test.target = 32'h0000_3400;
                4: test.target = 32'h0000_3500;
            endcase
            
            switch_case_pattern.push_back(test);
        end
        
        // 4. Padrão aleatório
        for (int i = 0; i < 50; i++) begin
            branch_test_t test;
            test.pc = random_address();
            test.is_branch = ($urandom_range(0, 100) < 30); // 30% de chance de ser branch
            test.is_taken = ($urandom_range(0, 100) < 60);  // 60% de chance de ser tomado
            test.target = random_address();
            random_pattern.push_back(test);
        end
    endtask
    
    // Task para executar um teste específico
    task run_test(input branch_test_t test);
        @(posedge clk);
        pc = test.pc;
        branch = test.is_branch;
        taken = test.is_taken;
        correct_target = test.target;
        
        @(posedge clk);
        
        if (branch) begin
            if (prediction == taken) begin
                correct_predictions++;
                $display("[%0t] PASS: PC=%h Prediction=%b Actual=%b", 
                         $time, test.pc, prediction, taken);
            end else begin
                $display("[%0t] FAIL: PC=%h Prediction=%b Actual=%b", 
                         $time, test.pc, prediction, taken);
            end
            
            total_predictions++;
            btb_accesses++;
            
            if (btb_hit) begin
                btb_hits++;
                if (predicted_target == test.target) begin
                    $display("[%0t] BTB TARGET CORRECT: %h", $time, predicted_target);
                end else begin
                    $display("[%0t] BTB TARGET INCORRECT: Predicted=%h Actual=%h", 
                             $time, predicted_target, test.target);
                end
            end
        end
    endtask
    
    // Task para executar uma sequência de testes
    task run_sequence(input branch_test_t sequence[$], input string sequence_name);
        $display("\n[%0t] Running %s sequence", $time, sequence_name);
        foreach (sequence[i]) begin
            run_test(sequence[i]);
        end
        $display("[%0t] %s sequence complete. Hit rate: %0d/%0d (%0d%%)", 
                 $time, sequence_name, correct_predictions, total_predictions,
                 (correct_predictions * 100) / (total_predictions > 0 ? total_predictions : 1));
    endtask
    
    // Verificação de sinal predictor_status
    always @(predictor_status) begin
        case (predictor_status)
            2'b00: $display("[%0t] Predictor Status: IDLE", $time);
            2'b01: $display("[%0t] Predictor Status: PREDICT", $time);
            2'b10: $display("[%0t] Predictor Status: UPDATE", $time);
            2'b11: $display("[%0t] Predictor Status: ERROR", $time);
            default: $display("[%0t] Predictor Status: UNKNOWN", $time);
        endcase
    end
    
    // Testes de padrões repetitivos
    task test_repetitive_patterns();
        $display("\n[%0t] Testing repetitive patterns...", $time);
        
        // Testar padrão T-NT-T-NT (2-bit deve aprender isso)
        for (int i = 0; i < 10; i++) begin
            // Primeiro ciclo: taken
            pc = 32'h0005_0000;
            branch = 1'b1;
            taken = 1'b1;
            correct_target = 32'h0005_0100;
            @(posedge clk);
            @(posedge clk);
            
            // Segundo ciclo: not taken
            pc = 32'h0005_0004;
            branch = 1'b1;
            taken = 1'b0;
            correct_target = 32'h0005_0200;
            @(posedge clk);
            @(posedge clk);
        end
        
        // Verificar se aprendeu o padrão (próximos 5 ciclos devem prever corretamente)
        for (int i = 0; i < 5; i++) begin
            // Verificar predição para taken
            pc = 32'h0005_0000;
            branch = 1'b1;
            @(posedge clk);
            if (prediction == 1'b1) begin
                $display("[%0t] PATTERN LEARNED: Predicted taken correctly", $time);
            end else begin
                $display("[%0t] PATTERN FAILED: Should predict taken", $time);
            end
            taken = 1'b1;
            correct_target = 32'h0005_0100;
            @(posedge clk);
            
            // Verificar predição para not taken
            pc = 32'h0005_0004;
            branch = 1'b1;
            @(posedge clk);
            if (prediction == 1'b0) begin
                $display("[%0t] PATTERN LEARNED: Predicted not taken correctly", $time);
            end else begin
                $display("[%0t] PATTERN FAILED: Should predict not taken", $time);
            end
            taken = 1'b0;
            correct_target = 32'h0005_0200;
            @(posedge clk);
        end
    endtask
    
    // Teste de BTB associativo
    task test_btb_associativity();
        $display("\n[%0t] Testing BTB associativity...", $time);
        
        // Resetar BTB
        clear_btb = 1'b1;
        @(posedge clk);
        clear_btb = 1'b0;
        @(posedge clk);
        
        // Criar colisão no mesmo índice mas com tags diferentes
        logic [7:0] test_index = 8'h10;
        logic [31:0] pc_base = {22'b0, test_index, 2'b0}; // PC com índice específico
        
        // Inserir primeira entrada no BTB
        pc = pc_base;
        branch = 1'b1;
        taken = 1'b1;
        correct_target = 32'h0006_0100;
        @(posedge clk);
        @(posedge clk);
        
        // Verificar se foi inserido
        pc = pc_base;
        branch = 1'b1;
        @(posedge clk);
        if (btb_hit && predicted_target == 32'h0006_0100) begin
            $display("[%0t] BTB WAY 1: Hit successful for PC=%h, Target=%h", 
                     $time, pc_base, predicted_target);
        end else begin
            $display("[%0t] BTB WAY 1: Failed hit for PC=%h", $time, pc_base);
        end
        @(posedge clk);
        
        // Inserir segunda entrada no mesmo índice mas tag diferente
        // Modificando bits altos do PC para mesma entrada no BTB
        pc = {8'hAA, 14'b0, test_index, 2'b0};
        branch = 1'b1;
        taken = 1'b1;
        correct_target = 32'h0006_0200;
        @(posedge clk);
        @(posedge clk);
        
        // Verificar se ambas entradas estão no BTB
        pc = pc_base;
        branch = 1'b1;
        @(posedge clk);
        if (btb_hit && predicted_target == 32'h0006_0100) begin
            $display("[%0t] BTB ASSOCIATIVITY: First entry preserved, Target=%h", 
                     $time, predicted_target);
        end else begin
            $display("[%0t] BTB ASSOCIATIVITY: First entry lost!", $time);
        end
        @(posedge clk);
        
        pc = {8'hAA, 14'b0, test_index, 2'b0};
        branch = 1'b1;
        @(posedge clk);
        if (btb_hit && predicted_target == 32'h0006_0200) begin
            $display("[%0t] BTB ASSOCIATIVITY: Second entry found, Target=%h", 
                     $time, predicted_target);
        end else begin
            $display("[%0t] BTB ASSOCIATIVITY: Second entry not found!", $time);
        end
        @(posedge clk);
    endtask
    
    // Teste de stress para overflow
    task test_overflow();
        $display("\n[%0t] Testing overflow conditions...", $time);
        
        // Testar comportamento quando índices se repetem
        for (int i = 0; i < BHT_SIZE*2; i++) begin
            pc = random_address();
            branch = 1'b1;
            taken = (i % 2 == 0);
            correct_target = random_address();
            @(posedge clk);
            @(posedge clk);
        end
        
        $display("[%0t] Overflow test complete. BHT size: %0d", $time, BHT_SIZE);
    endtask
    
    // Teste principal
    initial begin
        // Inicialização
        $display("=== Branch Predictor Testbench Iniciado ===");
        $display("Parâmetros: BHT_SIZE=%0d, HIST_LEN=%0d, BTB_WAYS=%0d", 
                 BHT_SIZE, HIST_LEN, BTB_WAYS);
        
        correct_predictions = 0;
        total_predictions = 0;
        btb_hits = 0;
        btb_accesses = 0;
        
        // Reset
        reset = 1'b1;
        clear_btb = 1'b0;
        pc = 32'h0;
        branch = 1'b0;
        taken = 1'b0;
        correct_target = 32'h0;
        
        // Inicializar dados de teste
        initialize_test_data();
        
        repeat(5) @(posedge clk);
        reset = 1'b0;
        repeat(5) @(posedge clk);
        
        // Execução de testes
        $display("\n=== Teste 1: Padrões de Loop ===");
        run_sequence(loop_pattern, "Loop");
        
        $display("\n=== Teste 2: Padrões de If-Else ===");
        run_sequence(if_else_pattern, "If-Else");
        
        $display("\n=== Teste 3: Padrões de Switch-Case ===");
        run_sequence(switch_case_pattern, "Switch-Case");
        
        $display("\n=== Teste 4: Padrões Aleatórios ===");
        run_sequence(random_pattern, "Random");
        
        $display("\n=== Teste 5: Padrões Repetitivos ===");
        test_repetitive_patterns();
        
        $display("\n=== Teste 6: Associatividade do BTB ===");
        test_btb_associativity();
        
        $display("\n=== Teste 7: Teste de Overflow ===");
        test_overflow();
        
        // Relatório final
        $display("\n=== Relatório Final de Testes ===");
        $display("Taxa de acerto de predição: %0d/%0d (%0d%%)", 
                 correct_predictions, total_predictions,
                 (correct_predictions * 100) / (total_predictions > 0 ? total_predictions : 1));
        $display("Taxa de hit BTB: %0d/%0d (%0d%%)", 
                 btb_hits, btb_accesses,
                 (btb_hits * 100) / (btb_accesses > 0 ? btb_accesses : 1));
        $display("Prediction Accuracy (DUT): %0d%%", prediction_accuracy);
        $display("BTB Hit Rate (DUT): %0d%%", btb_hit_rate);
        $display("Branch Frequency (DUT): %0d%%", branch_frequency);
        
        $finish;
    end
    
    // Coverage
    covergroup branch_predictor_cg @(posedge clk);
        // Cobertura para BTB hit/miss
        btb_hit_cp: coverpoint btb_hit {
            bins hit = {1'b1};
            bins miss = {1'b0};
        }
        
        // Cobertura para prediction correta/incorreta
        prediction_cp: coverpoint (branch && (prediction == taken)) {
            bins correct = {1'b1};
            bins incorrect = {1'b0};
        }
        
        // Cobertura para estado do preditor
        state_cp: coverpoint predictor_status {
            bins idle = {2'b00};
            bins predict = {2'b01};
            bins update = {2'b10};
            bins error = {2'b11};
        }
        
        // Cobertura para padrões de branch (taken/not-taken)
        branch_pattern_cp: coverpoint {branch, taken} {
            bins not_branch = {2'b00};
            bins branch_not_taken = {2'b10};
            bins branch_taken = {2'b11};
        }
        
        // Cross coverage
        prediction_x_hit: cross prediction_cp, btb_hit_cp;
        state_x_branch: cross state_cp, branch_pattern_cp;
    endgroup
    
    // Instanciar grupo de cobertura
    branch_predictor_cg cg;
    
    initial begin
        cg = new();
    end
    
endmodule