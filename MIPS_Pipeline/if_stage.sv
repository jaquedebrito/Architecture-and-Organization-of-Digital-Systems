module if_stage (
    // Sinais básicos
    input  logic        clk, reset,
    input  logic        stall,
    
    // Sinais de branch
    input  logic        branch_id,
    input  logic [31:0] pc_branch,
    input  logic        pcsrc,
    input  logic        prediction,
    input  logic [31:0] pc_predict,
    
    // Sinais de instrução
    input  logic [31:0] current_instr,
    input  logic        id_is_branch,
    input  logic        id_branch_taken,
    
    // Saídas principais
    output logic [31:0] pc,
    output logic [31:0] pc_plus4,
    output logic [31:0] instr,
    
    // Novas saídas para monitoramento e debug
    output logic [31:0] fetch_cycles,      // Contador de ciclos de fetch
    output logic [31:0] branch_misses,     // Contador de branch mispredictions
    output logic [31:0] stall_cycles,      // Contador de ciclos de stall
    output logic        prediction_valid,   // Indicador de predição válida
    output logic [1:0]  fetch_state,       // Estado atual do fetch
    output logic        fetch_ready        // Indicador de fetch válido
);
    // Sinais internos
    logic [31:0] pc_next;
    logic        is_branch_instr;
    logic        prediction_mismatch;
    logic [31:0] cycle_counter;
    logic        fetch_valid;
    
    // Estados do fetch
    typedef enum logic[1:0] {
        FETCH_NORMAL = 2'b00,
        FETCH_STALL  = 2'b01,
        FETCH_BRANCH = 2'b10,
        FETCH_FLUSH  = 2'b11
    } fetch_state_t;
    
    fetch_state_t current_state;

    // Detecção de branch misprediction
    assign prediction_mismatch = id_is_branch && (prediction != id_branch_taken);

    // Lógica de seleção do PC otimizada
    always_comb begin
        // Default
        pc_next = pc_plus4;
        fetch_valid = 1'b1;
        
        unique case (current_state)
            FETCH_NORMAL: begin
                if (prediction && !stall)
                    pc_next = pc_predict;
            end
            
            FETCH_STALL: begin
                pc_next = pc;
                fetch_valid = 1'b0;
            end
            
            FETCH_BRANCH: begin
                if (id_is_branch && id_branch_taken)
                    pc_next = pc_branch;
                else if (prediction_mismatch)
                    pc_next = pc_plus4;
            end
            
            FETCH_FLUSH: begin
                pc_next = pc_branch;
                fetch_valid = 1'b0;
            end
        endcase
    end

    // Máquina de estados do fetch
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            current_state <= FETCH_NORMAL;
        end else begin
            unique case (current_state)
                FETCH_NORMAL: begin
                    if (stall)
                        current_state <= FETCH_STALL;
                    else if (id_is_branch)
                        current_state <= FETCH_BRANCH;
                end
                
                FETCH_STALL: begin
                    if (!stall)
                        current_state <= FETCH_NORMAL;
                end
                
                FETCH_BRANCH: begin
                    if (prediction_mismatch)
                        current_state <= FETCH_FLUSH;
                    else
                        current_state <= FETCH_NORMAL;
                end
                
                FETCH_FLUSH: begin
                    current_state <= FETCH_NORMAL;
                end
            endcase
        end
    end

    // Registrador do PC com clear síncrono
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            pc <= 32'b0;
        end else if (!stall) begin
            pc <= pc_next;
        end
    end

    // Contadores de performance
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            fetch_cycles <= 32'h0;
            branch_misses <= 32'h0;
            stall_cycles <= 32'h0;
            cycle_counter <= 32'h0;
        end else begin
            cycle_counter <= cycle_counter + 1;
            
            if (!stall)
                fetch_cycles <= fetch_cycles + 1;
                
            if (prediction_mismatch)
                branch_misses <= branch_misses + 1;
                
            if (stall)
                stall_cycles <= stall_cycles + 1;
        end
    end

    // Atribuições de saída
    assign pc_plus4 = pc + 32'd4;
    assign fetch_state = current_state;
    assign fetch_ready = fetch_valid;
    assign prediction_valid = !prediction_mismatch;

    // Assertions para verificação
    `ifdef FORMAL
        // Verificar transições de estado válidas
        property valid_state_transition;
            @(posedge clk) disable iff (reset)
            current_state != $past(current_state) |-> 
                (current_state inside {FETCH_NORMAL, FETCH_STALL, FETCH_BRANCH, FETCH_FLUSH});
        endproperty

        // Verificar stall comportamento
        property valid_stall_behavior;
            @(posedge clk) disable iff (reset)
            stall |-> (pc == $past(pc));
        endproperty

        // Verificar predição válida
        property valid_prediction;
            @(posedge clk) disable iff (reset)
            prediction && id_is_branch |-> ##1 prediction_valid;
        endproperty

        assert property (valid_state_transition)
            else $error("Invalid state transition");
        assert property (valid_stall_behavior)
            else $error("Invalid stall behavior");
        assert property (valid_prediction)
            else $error("Invalid prediction behavior");

        // Coverage
        cover property (valid_state_transition);
        cover property (valid_stall_behavior);
        cover property (valid_prediction);
    `endif

endmodule