module hazard_detection_unit (
    // Entradas principais
    input  logic [4:0] rs_id, rt_id,
    input  logic [4:0] rt_ex, rd_ex, rd_mem,
    input  logic       memread_ex,
    input  logic       regwrite_ex,
    input  logic       branch_id,
    input  logic       jump_id,
    input  logic       branch_taken,
    
    // Saídas principais
    output logic       load_hazard,
    output logic       branch_hazard,
    output logic       control_hazard,
    
    // Novas saídas para monitoramento
    output logic [31:0] load_hazard_count,    // Contador de load hazards
    output logic [31:0] branch_hazard_count,  // Contador de branch hazards
    output logic [31:0] control_hazard_count, // Contador de control hazards
    output logic [1:0]  hazard_status,        // Status da unidade
    output logic [63:0] last_update_time      // Timestamp da última atualização
);
    // Definições de estado
    typedef enum logic[1:0] {
        HAZARD_NONE    = 2'b00,
        HAZARD_LOAD    = 2'b01,
        HAZARD_BRANCH  = 2'b10,
        HAZARD_CONTROL = 2'b11
    } hazard_state_t;

    // Sinais internos
    hazard_state_t current_state;
    logic [63:0]   current_time;
    logic          multiple_hazards;
    logic [31:0]   hazard_by_reg[31:0];  // Contador de hazards por registrador

    // Inicialização
    initial begin
        current_time = 64'd1711801123; // 2025-03-20 12:18:43
        current_state = HAZARD_NONE;
        load_hazard_count = 32'h0;
        branch_hazard_count = 32'h0;
        control_hazard_count = 32'h0;
        multiple_hazards = 1'b0;
        
        for (int i = 0; i < 32; i++)
            hazard_by_reg[i] = 32'h0;
    end

    // Lógica de detecção de hazards com monitoramento
    always_comb begin
        // Reset de sinais temporários
        load_hazard = 1'b0;
        branch_hazard = 1'b0;
        control_hazard = 1'b0;
        multiple_hazards = 1'b0;
        
        // Load hazard
        if (memread_ex && ((rt_ex == rs_id) || (rt_ex == rt_id))) begin
            load_hazard = 1'b1;
            if (rt_ex == rs_id && rt_ex == rt_id)
                multiple_hazards = 1'b1;
        end
        
        // Branch hazard
        if (branch_id && (
            (rd_ex == rs_id) || (rd_ex == rt_id) ||
            (rd_mem == rs_id) || (rd_mem == rt_id)
        )) begin
            branch_hazard = 1'b1;
            if ((rd_ex == rs_id && rd_ex == rt_id) ||
                (rd_mem == rs_id && rd_mem == rt_id))
                multiple_hazards = 1'b1;
        end
        
        // Control hazard
        if (jump_id || (branch_id && branch_taken)) begin
            control_hazard = 1'b1;
        end
        
        // Atualização de estado
        case ({load_hazard, branch_hazard, control_hazard})
            3'b100:  current_state = HAZARD_LOAD;
            3'b010:  current_state = HAZARD_BRANCH;
            3'b001:  current_state = HAZARD_CONTROL;
            3'b000:  current_state = HAZARD_NONE;
            default: current_state = HAZARD_CONTROL; // Múltiplos hazards
        endcase
    end

    // Monitoramento e contadores
    always @(posedge load_hazard or posedge branch_hazard or posedge control_hazard) begin
        current_time = current_time + 1;
        
        if (load_hazard) begin
            load_hazard_count = load_hazard_count + 1;
            if (rt_ex < 32) hazard_by_reg[rt_ex] = hazard_by_reg[rt_ex] + 1;
        end
        
        if (branch_hazard) begin
            branch_hazard_count = branch_hazard_count + 1;
            if (rd_ex < 32) hazard_by_reg[rd_ex] = hazard_by_reg[rd_ex] + 1;
            if (rd_mem < 32) hazard_by_reg[rd_mem] = hazard_by_reg[rd_mem] + 1;
        end
        
        if (control_hazard)
            control_hazard_count = control_hazard_count + 1;
    end

    // Debug logging
    `ifdef DEBUG
        always @(current_state) begin
            $display("%s - Hazard Detection Status:", format_timestamp(current_time));
            $display("  User: jaquedebrito");
            $display("  State: %s", get_state_name(current_state));
            
            if (load_hazard) begin
                $display("  Load Hazard Detected:");
                $display("    rt_ex: %d", rt_ex);
                $display("    rs_id: %d, rt_id: %d", rs_id, rt_id);
            end
            
            if (branch_hazard) begin
                $display("  Branch Hazard Detected:");
                $display("    rd_ex: %d, rd_mem: %d", rd_ex, rd_mem);
                $display("    rs_id: %d, rt_id: %d", rs_id, rt_id);
            end
            
            if (control_hazard)
                $display("  Control Hazard Detected");
                
            if (multiple_hazards)
                $display("  WARNING: Multiple hazards detected");
                
            $display("  Statistics:");
            $display("    Load Hazards: %d", load_hazard_count);
            $display("    Branch Hazards: %d", branch_hazard_count);
            $display("    Control Hazards: %d", control_hazard_count);
        end
        
        function string format_timestamp(input logic [63:0] unix_time);
            return $sformatf("2025-03-20 12:18:%02d", unix_time % 60);
        endfunction
        
        function string get_state_name(input hazard_state_t state);
            case (state)
                HAZARD_NONE:    return "No Hazard";
                HAZARD_LOAD:    return "Load Hazard";
                HAZARD_BRANCH:  return "Branch Hazard";
                HAZARD_CONTROL: return "Control Hazard";
                default:        return "Unknown";
            endcase
        endfunction
    `endif

    // Assertions para verificação
    `ifdef FORMAL
        // Verificar exclusividade de load e branch hazards
        property exclusive_hazards;
            @(current_state) 
            !(load_hazard && branch_hazard);
        endproperty

        // Verificar registradores válidos
        property valid_registers;
            @(current_state)
            (rs_id < 32) && (rt_id < 32) && (rt_ex < 32) && 
            (rd_ex < 32) && (rd_mem < 32);
        endproperty

        // Verificar condições de load hazard
        property valid_load_hazard;
            @(current_state)
            load_hazard |-> memread_ex;
        endproperty

        // Verificar condições de branch hazard
        property valid_branch_hazard;
            @(current_state)
            branch_hazard |-> branch_id;
        endproperty

        assert property (exclusive_hazards)
            else $error("Invalid: simultaneous load and branch hazards");
        assert property (valid_registers)
            else $error("Invalid register numbers detected");
        assert property (valid_load_hazard)
            else $error("Invalid load hazard condition");
        assert property (valid_branch_hazard)
            else $error("Invalid branch hazard condition");

        // Coverage
        cover property (exclusive_hazards);
        cover property (valid_registers);
        cover property (valid_load_hazard);
        cover property (valid_branch_hazard);
    `endif

    // Status e timestamp
    assign hazard_status = current_state;
    assign last_update_time = current_time;

endmodule