// Aluna: Jaqueline Ferreira de Brito
// Data: 2025-03-20 12:38:36

module ula (
    // Interface básica
    input  logic [31:0] a, b,
    input  logic [2:0]  ULAcontrol,
    output logic [31:0] result,
    output logic        zero,
    
    // Novas saídas para monitoramento
    output logic [31:0] op_count[8],     // Contador por operação
    output logic [31:0] overflow_count,  // Contador de overflows
    output logic [31:0] error_count,     // Contador de operações inválidas
    output logic [1:0]  ula_status,      // Status da ULA
    output logic [63:0] last_op_time    // Timestamp da última operação
);
    // Definições de estado
    typedef enum logic[1:0] {
        ULA_NORMAL  = 2'b00,
        ULA_OVERFLOW = 2'b01,
        ULA_ERROR   = 2'b10,
        ULA_INVALID = 2'b11
    } ula_state_t;

    // Sinais internos
    ula_state_t current_state;
    logic       overflow;
    logic       invalid_op;
    logic [63:0] current_time;

    // Inicialização
    initial begin
        current_time = 64'd1711801916; // 2025-03-20 12:38:36
        for (int i = 0; i < 8; i++)
            op_count[i] = 32'h0;
        overflow_count = 32'h0;
        error_count = 32'h0;
        current_state = ULA_NORMAL;
    end

    // Detecção de overflow para operações aritméticas
    function automatic logic check_overflow(logic [31:0] a, b, result);
        logic sign_a, sign_b, sign_r;
        sign_a = a[31];
        sign_b = b[31];
        sign_r = result[31];
        
        return ((sign_a == sign_b) && (sign_r != sign_a) &&
                (ULAcontrol == 3'b010 || ULAcontrol == 3'b110));
    endfunction

    // Lógica principal da ULA
    always_comb begin
        // Reset de sinais
        result = 32'h0;
        overflow = 1'b0;
        invalid_op = 1'b0;
        current_state = ULA_NORMAL;

        case (ULAcontrol)
            3'b000: begin  // AND
                result = a & b;
                op_count[0] = op_count[0] + 1;
            end
            3'b001: begin  // OR
                result = a | b;
                op_count[1] = op_count[1] + 1;
            end
            3'b010: begin  // ADD
                result = a + b;
                overflow = check_overflow(a, b, result);
                op_count[2] = op_count[2] + 1;
                if (overflow) begin
                    current_state = ULA_OVERFLOW;
                    overflow_count = overflow_count + 1;
                end
            end
            3'b110: begin  // SUB
                result = a - b;
                overflow = check_overflow(a, b, result);
                op_count[6] = op_count[6] + 1;
                if (overflow) begin
                    current_state = ULA_OVERFLOW;
                    overflow_count = overflow_count + 1;
                end
            end
            3'b111: begin  // SLT
                if (a[31] != b[31])
                    result = a[31] ? 32'd1 : 32'd0;
                else
                    result = (a < b) ? 32'd1 : 32'd0;
                op_count[7] = op_count[7] + 1;
            end
            default: begin
                invalid_op = 1'b1;
                current_state = ULA_INVALID;
                error_count = error_count + 1;
                result = ULAcontrol[0] ? (a | b) : (a & b);
            end
        endcase

        // Atualizar timestamp
        current_time = current_time + 1;
    end

    // Flag zero
    assign zero = (result == 32'b0);

    // Debug logging
    `ifdef DEBUG
        always @(a, b, ULAcontrol) begin
            $display("%s - ULA Operation:", format_timestamp(current_time));
            $display("  User: jaquedebrito");
            $display("  Operation: %s", get_op_name(ULAcontrol));
            $display("  A: 0x%h", a);
            $display("  B: 0x%h", b);
            $display("  Result: 0x%h", result);
            $display("  Zero: %b", zero);
            
            if (overflow)
                $display("  WARNING: Overflow detected!");
            if (invalid_op)
                $display("  WARNING: Invalid operation!");
        end
        
        function string format_timestamp(input logic [63:0] unix_time);
            return $sformatf("2025-03-20 12:38:%02d", unix_time % 60);
        endfunction
        
        function string get_op_name(input logic [2:0] op);
            case (op)
                3'b000: return "AND";
                3'b001: return "OR";
                3'b010: return "ADD";
                3'b110: return "SUB";
                3'b111: return "SLT";
                default: return "INVALID";
            endcase
        endfunction
    `endif

    // Assertions
    `ifdef FORMAL
        // Verificar operações válidas
        property valid_operation;
            @(ULAcontrol) 
            ULAcontrol inside {3'b000, 3'b001, 3'b010, 3'b110, 3'b111};
        endproperty

        // Verificar overflow em operações aritméticas
        property check_arithmetic_overflow;
            @(a, b) 
            (ULAcontrol inside {3'b010, 3'b110}) |-> 
            !((a[31] == b[31]) && (result[31] != a[31]));
        endproperty

        // Verificar flag zero
        property valid_zero_flag;
            @(result) 
            (result == 0) == zero;
        endproperty

        assert property (valid_operation)
            else $error("Invalid ULA operation");
        assert property (check_arithmetic_overflow)
            else $error("Arithmetic overflow");
        assert property (valid_zero_flag)
            else $error("Invalid zero flag");

        // Coverage
        cover property (valid_operation);
        cover property (check_arithmetic_overflow);
        cover property (valid_zero_flag);
    `endif

    // Status outputs
    assign ula_status = current_state;
    assign last_op_time = current_time;

endmodule