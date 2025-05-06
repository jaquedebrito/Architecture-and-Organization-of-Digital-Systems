// Aluna: Jaqueline Ferreira de Brito
module forwarding_unit (
    // Registradores fonte no estágio EX
    input  logic [4:0] rs_ex,
    input  logic [4:0] rt_ex,
    
    // Registradores destino em estágios posteriores
    input  logic [4:0] rd_mem,
    input  logic [4:0] rd_wb,
    
    // Sinais de escrita em registradores
    input  logic       regwrite_mem,
    input  logic       regwrite_wb,
    
    // Sinais para tratamento de loads
    input  logic       memread_mem,
    input  logic       memread_wb,
    
    // Clock para sincronização
    input  logic       clk,
    input  logic       rst_n,
    
    // Saídas de controle
    output logic [1:0] forward_a,
    output logic [1:0] forward_b,
    output logic [1:0] forward_mem,
    
    // Novas saídas para monitoramento
    output logic [31:0] forward_count_a,     
    output logic [31:0] forward_count_b,     
    output logic [31:0] forward_count_mem,   
    output logic [1:0]  forward_status,      
    output logic [63:0] last_update_time     
);
    // Definições de estado
    typedef enum logic[1:0] {
        FWD_NONE  = 2'b00,
        FWD_WB    = 2'b01,
        FWD_MEM   = 2'b10,
        FWD_ERROR = 2'b11
    } forward_state_t;

    // Sinais internos
    logic [63:0] current_time;
    logic [31:0] forward_by_reg[32];
    logic        invalid_forward;

    // Lógica combinacional para forwarding
    always_comb begin
        // Valores default
        forward_a = 2'b00;
        forward_b = 2'b00;
        forward_mem = 2'b00;
        forward_status = FWD_NONE;
        invalid_forward = 1'b0;

        // Forward A logic
        if (regwrite_mem && (rd_mem != 0) && (rd_mem == rs_ex)) begin
            forward_a = 2'b10;
            forward_status = FWD_MEM;
        end 
        else if (regwrite_wb && (rd_wb != 0) && (rd_wb == rs_ex) &&
                 !(regwrite_mem && (rd_mem != 0) && (rd_mem == rs_ex))) begin
            forward_a = 2'b01;
            forward_status = FWD_WB;
        end

        // Forward B logic
        if (regwrite_mem && (rd_mem != 0) && (rd_mem == rt_ex)) begin
            forward_b = 2'b10;
            if (forward_status != FWD_NONE) 
                forward_status = FWD_ERROR;
        end 
        else if (regwrite_wb && (rd_wb != 0) && (rd_wb == rt_ex) &&
                 !(regwrite_mem && (rd_mem != 0) && (rd_mem == rt_ex))) begin
            forward_b = 2'b01;
            if (forward_status != FWD_NONE) 
                forward_status = FWD_ERROR;
        end

        // Memory forwarding logic
        if (memread_mem && (rd_mem != 0) && (rd_mem == rt_ex)) begin
            forward_mem = 2'b10;
            if (forward_status != FWD_NONE) 
                forward_status = FWD_ERROR;
        end 
        else if (memread_wb && (rd_wb != 0) && (rd_wb == rt_ex) &&
                 !(memread_mem && (rd_mem != 0) && (rd_mem == rt_ex))) begin
            forward_mem = 2'b01;
            if (forward_status != FWD_NONE) 
                forward_status = FWD_ERROR;
        end

        // Invalid forwarding check
        invalid_forward = (forward_a == 2'b11) || (forward_b == 2'b11) || (forward_mem == 2'b11);
    end

    // Lógica sequencial para contadores e timestamp
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_time <= 64'd0;
            forward_count_a <= 32'h0;
            forward_count_b <= 32'h0;
            forward_count_mem <= 32'h0;
            for (int i = 0; i < 32; i++)
                forward_by_reg[i] <= 32'h0;
            last_update_time <= 64'd0;
        end
        else begin
            current_time <= current_time + 1;
            last_update_time <= current_time;
            
            if (forward_a != 2'b00) begin
                forward_count_a <= forward_count_a + 1;
                if (rs_ex < 32) 
                    forward_by_reg[rs_ex] <= forward_by_reg[rs_ex] + 1;
            end
            
            if (forward_b != 2'b00) begin
                forward_count_b <= forward_count_b + 1;
                if (rt_ex < 32) 
                    forward_by_reg[rt_ex] <= forward_by_reg[rt_ex] + 1;
            end
            
            if (forward_mem != 2'b00)
                forward_count_mem <= forward_count_mem + 1;
        end
    end

    // Debug logging
    `ifdef DEBUG
        always @(forward_status) begin
            $display("%s - Forwarding Unit Status:", format_timestamp(current_time));
            $display("  User: jaquedebrito");
            $display("  State: %s", get_state_name(forward_status));
            
            if (forward_a != 2'b00) begin
                $display("  Forward A Active:");
                $display("    Source: %s", get_forward_source(forward_a));
                $display("    Register: rs_ex(%d)", rs_ex);
            end
            
            if (forward_b != 2'b00) begin
                $display("  Forward B Active:");
                $display("    Source: %s", get_forward_source(forward_b));
                $display("    Register: rt_ex(%d)", rt_ex);
            end
            
            if (forward_mem != 2'b00) begin
                $display("  Memory Forward Active:");
                $display("    Source: %s", get_forward_source(forward_mem));
            end
            
            if (invalid_forward)
                $display("  WARNING: Invalid forwarding detected");
                
            $display("  Statistics:");
            $display("    Forward A Count: %d", forward_count_a);
            $display("    Forward B Count: %d", forward_count_b);
            $display("    Memory Forward Count: %d", forward_count_mem);
        end
        
        function string format_timestamp(input logic [63:0] unix_time);
            return $sformatf("2025-03-20 17:33:%02d", unix_time % 60);
        endfunction
        
        function string get_state_name(input forward_state_t state);
            case (state)
                FWD_NONE:  return "No Forwarding";
                FWD_WB:    return "WB Forwarding";
                FWD_MEM:   return "MEM Forwarding";
                FWD_ERROR: return "Error";
                default:   return "Unknown";
            endcase
        endfunction
        
        function string get_forward_source(input logic [1:0] forward);
            case (forward)
                2'b00: return "None";
                2'b01: return "WB Stage";
                2'b10: return "MEM Stage";
                2'b11: return "Invalid";
            endcase
        endfunction
    `endif

    // Assertions para verificação
    `ifdef FORMAL
        property valid_forward_values;
            @(posedge clk) disable iff (!rst_n)
            !invalid_forward;
        endproperty

        property valid_registers;
            @(posedge clk) disable iff (!rst_n)
            (rs_ex < 32) && (rt_ex < 32) && 
            (rd_mem < 32) && (rd_wb < 32);
        endproperty

        property forwarding_priority;
            @(posedge clk) disable iff (!rst_n)
            (forward_a == 2'b10) |-> !(forward_a == 2'b01);
        endproperty

        property exclusive_forwarding;
            @(posedge clk) disable iff (!rst_n)
            !(forward_a != 2'b00 && forward_b != 2'b00 && forward_mem != 2'b00);
        endproperty

        assert property (valid_forward_values)
            else $error("Invalid forwarding values detected");
        assert property (valid_registers)
            else $error("Invalid register numbers detected");
        assert property (forwarding_priority)
            else $error("Invalid forwarding priority");
        assert property (exclusive_forwarding)
            else $error("Invalid: multiple simultaneous forwardings");

        cover property (valid_forward_values);
        cover property (valid_registers);
        cover property (forwarding_priority);
        cover property (exclusive_forwarding);
    `endif
endmodule