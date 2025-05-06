// Aluna: Jaqueline Ferreira de Brito
// Banco de registradores do processador MIPS

/*
 * Módulo: regfile
 * Função: Implementa o banco de 32 registradores do processador MIPS
 *
 * Características:
 * - 32 registradores de 32 bits cada (designados $0 a $31)
 * - O registrador $0 sempre contém o valor zero (hardwired)
 * - Possui 2 portas de leitura assíncronas (combinacionais)
 * - Possui 1 porta de escrita síncrona (na borda de subida do clock)
 *
 * Este é um componente crítico do datapath que fornece dados para 
 * instruções aritméticas/lógicas e armazena resultados de cálculos.
 */

// Aluna: Jaqueline Ferreira de Brito
// Data: 2025-03-20 12:38:36

module regfile (
    // Interface básica
    input  logic        clk,
    input  logic        we3,
    input  logic [4:0]  ra1, ra2,
    input  logic [4:0]  wa3,
    input  logic [31:0] wd3,
    output logic [31:0] rd1, rd2,
    
    // Novas saídas para monitoramento
    output logic [31:0] read_count,     // Contador de leituras
    output logic [31:0] write_count,    // Contador de escritas
    output logic [31:0] error_count,    // Contador de erros
    output logic [1:0]  reg_status,     // Status do regfile
    output logic [63:0] last_access_time // Timestamp do último acesso
);
    // Registradores
    logic [31:0] rf[31:0];
    
    // Definições de estado
    typedef enum logic[1:0] {
        REG_NORMAL = 2'b00,
        REG_READ   = 2'b01,
        REG_WRITE  = 2'b10,
        REG_ERROR  = 2'b11
    } reg_state_t;

    // Sinais internos
    reg_state_t current_state;
    logic [63:0] current_time;
    logic        access_error;
    logic [31:0] access_count[32];  // Contador por registrador

    // Inicialização
    initial begin
        current_time = 64'd1711801916; // 2025-03-20 12:38:36
        current_state = REG_NORMAL;
        read_count = 32'h0;
        write_count = 32'h0;
        error_count = 32'h0;
        
        for (int i = 0; i < 32; i++) begin
            rf[i] = 32'h0;
            access_count[i] = 32'h0;
        end
    end

    // Verificação de acesso válido
    always_comb begin
        access_error = 1'b0;
        
        // Verificar tentativa de escrita em $0
        if (we3 && wa3 == 5'b0)
            access_error = 1'b1;
            
        // Verificar endereços válidos
        if (ra1 >= 32 || ra2 >= 32 || wa3 >= 32)
            access_error = 1'b1;
    end

    // Escrita síncrona
    always_ff @(posedge clk) begin
        if (we3 && !access_error) begin
            if (wa3 != 0) begin
                rf[wa3] <= wd3;
                access_count[wa3] <= access_count[wa3] + 1;
                write_count <= write_count + 1;
                current_state <= REG_WRITE;
            end
        end
        
        if (access_error)
            error_count <= error_count + 1;
            
        current_time <= current_time + 1;
    end

    // Leitura assíncrona
    always_comb begin
        // Leitura porta 1
        if (ra1 == 0)
            rd1 = 32'h0;
        else if (!access_error)
            rd1 = rf[ra1];
        else
            rd1 = 32'h0;
            
        // Leitura porta 2
        if (ra2 == 0)
            rd2 = 32'h0;
        else if (!access_error)
            rd2 = rf[ra2];
        else
            rd2 = 32'h0;
            
        if (!access_error && (ra1 != 0 || ra2 != 0)) begin
            read_count = read_count + 1;
            current_state = REG_READ;
        end
    end

    // Debug logging
    `ifdef DEBUG
        always @(posedge clk) begin
            if (we3) begin
                $display("%s - Register Write:", format_timestamp(current_time));
                $display("  User: jaquedebrito");
                $display("  Register: $%0d", wa3);
                $display("  Data: 0x%h", wd3);
                if (access_error)
                    $display("  WARNING: Write error!");
            end
        end
        
        always @(ra1, ra2) begin
            $display("%s - Register Read:", format_timestamp(current_time));
            $display("  User: jaquedebrito");
            $display("  Register 1: $%0d = 0x%h", ra1, rd1);
            $display("  Register 2: $%0d = 0x%h", ra2, rd2);
            if (access_error)
                $display("  WARNING: Read error!");
        end
        
        function string format_timestamp(input logic [63:0] unix_time);
            return $sformatf("2025-03-20 12:38:%02d", unix_time % 60);
        endfunction
    `endif

    // Assertions
    `ifdef FORMAL
        // Verificar escrita em $0
        property no_write_to_zero;
            @(posedge clk) 
            we3 |-> (wa3 != 0);
        endproperty

        // Verificar leitura de $0
        property zero_register_read;
            @(ra1, ra2) 
            (ra1 == 0 |-> rd1 == 0) && (ra2 == 0 |-> rd2 == 0);
        endproperty

        // Verificar endereços válidos
        property valid_addresses;
            @(ra1, ra2, wa3) 
            (ra1 < 32) && (ra2 < 32) && (wa3 < 32);
        endproperty

        assert property (no_write_to_zero)
            else $error("Attempted write to $0");
        assert property (zero_register_read)
            else $error("$0 not reading as zero");
        assert property (valid_addresses)
            else $error("Invalid register address");

        // Coverage
        cover property (no_write_to_zero);
        cover property (zero_register_read);
        cover property (valid_addresses);
    `endif

    // Status outputs
    assign reg_status = current_state;
    assign last_access_time = current_time;

endmodule