// Aluna: Jaqueline Ferreira de Brito
// Testbench para o controlador do processador MIPS

/*
 * Módulo: controller_tb
 * Função: Testar a funcionalidade do módulo controller
 *
 * Este testbench verifica se o controlador gera corretamente todos os sinais de controle
 * para diferentes tipos de instruções (R-type, lw, sw, beq) e condições (zero=0, zero=1).
 * Cada caso de teste define os valores esperados para os sinais de controle e verifica
 * se o módulo produz os valores corretos.
 */

module controller_tb;
    // Sinais de teste
    logic [5:0] op, funct;
    logic zero;
    logic memtoreg, memwrite;
    logic memread;
    logic pcsrc, ULAsrc;
    logic regdst, regwrite;
    logic [2:0] ULAcontrol;

    // Instância do módulo sob teste
    controller DUT(
        .op(op),
        .funct(funct),
        .zero(zero),
        .memtoreg(memtoreg),
        .memwrite(memwrite),
        .memread(memread),
        .pcsrc(pcsrc),
        .ULAsrc(ULAsrc),
        .regdst(regdst),
        .regwrite(regwrite),
        .ULAcontrol(ULAcontrol)
    );

    // Task para verificação dos sinais de controle
    task check_output(
        input string test_name,
        input logic [5:0] op_in,
        input logic [5:0] funct_in,
        input logic zero_in,
        input logic exp_memtoreg,
        input logic exp_memwrite,
        input logic exp_memread,
        input logic exp_pcsrc,
        input logic exp_ULAsrc,
        input logic exp_regdst,
        input logic exp_regwrite,
        input logic [2:0] exp_ULAcontrol
    );
        // Aplicar entradas
        op = op_in;
        funct = funct_in;
        zero = zero_in;
        #5; // Aguardar estabilização das saídas
        
        $display("\n=== Testing %s ===", test_name);
        $display("Inputs:");
        $display("  op    = %b", op);
        $display("  funct = %b", funct);
        $display("  zero  = %b", zero);
        
        /* 
         * "v" (válido/passou): indica que o teste passou (valor atual corresponde ao esperado)
         * "x" (inválido/falhou): indica que o teste falhou (valor atual não corresponde ao esperado)
         */
        
        $display("\nControl Signals:");
        $display("Signal    | Expected | Actual | Status");
        $display("----------|----------|--------|--------");
        $display("memtoreg  |    %b     |    %b    |   %s", exp_memtoreg, memtoreg, 
                 memtoreg === exp_memtoreg ? "v" : "x");
        $display("memwrite  |    %b     |    %b    |   %s", exp_memwrite, memwrite,
                 memwrite === exp_memwrite ? "v" : "x");
        $display("memread   |    %b     |    %b    |   %s", exp_memread, memread,
                 memread === exp_memread ? "v" : "x");
        $display("pcsrc     |    %b     |    %b    |   %s", exp_pcsrc, pcsrc,
                 pcsrc === exp_pcsrc ? "v" : "x");
        $display("ULAsrc    |    %b     |    %b    |   %s", exp_ULAsrc, ULAsrc,
                 ULAsrc === exp_ULAsrc ? "v" : "x");
        $display("regdst    |    %b     |    %b    |   %s", exp_regdst, regdst,
                 regdst === exp_regdst ? "v" : "x");
        $display("regwrite  |    %b     |    %b    |   %s", exp_regwrite, regwrite,
                 regwrite === exp_regwrite ? "v" : "x");
        $display("ULAcontrol|   %b    |   %b   |   %s", exp_ULAcontrol, ULAcontrol,
                 ULAcontrol === exp_ULAcontrol ? "v" : "x");
        
        // Verificações formais (assertions)
        assert(memtoreg === exp_memtoreg) else $error("%s: memtoreg mismatch", test_name);
        assert(memwrite === exp_memwrite) else $error("%s: memwrite mismatch", test_name);
        assert(memread === exp_memread) else $error("%s: memread mismatch", test_name);
        assert(pcsrc === exp_pcsrc) else $error("%s: pcsrc mismatch", test_name);
        assert(ULAsrc === exp_ULAsrc) else $error("%s: ULAsrc mismatch", test_name);
        assert(regdst === exp_regdst) else $error("%s: regdst mismatch", test_name);
        assert(regwrite === exp_regwrite) else $error("%s: regwrite mismatch", test_name);
        assert(ULAcontrol === exp_ULAcontrol) else $error("%s: ULAcontrol mismatch", test_name);
    endtask

    // Procedimento de teste
    initial begin
        $display("\n=== Controller Testbench ===");

        // Test Case 1: R-type ADD (zero=0)
        check_output(
            "R-type ADD (zero=0)",
            6'b000000,  // op
            6'b100000,  // funct (add)
            1'b0,       // zero
            1'b0,       // memtoreg
            1'b0,       // memwrite
            1'b0,       // memread
            1'b0,       // pcsrc
            1'b0,       // ULAsrc
            1'b1,       // regdst
            1'b1,       // regwrite
            3'b010      // ULAcontrol (add)
        );

        // Test Case 2: R-type SUB (zero=1)
        check_output(
            "R-type SUB (zero=1)",
            6'b000000,  // op
            6'b100010,  // funct (sub)
            1'b1,       // zero
            1'b0,       // memtoreg
            1'b0,       // memwrite
            1'b0,       // memread
            1'b0,       // pcsrc
            1'b0,       // ULAsrc
            1'b1,       // regdst
            1'b1,       // regwrite
            3'b110      // ULAcontrol (sub)
        );

        // Test Case 3: LW
        check_output(
            "LW",
            6'b100011,  // op
            6'bxxxxxx,  // funct (don't care)
            1'b0,       // zero
            1'b1,       // memtoreg
            1'b0,       // memwrite
            1'b1,       // memread
            1'b0,       // pcsrc
            1'b1,       // ULAsrc
            1'b0,       // regdst
            1'b1,       // regwrite
            3'b010      // ULAcontrol (add)
        );

        // Test Case 4: SW
        check_output(
            "SW",
            6'b101011,  // op
            6'bxxxxxx,  // funct (don't care)
            1'b0,       // zero
            1'bx,       // memtoreg (don't care)
            1'b1,       // memwrite
            1'b0,       // memread
            1'b0,       // pcsrc
            1'b1,       // ULAsrc
            1'bx,       // regdst (don't care)
            1'b0,       // regwrite
            3'b010      // ULAcontrol (add)
        );

        // Test Case 5: BEQ (zero=0, não toma desvio)
        check_output(
            "BEQ (zero=0)",
            6'b000100,  // op
            6'bxxxxxx,  // funct (don't care)
            1'b0,       // zero
            1'bx,       // memtoreg (don't care)
            1'b0,       // memwrite
            1'b0,       // memread
            1'b0,       // pcsrc
            1'b0,       // ULAsrc
            1'bx,       // regdst (don't care)
            1'b0,       // regwrite
            3'b110      // ULAcontrol (sub)
        );

        // Test Case 6: BEQ (zero=1, toma desvio)
        check_output(
            "BEQ (zero=1)",
            6'b000100,  // op
            6'bxxxxxx,  // funct (don't care)
            1'b1,       // zero
            1'bx,       // memtoreg (don't care)
            1'b0,       // memwrite
            1'b0,       // memread
            1'b1,       // pcsrc
            1'b0,       // ULAsrc
            1'bx,       // regdst (don't care)
            1'b0,       // regwrite
            3'b110      // ULAcontrol (sub)
        );

        $display("\n=== Test Summary ===");
        $display("Total test cases: 6");
        $display("Completed testbench");
        $display("===================\n");
        $finish;
    end

endmodule