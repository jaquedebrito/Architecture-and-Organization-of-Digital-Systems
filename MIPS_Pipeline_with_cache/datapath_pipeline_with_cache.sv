module datapath_pipeline_with_cache(
    input  logic        clk, reset,
    // Sinais de controle
    input  logic        memtoreg_id, memwrite_id, memread_id,
    input  logic        ULAsrc_id, regdst_id,
    input  logic        regwrite_id, branch_id,
    input  logic [2:0]  ULAcontrol_id,
    output logic        zero_ex,
    // Interface com memórias
    output logic [31:0] pc,
    input  logic [31:0] instr,
    output logic [31:0] ULAout_mem, writedata_mem,
    input  logic [31:0] readdata,
    // Sinais para hazards
    input  logic        stall, flush, cache_stall,
    input  logic [1:0]  forward_a, forward_b,
    // Sinais para detecção de hazards
    output logic [4:0]  rs_id, rt_id,
    output logic [4:0]  rs_ex, rt_ex, rd_ex,
    output logic [4:0]  rd_mem, rd_wb,
    output logic        regwrite_ex, regwrite_mem, regwrite_wb,
    output logic        memread_ex
);
    // ... (parte anterior do código)

    // Mux para segundo operando da ULA
    assign srcb_ex = ULAsrc_ex ? signimm_ex : write_data_ex;
    
    // ULA
    ula u(
        .a(srca_ex),
        .b(srcb_ex),
        .ULAcontrol(ULAcontrol_ex),
        .result(alu_out_ex),
        .zero(zero_ex)
    );
    
    // Mux para seleção do registrador de destino
    assign writereg_ex = regdst_ex ? rd_dest_ex : rt_dest_ex;
    
    // Registradores pipeline ID/EX
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            rd1_ex <= 32'h0;
            rd2_ex <= 32'h0;
            rs_ex <= 5'h0;
            rt_ex <= 5'h0;
            rd_ex <= 5'h0;
            rt_dest_ex <= 5'h0;
            rd_dest_ex <= 5'h0;
            signimm_ex <= 32'h0;
            pc_plus4_ex <= 32'h0;
            regwrite_ex <= 1'b0;
            memtoreg_ex <= 1'b0;
            memread_ex <= 1'b0;
            memwrite_ex <= 1'b0;
            ULAsrc_ex <= 1'b0;
            regdst_ex <= 1'b0;
            branch_ex <= 1'b0;
            ULAcontrol_ex <= 3'b000;
        end else if (!stall) begin
            rd1_ex <= rd1_id;
            rd2_ex <= rd2_id;
            rs_ex <= rs_id;
            rt_ex <= rt_id;
            rd_ex <= instr_id[15:11];
            rt_dest_ex <= instr_id[20:16];
            rd_dest_ex <= instr_id[15:11];
            signimm_ex <= signimm_id;
            pc_plus4_ex <= pc_plus4_id;
            regwrite_ex <= flush ? 1'b0 : regwrite_id;
            memtoreg_ex <= memtoreg_id;
            memread_ex <= memread_id;
            memwrite_ex <= memwrite_id;
            ULAsrc_ex <= ULAsrc_id;
            regdst_ex <= regdst_id;
            branch_ex <= branch_id;
            ULAcontrol_ex <= ULAcontrol_id;
        end
    end
    
    // Processamento do estágio MEM (acesso à memória)
    // Cálculo do endereço de branch
    assign pc_branch = pc_plus4_ex + (signimm_ex << 2);
    
    // Condição de branch
    assign pc_src = branch_ex & zero_ex;
    
    // Mux para seleção do próximo PC
    assign pc_next = pc_src ? pc_branch : pc + 4;
    
    // Registradores pipeline EX/MEM
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            ULAout_mem <= 32'h0;
            writedata_mem <= 32'h0;
            writereg_mem <= 5'h0;
            regwrite_mem <= 1'b0;
            memtoreg_mem <= 1'b0;
            memwrite_mem <= 1'b0;
            memread_mem <= 1'b0;
            branch_mem <= 1'b0;
            rd_mem <= 5'h0;
        end else if (!cache_stall) begin
            ULAout_mem <= alu_out_ex;
            writedata_mem <= write_data_ex;
            writereg_mem <= writereg_ex;
            regwrite_mem <= regwrite_ex;
            memtoreg_mem <= memtoreg_ex;
            memwrite_mem <= memwrite_ex;
            memread_mem <= memread_ex;
            branch_mem <= branch_ex;
            rd_mem <= writereg_ex;
        end
    end
    
    // Processamento do estágio WB (write back)
    // Mux para seleção do resultado a ser escrito nos registradores
    assign result_wb = memtoreg_wb ? readdata_wb : alu_out_wb;
    
    // Registradores pipeline MEM/WB
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            alu_out_wb <= 32'h0;
            readdata_wb <= 32'h0;
            writereg_wb <= 5'h0;
            regwrite_wb <= 1'b0;
            memtoreg_wb <= 1'b0;
            rd_wb <= 5'h0;
        end else if (!cache_stall) begin
            alu_out_wb <= ULAout_mem;
            readdata_wb <= readdata;
            writereg_wb <= writereg_mem;
            regwrite_wb <= regwrite_mem;
            memtoreg_wb <= memtoreg_mem;
            rd_wb <= writereg_mem;
        end
    end
    
    // Saídas para o módulo top
    assign ULAout_mem = alu_out_ex;
    assign writedata_mem = write_data_ex;
endmodule