module top_pipeline_with_cache(
    input  logic        clk, reset,
    output logic [31:0] writedata, dataadr,
    output logic        memwrite
);
    logic [31:0] pc, instr, readdata;
    logic        zero_ex;
    
    // Sinais para cache
    logic        i_ready, d_ready;
    logic [31:0] mem_addr, mem_write_data, mem_read_data;
    logic        mem_read, mem_write, mem_ready;

    // Sinais de controle
    logic        memtoreg_id, memwrite_id, memread_id;
    logic        ULAsrc_id, regdst_id;
    logic        regwrite_id, branch_id;
    logic [2:0]  ULAcontrol_id;

    // Instância do processador pipeline
    top_pipeline processor(
        .clk(clk),
        .reset(reset),
        .writedata(writedata),
        .dataadr(dataadr),
        .memwrite(memwrite),
        .pc(pc),
        .instr(instr),
        .readdata(readdata),
        .zero_ex(zero_ex),
        .memtoreg_id(memtoreg_id),
        .memwrite_id(memwrite_id),
        .memread_id(memread_id),
        .ULAsrc_id(ULAsrc_id),
        .regdst_id(regdst_id),
        .regwrite_id(regwrite_id),
        .branch_id(branch_id),
        .ULAcontrol_id(ULAcontrol_id)
    );

    // Instância do controlador de cache
    cache_controller cache_ctrl(
        .clk(clk),
        .reset(reset),
        // Interface com o processador (instruções)
        .i_addr(pc),
        .i_data(instr),
        .i_read(1'b1),  // Sempre lendo instruções
        .i_ready(i_ready),
        // Interface com o processador (dados)
        .d_addr(dataadr),
        .d_write_data(writedata),
        .d_read_data(readdata),
        .d_read(memread_id),
        .d_write(memwrite_id),
        .d_ready(d_ready),
        // Interface com a memória principal
        .mem_addr(mem_addr),
        .mem_write_data(mem_write_data),
        .mem_read_data(mem_read_data),
        .mem_read(mem_read),
        .mem_write(mem_write),
        .mem_ready(mem_ready)
    );

    // Memória principal (mais lenta que a cache)
    main_memory main_mem(
        .clk(clk),
        .reset(reset),
        .addr(mem_addr),
        .write_data(mem_write_data),
        .read_data(mem_read_data),
        .read(mem_read),
        .write(mem_write),
        .ready(mem_ready)
    );
endmodule