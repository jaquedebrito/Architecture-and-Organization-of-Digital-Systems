module top_pipeline_with_cache_monitor(
    input  logic        clk, reset,
    output logic [31:0] writedata, dataadr,
    output logic        memwrite
);
    logic [31:0] pc, instr, readdata;
    
    // Sinais para cache
    logic        i_ready, d_ready;
    logic        i_hit, d_hit;
    logic        i_read, d_read, d_write;
    
    // Instância do processador com cache
    top_pipeline_with_cache processor(
        .clk(clk),
        .reset(reset),
        .writedata(writedata),
        .dataadr(dataadr),
        .memwrite(memwrite),
        .i_ready(i_ready),
        .d_ready(d_ready),
        .i_hit(i_hit),
        .d_hit(d_hit),
        .i_read(i_read),
        .d_read(d_read),
        .d_write(d_write)
    );
    
    // Instância do monitor de cache
    cache_monitor monitor(
        .clk(clk),
        .reset(reset),
        .i_read(i_read),
        .d_read(d_read),
        .d_write(d_write),
        .i_hit(i_hit),
        .d_hit(d_hit),
        .i_ready(i_ready),
        .d_ready(d_ready)
    );
endmodule