module controller_pipeline_with_cache(
    input  logic [5:0] op, funct,
    input  logic       zero_ex,
    // Registradores para detecção de hazards
    input  logic [4:0] rs_id, rt_id,
    input  logic [4:0] rs_ex, rt_ex, rd_ex,
    input  logic [4:0] rd_mem, rd_wb,
    input  logic       regwrite_ex, regwrite_mem, regwrite_wb,
    input  logic       memread_ex,
    // Cache signals
    input  logic       i_cache_ready,
    input  logic       d_cache_ready,
    // Saídas de controle para ID
    output logic       memtoreg_id, memwrite_id, memread_id,
    output logic       branch_id,
    output logic       ULAsrc_id, regdst_id,
    output logic       regwrite_id,
    output logic [2:0] ULAcontrol_id,
    // Saídas para hazard handling
    output logic       stall, flush,
    output logic [1:0] forward_a, forward_b,
    // Nova saída para stall devido a cache miss
    output logic       cache_stall
);
    logic [1:0] ULAop_id;
    logic       hazard_stall;  // Stall devido a hazards de dados

    // Unidade de controle principal
    main_control mc(
        .op(op),
        .memread(memread_id),
        .memtoreg(memtoreg_id),
        .memwrite(memwrite_id),
        .branch(branch_id),
        .ULAsrc(ULAsrc_id),
        .regdst(regdst_id),
        .regwrite(regwrite_id),
        .ULAop(ULAop_id)
    );

    // Unidade de controle da ULA
    ula_control uc(
        .funct(funct),
        .ULAop(ULAop_id),
        .ULAcontrol(ULAcontrol_id)
    );
    
    // Instanciar unidade de forwarding
    forwarding_unit fu(
        .rs_id_ex(rs_ex),
        .rt_id_ex(rt_ex), 
        .rd_ex_mem(rd_mem),
        .rd_mem_wb(rd_wb),
        .regwrite_ex_mem(regwrite_mem),
        .regwrite_mem_wb(regwrite_wb),
        .forward_a(forward_a),
        .forward_b(forward_b)
    );

    // Instanciar unidade de detecção de hazards
    hazard_detection_unit hdu(
        .rs_if_id(rs_id),
        .rt_if_id(rt_id),
        .rt_id_ex(rt_ex),
        .memread_id_ex(memread_ex),
        .branch_id(branch_id),
        .zero_ex(zero_ex),
        .stall(hazard_stall),
        .flush(flush)
    );
    
    // Stall devido a cache miss
    assign cache_stall = !i_cache_ready || (memread_id && !d_cache_ready) || (memwrite_id && !d_cache_ready);
    
    // Stall combinado (hazards de dados ou cache miss)
    assign stall = hazard_stall || cache_stall;
    
endmodule