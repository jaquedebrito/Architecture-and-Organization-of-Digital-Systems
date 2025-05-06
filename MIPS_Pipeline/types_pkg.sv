package types_pkg;
    typedef enum logic[1:0] {
        PROC_NORMAL = 2'b00,
        PROC_STALL  = 2'b01,
        PROC_FLUSH  = 2'b10,
        PROC_ERROR  = 2'b11
    } proc_state_t;
endpackage