// Aluna: Jaqueline Ferreira de Brito

`timescale 1ns/1ps

module forwarding_unit_tb;

    // Testbench configuration parameters
    localparam CLK_PERIOD = 10;
    localparam TEST_TIMEOUT = 1000;
    
    // Test control variables
    static int errors = 0;
    static int num_tests = 20;
    
    // Interface signals
    logic [4:0] rs_ex;
    logic [4:0] rt_ex;
    logic [4:0] rd_mem;
    logic [4:0] rd_wb;
    logic       regwrite_mem;
    logic       regwrite_wb;
    logic       memread_mem;
    logic       memread_wb;
    logic       clk;
    logic       rst_n;
    
    logic [1:0] forward_a;
    logic [1:0] forward_b;
    logic [1:0] forward_mem;
    logic [31:0] forward_count_a;
    logic [31:0] forward_count_b;
    logic [31:0] forward_count_mem;
    logic [1:0]  forward_status;
    logic [63:0] last_update_time;

    // DUT instantiation
    forwarding_unit dut (.*);

    // Clock generation
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end

    // Test stimulus class
    class TestVector;
        rand bit [4:0] rs_ex;
        rand bit [4:0] rt_ex;
        rand bit [4:0] rd_mem;
        rand bit [4:0] rd_wb;
        rand bit regwrite_mem;
        rand bit regwrite_wb;
        rand bit memread_mem;
        rand bit memread_wb;
        
        // Expected outputs
        bit [1:0] exp_forward_a;
        bit [1:0] exp_forward_b;
        bit [1:0] exp_forward_mem;
        
        // Constraints to improve test coverage
        constraint valid_regs {
            rs_ex inside {[0:31]};
            rt_ex inside {[0:31]};
            rd_mem inside {[0:31]};
            rd_wb inside {[0:31]};
        }
        
        // Ensure some interesting cases
        constraint interesting_cases {
            solve rd_mem, rd_wb before rs_ex, rt_ex;
            rd_mem dist {0 := 20, [1:31] := 80};
            rd_wb dist {0 := 20, [1:31] := 80};
            rs_ex inside {rd_mem, rd_wb, [0:31]};
            rt_ex inside {rd_mem, rd_wb, [0:31]};
        }
        
        function void post_randomize();
            exp_forward_a = get_expected_forward_a();
            exp_forward_b = get_expected_forward_b();
            exp_forward_mem = get_expected_forward_mem();
        endfunction
        
        function bit [1:0] get_expected_forward_a();
            if (regwrite_mem && (rd_mem != 0) && (rd_mem == rs_ex))
                return 2'b10;
            else if (regwrite_wb && (rd_wb != 0) && (rd_wb == rs_ex) &&
                     !(regwrite_mem && (rd_mem != 0) && (rd_mem == rs_ex)))
                return 2'b01;
            else
                return 2'b00;
        endfunction
        
        function bit [1:0] get_expected_forward_b();
            if (regwrite_mem && (rd_mem != 0) && (rd_mem == rt_ex))
                return 2'b10;
            else if (regwrite_wb && (rd_wb != 0) && (rd_wb == rt_ex) &&
                     !(regwrite_mem && (rd_mem != 0) && (rd_mem == rt_ex)))
                return 2'b01;
            else
                return 2'b00;
        endfunction
        
        function bit [1:0] get_expected_forward_mem();
            if (memread_mem && (rd_mem != 0) && (rd_mem == rt_ex))
                return 2'b10;
            else if (memread_wb && (rd_wb != 0) && (rd_wb == rt_ex) &&
                     !(memread_mem && (rd_mem != 0) && (rd_mem == rt_ex)))
                return 2'b01;
            else
                return 2'b00;
        endfunction
    endclass

    // Static test vector instance
    static TestVector tv = new();

    // Test execution
    initial begin
        $timeformat(-9, 2, " ns", 20);
        $display("Starting Forwarding Unit Tests at %t", $time);
        $display("Aluna: Jaqueline Brito");
        $display("Data: 20/03/2025");
        
        // Reset sequence
        rst_n = 0;
        {rs_ex, rt_ex, rd_mem, rd_wb} = '0;
        {regwrite_mem, regwrite_wb, memread_mem, memread_wb} = '0;
        errors = 0;
        
        repeat(3) @(posedge clk);
        rst_n = 1;
        
        // Test specific cases
        run_specific_test_cases();
        
        // Random test cases
        run_random_test_cases();
        
        // Test summary
        print_test_summary();
        
        $finish;
    end

    // Specific test cases task
    task run_specific_test_cases();
        // Case 1: MEM forwarding
        @(posedge clk);
        rs_ex = 5'd10; rt_ex = 5'd15; rd_mem = 5'd10;
        regwrite_mem = 1'b1; regwrite_wb = 1'b0;
        check_results(1);
        
        // Case 2: WB forwarding
        @(posedge clk);
        rd_mem = 5'd0; rd_wb = 5'd10;
        regwrite_mem = 1'b0; regwrite_wb = 1'b1;
        check_results(2);
        
        // Case 3: No forwarding needed
        @(posedge clk);
        rs_ex = 5'd20; rt_ex = 5'd25;
        rd_mem = 5'd10; rd_wb = 5'd15;
        regwrite_mem = 1'b1; regwrite_wb = 1'b1;
        check_results(3);
        
        // Case 4: Memory forwarding
        @(posedge clk);
        rt_ex = 5'd10; rd_mem = 5'd10;
        memread_mem = 1'b1; memread_wb = 1'b0;
        check_results(4);
        
        // Case 5: Double forwarding (MEM and WB)
        @(posedge clk);
        rs_ex = 5'd10; rt_ex = 5'd15;
        rd_mem = 5'd10; rd_wb = 5'd15;
        regwrite_mem = 1'b1; regwrite_wb = 1'b1;
        check_results(5);
    endtask

    // Random test cases task
    task run_random_test_cases();
        for (int i = 6; i <= num_tests; i++) begin
            @(posedge clk);
            assert(tv.randomize()) else $error("Randomization failed");
            rs_ex = tv.rs_ex;
            rt_ex = tv.rt_ex;
            rd_mem = tv.rd_mem;
            rd_wb = tv.rd_wb;
            regwrite_mem = tv.regwrite_mem;
            regwrite_wb = tv.regwrite_wb;
            memread_mem = tv.memread_mem;
            memread_wb = tv.memread_wb;
            
            check_results(i);
        end
    endtask

    // Print test summary task
    task print_test_summary();
        $display("\nTest Summary at %t", $time);
        $display("Total Tests: %0d", num_tests);
        $display("Total Errors: %0d", errors);
        $display("Coverage: %0.2f%%", (num_tests - errors) * 100.0 / num_tests);
        
        $display("\nPerformance Counters:");
        $display("Forward A Count: %0d", forward_count_a);
        $display("Forward B Count: %0d", forward_count_b);
        $display("Forward MEM Count: %0d", forward_count_mem);
        $display("Last Update Time: %0d", last_update_time);
    endtask

    // Helper task to check results
    task automatic check_results(int test_num);
        tv.rs_ex = rs_ex;
        tv.rt_ex = rt_ex;
        tv.rd_mem = rd_mem;
        tv.rd_wb = rd_wb;
        tv.regwrite_mem = regwrite_mem;
        tv.regwrite_wb = regwrite_wb;
        tv.memread_mem = memread_mem;
        tv.memread_wb = memread_wb;
        tv.post_randomize();
        
        #1; // Allow combinational logic to settle
        
        // Check forwarding outputs
        if (forward_a !== tv.exp_forward_a) begin
            $error("Test %0d: forward_a mismatch. Expected %b, Got %b", 
                   test_num, tv.exp_forward_a, forward_a);
            errors++;
        end
        
        if (forward_b !== tv.exp_forward_b) begin
            $error("Test %0d: forward_b mismatch. Expected %b, Got %b",
                   test_num, tv.exp_forward_b, forward_b);
            errors++;
        end
        
        if (forward_mem !== tv.exp_forward_mem) begin
            $error("Test %0d: forward_mem mismatch. Expected %b, Got %b",
                   test_num, tv.exp_forward_mem, forward_mem);
            errors++;
        end
        
        $display("Test %0d: forward_a=%b, forward_b=%b, forward_mem=%b, status=%b",
                 test_num, forward_a, forward_b, forward_mem, forward_status);
    endtask

    // Timeout watchdog
    initial begin
        #TEST_TIMEOUT;
        $display("ERROR: Test timeout after %0d ns", TEST_TIMEOUT);
        $finish;
    end

endmodule