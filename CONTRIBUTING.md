# Contributing to Architecture and Organization of Digital Systems

First off, thank you for considering contributing to this project! It's people like you that make this educational repository a great learning resource.

## 🌟 Ways to Contribute

### 1. Report Bugs
If you find a bug, please create an issue with:
- Clear description of the problem
- Steps to reproduce
- Expected vs actual behavior
- SystemVerilog simulator version
- Any relevant error messages

### 2. Suggest Enhancements
We welcome suggestions for:
- New processor features
- Additional instructions
- Performance optimizations
- Documentation improvements
- Better testbenches

### 3. Submit Pull Requests
We actively welcome pull requests for:
- Bug fixes
- New features
- Documentation improvements
- Test coverage improvements
- Code optimizations

## 📋 Pull Request Process

### Before You Start

1. **Check existing issues and PRs** to avoid duplicating work
2. **Discuss major changes** by opening an issue first
3. **Fork the repository** and create a branch from `main`

### Development Workflow

1. **Create a feature branch**:
   ```bash
   git checkout -b feature/your-feature-name
   ```

2. **Make your changes**:
   - Follow the existing code style
   - Add comments for complex logic
   - Update documentation if needed
   - Add tests for new features

3. **Test your changes**:
   ```bash
   cd <implementation_folder>
   ./run_sim.sh
   # Test relevant modules
   ```

4. **Commit your changes**:
   ```bash
   git add .
   git commit -m "Brief description of changes"
   ```
   
   Use clear, descriptive commit messages:
   - ✅ "Add branch prediction to pipeline"
   - ✅ "Fix data hazard in forwarding unit"
   - ❌ "Update files"
   - ❌ "Fix bug"

5. **Push to your fork**:
   ```bash
   git push origin feature/your-feature-name
   ```

6. **Open a Pull Request**:
   - Provide clear description of changes
   - Reference any related issues
   - Include test results if applicable

## 💻 Coding Standards

### SystemVerilog Style Guide

#### Naming Conventions

- **Modules**: lowercase with underscores
  ```systemverilog
  module data_memory(...);
  ```

- **Signals**: descriptive, lowercase with underscores
  ```systemverilog
  logic [31:0] instruction_data;
  logic        reg_write_enable;
  ```

- **Constants**: UPPERCASE with underscores
  ```systemverilog
  parameter ADDR_WIDTH = 32;
  ```

#### Code Organization

```systemverilog
module example_module #(
    parameter WIDTH = 32
) (
    input  logic             clk,
    input  logic             reset,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);

    // Internal signals
    logic [WIDTH-1:0] internal_reg;
    
    // Sequential logic
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            internal_reg <= '0;
        else
            internal_reg <= data_in;
    end
    
    // Combinational logic
    always_comb begin
        data_out = internal_reg;
    end

endmodule
```

#### Best Practices

1. **Use `always_ff` and `always_comb`** instead of `always @`
2. **Avoid latches** - ensure all combinational outputs are assigned in all paths
3. **Use non-blocking assignments (`<=`)** in sequential logic
4. **Use blocking assignments (`=`)** in combinational logic
5. **Add meaningful comments** for complex logic
6. **Keep modules focused** - one clear purpose per module
7. **Use parameters** for configurable values

### Testbench Standards

#### Testbench Structure

```systemverilog
module example_tb;

    // Testbench signals
    logic clk;
    logic reset;
    logic [31:0] test_data;
    
    // Instantiate module under test
    example_module dut (
        .clk(clk),
        .reset(reset),
        .data_in(test_data),
        .data_out(result_data)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Test stimulus
    initial begin
        // Initialize
        reset = 1;
        test_data = 0;
        #10 reset = 0;
        
        // Test case 1
        test_data = 32'h12345678;
        #10;
        assert(result_data == expected) 
            else $error("Test 1 failed");
        
        // Test case 2
        // ...
        
        $display("All tests passed!");
        $finish;
    end

endmodule
```

#### Testbench Requirements

- ✅ Test normal operation
- ✅ Test edge cases
- ✅ Test error conditions
- ✅ Use assertions for verification
- ✅ Provide clear pass/fail messages
- ✅ Clean up (finish simulation properly)

## 📚 Documentation Standards

### Code Documentation

- **Module headers**: Describe purpose, parameters, interfaces
- **Complex logic**: Explain the "why", not just the "what"
- **Algorithms**: Document the approach and reasoning

Example:
```systemverilog
// Branch Predictor Module
// 
// Implements a 2-bit saturating counter branch predictor
// to reduce branch penalty in the pipeline.
//
// Parameters:
//   - BHT_SIZE: Size of branch history table (entries)
//
// Algorithm:
//   - Uses lower bits of PC to index into BHT
//   - 2-bit counter: 00, 01 = not taken, 10, 11 = taken
//   - Updates counter on branch resolution
module branch_predictor #(
    parameter BHT_SIZE = 256
) (
    // ...
);
```

### README Updates

When adding new features, update relevant README files:
- Main repository README
- Implementation-specific README
- Portuguese version (README_PT.md)

## 🧪 Testing Requirements

### Before Submitting PR

1. **Run all relevant testbenches**:
   ```bash
   ./run_sim.sh
   # Select "Test All" option
   ```

2. **Verify no regressions**:
   - Existing tests should still pass
   - No new warnings or errors

3. **Add tests for new features**:
   - Create testbench for new modules
   - Add test cases to existing testbenches

### Test Coverage Goals

- **Module level**: 100% of modules should have testbenches
- **Functionality**: All features should be tested
- **Edge cases**: Important edge cases should be covered

## 📝 Commit Message Guidelines

### Format

```
<type>: <subject>

<body>

<footer>
```

### Types

- **feat**: New feature
- **fix**: Bug fix
- **docs**: Documentation changes
- **style**: Code style changes (formatting, etc.)
- **refactor**: Code refactoring
- **test**: Adding or updating tests
- **chore**: Maintenance tasks

### Examples

```
feat: Add write-back cache to pipeline

Implement write-back policy for data cache to reduce
memory bandwidth usage. Includes dirty bit tracking
and write-back buffer.

Closes #123
```

```
fix: Correct forwarding unit data hazard detection

The forwarding unit was not detecting WAW hazards correctly.
Updated hazard detection logic to check destination registers
in both EX and MEM stages.
```

## 🤝 Code Review Process

### What to Expect

1. **Initial review**: Within 1-2 weeks
2. **Feedback**: Constructive comments and suggestions
3. **Iteration**: You may be asked to make changes
4. **Approval**: Once all feedback is addressed
5. **Merge**: Maintainer will merge your PR

### Review Criteria

- ✅ Code follows style guidelines
- ✅ Changes are well-tested
- ✅ Documentation is updated
- ✅ No regressions introduced
- ✅ Commit messages are clear
- ✅ PR description is comprehensive

## ❓ Questions?

If you have questions:

1. **Check existing documentation** in README files
2. **Search existing issues** for similar questions
3. **Open a new issue** with the "question" label

## 📜 Code of Conduct

### Our Pledge

We are committed to providing a welcoming and inspiring community for all.

### Our Standards

**Positive behaviors:**
- Using welcoming and inclusive language
- Being respectful of differing viewpoints
- Gracefully accepting constructive criticism
- Focusing on what is best for the community
- Showing empathy towards other community members

**Unacceptable behaviors:**
- Harassment of any kind
- Trolling or insulting comments
- Public or private harassment
- Publishing others' private information
- Other conduct which could reasonably be considered inappropriate

## 🎓 Learning Resources

If you're new to:

### SystemVerilog
- [SystemVerilog Tutorial](https://www.chipverify.com/systemverilog/systemverilog-tutorial)
- [IEEE SystemVerilog Standard](https://standards.ieee.org/)

### MIPS Architecture
- [MIPS Architecture Guide](https://en.wikipedia.org/wiki/MIPS_architecture)
- "Computer Organization and Design" by Patterson & Hennessy

### Digital Design
- "Digital Design and Computer Architecture" by Harris & Harris
- Online courses on computer architecture

## 🌟 Recognition

Contributors will be:
- Listed in the project's acknowledgments
- Credited in relevant commit messages
- Appreciated by the community! 🎉

---

Thank you for contributing to making this educational resource better for everyone!
