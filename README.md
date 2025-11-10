# Architecture and Organization of Digital Systems

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![SystemVerilog](https://img.shields.io/badge/Language-SystemVerilog-blue.svg)](https://www.systemverilog.io/)
[![MIPS](https://img.shields.io/badge/Architecture-MIPS-green.svg)](https://en.wikipedia.org/wiki/MIPS_architecture)

[English](#english) | [Português](./README_PT.md)

---

## English

### 📚 Overview

This repository serves as a comprehensive study of the design, implementation, and analysis of digital systems, exploring both theoretical and practical aspects. The focus is on understanding modern digital architectures, with a primary emphasis on MIPS processor designs and advanced topics such as System-on-Chip (SoC) and Network-on-Chip (NoC).

### 🎯 Project Goals

- Implement and understand MIPS processor architectures
- Explore single-cycle and pipelined processor designs
- Study cache memory integration and optimization
- Demonstrate practical hardware design using SystemVerilog
- Provide educational resources for digital system architecture

### 🚀 Quick Start

#### Prerequisites

- **SystemVerilog Simulator**: ModelSim, QuestaSim, Icarus Verilog, or Verilator
- **Bash**: For running simulation scripts (Linux/Mac/WSL)
- **Basic knowledge**: Digital design and computer architecture concepts

#### Running Simulations

1. **Clone the repository**:
   ```bash
   git clone https://github.com/jaquedebrito/Architecture-and-Organization-of-Digital-Systems.git
   cd Architecture-and-Organization-of-Digital-Systems
   ```

2. **Navigate to desired implementation**:
   ```bash
   cd MIPS_monociclo    # For single-cycle processor
   # or
   cd MIPS_Pipeline     # For pipelined processor
   ```

3. **Run simulations**:
   ```bash
   chmod +x run_sim.sh  # Make script executable (first time only)
   ./run_sim.sh         # Run interactive simulation menu
   ```

4. **Select module to test** from the interactive menu

---

## 📁 Repository Structure

### Project Organization

```
Architecture-and-Organization-of-Digital-Systems/
├── MIPS_monociclo/              # Single-cycle MIPS processor
├── MIPS_Pipeline/               # Pipelined MIPS processor with hazard handling
├── MIPS_Pipeline_with_cache/    # Pipelined MIPS with cache memory system
├── README.md                    # This file (English)
├── README_PT.md                 # Portuguese version
├── LICENSE                      # MIT License
└── .gitignore                   # Git ignore rules
```

---

## 🔧 Implementations

### 1. MIPS_monociclo - Single-Cycle MIPS Processor

A complete implementation of a single-cycle MIPS processor featuring Harvard architecture.

**Key Features:**
- ✅ Harvard architecture with separate instruction and data memories
- ✅ Support for R-type, I-type, and J-type instructions
- ✅ Complete ALU with arithmetic and logical operations
- ✅ 32-register file (32 bits each)
- ✅ Simple control unit design

**Core Modules:**
- `controller.sv` - Main control unit
- `datapath.sv` - Data path logic
- `instruction_memory.sv` - Instruction storage
- `data_memory.sv` - Data storage
- `ula.sv` - Arithmetic Logic Unit
- `regfile.sv` - Register file
- `top.sv` - Top-level integration

**Supported Instructions:**
- **Arithmetic**: `add`, `sub`, `addi`
- **Logical**: `and`, `or`, `slt`
- **Memory**: `lw` (load word), `sw` (store word)
- **Control**: `beq` (branch if equal), `j` (jump)

📖 **[Detailed Documentation](./MIPS_monociclo/README.md)**

---

### 2. MIPS_Pipeline - Pipelined MIPS Processor

Advanced 5-stage pipelined implementation with performance optimizations and hazard handling.

**Pipeline Stages:**
1. **IF** (Instruction Fetch) - `if_stage.sv`
2. **ID** (Instruction Decode) - `id_stage.sv`
3. **EX** (Execute) - `ex_stage.sv`
4. **MEM** (Memory Access) - `mem_stage.sv`
5. **WB** (Write Back) - `wb_stage.sv`

**Performance Features:**
- ✅ **Forwarding Unit** - Data forwarding to resolve data hazards
- ✅ **Hazard Detection Unit** - Detects and handles pipeline hazards
- ✅ **Branch Predictor** - Dynamic branch prediction for improved performance
- ✅ **Performance Monitor** - Track CPI, stalls, and other metrics

**Key Modules:**
- `datapath_pipeline.sv` - Pipelined datapath
- `controller_pipeline.sv` - Pipeline control logic
- `forwarding_unit.sv` - Handles data forwarding
- `hazard_detection_unit.sv` - Detects pipeline hazards
- `branch_predictor.sv` - Branch prediction logic
- `performance_monitor.sv` - Performance tracking

**Advantages over Single-Cycle:**
- Higher throughput (multiple instructions in flight)
- Better clock frequency potential
- Improved performance with hazard mitigation

📖 **[Detailed Documentation](./MIPS_Pipeline/README.md)**

---

### 3. MIPS_Pipeline_with_cache - Pipelined MIPS with Cache

Enhanced pipelined processor with integrated cache memory system for improved memory performance.

**Cache Features:**
- ✅ **Instruction Cache (I-Cache)** - Dedicated instruction cache
- ✅ **Data Cache (D-Cache)** - Separate data cache with write-back policy
- ✅ **Cache Controller** - Manages cache operations and coherency
- ✅ **Cache Monitor** - Performance monitoring (hits, misses, etc.)
- ✅ **Main Memory Interface** - Handles cache misses

**Core Modules:**
- `icache.sv` - Instruction cache implementation
- `dcache.sv` - Data cache implementation
- `cache_controller.sv` - Cache control logic
- `cache_monitor.sv` - Performance tracking
- `main_memory.sv` - Main memory model
- `top_pipeline_with_cache.sv` - Complete system integration

**Benefits:**
- Reduced memory access latency
- Higher effective memory bandwidth
- Realistic modern processor behavior

📖 **[Detailed Documentation](./MIPS_Pipeline_with_cache/README.md)**

---

## 📖 Theoretical Coverage

The repository also demonstrates understanding of advanced theoretical concepts:

### 1. **IP Cores**
- Reusable design blocks for modularity and scalability
- Types: Soft Cores, Firm Cores, and Hard Cores
- Enables faster design iteration and verified components

### 2. **System-on-Chip (SoC)**
- Integration of processors, memory, interfaces, and peripherals on a single chip
- Evolution from ASICs to modern SoC designs
- Demonstrated through integrated processor and memory systems

### 3. **Communication Architectures**
- Traditional bus systems (e.g., PCI, AMBA) and their limitations
- Transition to Network-on-Chip (NoC) for scalability
- Parallel communication and improved bandwidth

### 4. **3D Technologies**
- **3D-IC (Integrated Circuits)**: Layered designs for improved density
- **3D-NoC (Network-on-Chip)**: Combining NoC with 3D-IC
- Benefits: reduced wire length, improved performance, lower power

---

## 🎓 Learning Outcomes

This repository demonstrates the following key competencies:

### Practical Skills
- ✅ Implementation and testing of MIPS processors (single-cycle and pipelined)
- ✅ Mastery of modular hardware design principles
- ✅ Verification techniques using SystemVerilog testbenches
- ✅ Performance analysis and optimization

### Advanced Knowledge
- ✅ Understanding of IP Cores, SoCs, NoCs, and 3D technologies
- ✅ Pipeline hazard detection and mitigation strategies
- ✅ Cache memory design and performance optimization
- ✅ Evolution and trends in digital architecture

### Tool Proficiency
- ✅ SystemVerilog hardware description language
- ✅ Simulation tools (ModelSim, QuestaSim, etc.)
- ✅ Automated testing and verification
- ✅ Performance monitoring and analysis

### Documentation and Communication
- ✅ Clear technical documentation
- ✅ Code organization and modularity
- ✅ Test results analysis and presentation

---

## 🧪 Testing and Verification

Each implementation includes comprehensive testbenches:

### Testbench Organization
```
<implementation>/
├── testbenchs/              # Directory containing all testbenches
│   ├── adder_tb.sv         # ALU adder tests
│   ├── controller_tb.sv    # Control unit tests
│   ├── datapath_tb.sv      # Datapath tests
│   └── ...                 # Other component tests
└── top_*_tb.sv             # Complete system testbench
```

### Running Tests

Use the interactive simulation script:
```bash
./run_sim.sh
```

The script provides:
- Individual module testing
- Complete system simulation
- Custom test selection
- Automated result verification

### Test Coverage

Each testbench includes:
- Normal operation test cases
- Edge case testing
- Error condition handling
- Performance metrics collection

---

## 🤝 Contributing

Contributions are welcome! Here's how you can help:

### Ways to Contribute

1. **Improve existing modules**: Optimize designs or add features
2. **Add new testbenches**: Increase test coverage
3. **Enhance documentation**: Improve clarity or add examples
4. **Fix bugs**: Report or fix issues you find
5. **Add new features**: Implement additional instructions or optimizations

### Contribution Guidelines

1. **Fork** the repository
2. **Create** a feature branch (`git checkout -b feature/amazing-feature`)
3. **Commit** your changes (`git commit -m 'Add amazing feature'`)
4. **Push** to the branch (`git push origin feature/amazing-feature`)
5. **Open** a Pull Request

### Coding Standards

- Follow existing code style and naming conventions
- Comment complex logic and important decisions
- Include testbenches for new modules
- Update documentation for significant changes

---

## 📝 License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

### MIT License Summary

✅ Commercial use  
✅ Modification  
✅ Distribution  
✅ Private use  

---

## 👤 Author

**Jaqueline Ferreira de Brito**

- GitHub: [@jaquedebrito](https://github.com/jaquedebrito)

---

## 🌟 Acknowledgments

- MIPS architecture documentation and specifications
- Computer architecture textbooks and resources
- SystemVerilog community and tools
- Open-source hardware design community

---

## 📚 References

### MIPS Architecture
- [MIPS Architecture Overview](https://en.wikipedia.org/wiki/MIPS_architecture)
- [MIPS Instruction Set](https://www.mips.com/)

### SystemVerilog
- [SystemVerilog IEEE Standard](https://standards.ieee.org/)
- [SystemVerilog Tutorial](https://www.chipverify.com/systemverilog/systemverilog-tutorial)

### Computer Architecture
- "Computer Organization and Design: The Hardware/Software Interface" by Patterson & Hennessy
- "Digital Design and Computer Architecture" by Harris & Harris

---

## 📊 Project Status

| Component | Status | Test Coverage |
|-----------|--------|---------------|
| MIPS_monociclo | ✅ Complete | High |
| MIPS_Pipeline | ✅ Complete | High |
| MIPS_Pipeline_with_cache | ✅ Complete | Medium |

---

## 🔄 Version History

- **v1.0** (March 2025) - Initial release with all three MIPS implementations
  - Single-cycle MIPS processor
  - Pipelined MIPS processor with hazard handling
  - Pipelined MIPS with cache memory

---

**Note**: For the Portuguese version of this README, please see [README_PT.md](./README_PT.md)
