# Architecture and Organization of Digital Systems

This repository serves as a comprehensive study of the design, implementation, and analysis of digital systems, exploring both theoretical and practical aspects. The focus is on understanding modern digital architectures, with a primary emphasis on MIPS processor designs and advanced topics such as System-on-Chip (SoC) and Network-on-Chip (NoC).

---

## Repository Structure

### 1. **MIPS_Pipeline**
This folder contains the implementation of a pipelined MIPS processor, showcasing the following:

- **Modules**:
  - Core components: `adder.sv`, `mux2.sv`, `mux3.sv`, `datapath_pipeline.sv`.
  - Pipeline stages: `if_stage.sv`, `id_stage.sv`, `ex_stage.sv`, `mem_stage.sv`, `wb_stage.sv`.
  - Performance enhancements: `branch_predictor.sv`, `hazard_detection_unit.sv`, `forwarding_unit.sv`.

- **Utilities**:
  - `run_sim.sh`: Script for automating simulations.
  - `types_pkg.sv`: Type definitions for the project.
  - `memfile.dat`: Memory initialization file.

- **Testbenches**:
  Comprehensive testing for each module and the entire pipeline, located in the `testbenchs` directory, such as:
  - `adder_tb.sv`
  - `datapath_tb.sv`
  - `top_pipeline_tb.sv`

Explore this folder: [MIPS_Pipeline](https://github.com/jaquedebrito/Architecture-and-Organization-of-Digital-Systems/tree/main/MIPS_Pipeline)

---

### 2. **MIPS_monociclo**
This folder contains the implementation of a single-cycle MIPS processor, featuring:

- **Modules**:
  - `controller.sv`, `datapath.sv`: Core logic for the control unit and data path.
  - `instruction_memory.sv`, `data_memory.sv`: Memory modules.
  - `top.sv`: Top-level module integrating all components.

- **Explanations**:
  - Detailed explanations for modules and results in the `explicacoes` folder, such as `adder_explicacao_resultado`.

- **Utilities**:
  - `run_sim.sh`: Script for running simulations.
  - `memfile.dat`: Memory initialization file.

- **Testbenches**:
  A variety of testbenches for modules like `mux2_tb.sv`, `controller_tb.sv`, and `datapath_tb.sv`.

Explore this folder: [MIPS_monociclo](https://github.com/jaquedebrito/Architecture-and-Organization-of-Digital-Systems/tree/main/MIPS_monociclo)

---

## Theoretical Coverage

The discipline also covered advanced theoretical topics, bridging the gap between traditional architectures and modern digital system design:

1. **IP Cores**:
   - Reusable design blocks that enable modularity and scalability in digital system design.
   - Types: Soft Cores, Firm Cores, and Hard Cores.

2. **System-on-Chip (SoC)**:
   - Integration of processors, memory, interfaces, and peripherals on a single chip.
   - Explored the evolution from ASICs to SoCs.

3. **Communication Architectures**:
   - Traditional bus systems (e.g., PCI, AMBA) and their limitations.
   - Transition to Network-on-Chip (NoC), enabling parallel communication and scalability.

4. **3D Technologies**:
   - 3D-IC (Integrated Circuits): Layered designs for improved density and performance.
   - 3D-NoC (Network-on-Chip): Combining NoC with 3D-IC for optimal communication and integration.

---

## Learning Outcomes

This repository reflects the following key outcomes for students:
1. **Practical Skills**:
   - Implementation and testing of single-cycle and pipelined MIPS processors.
   - Mastery of modular design and verification techniques.

2. **Advanced Knowledge**:
   - Understanding of IP Cores, SoCs, NoCs, and 3D technologies.
   - Insights into the evolution of digital architectures.

3. **Tool Proficiency**:
   - Use of hardware description languages (SystemVerilog) and simulation tools.
   - Automation of testing and simulation processes.

4. **Documentation and Communication**:
   - Clear documentation of designs, test results, and theoretical concepts.

---

## Contributions

Contributions are welcome! You can:
- Improve existing modules or explanations.
- Add new testbenches or features.
- Enhance documentation.
