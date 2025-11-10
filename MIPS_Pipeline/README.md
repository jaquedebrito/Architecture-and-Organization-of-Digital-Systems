# MIPS_Pipeline - Pipelined MIPS Processor

[English](#english) | [Português](#português)

---

## English

### Overview

This folder contains an advanced implementation of a 5-stage pipelined MIPS processor in SystemVerilog. The pipelined design significantly improves performance through instruction-level parallelism, allowing multiple instructions to be in various stages of execution simultaneously.

### Pipeline Architecture

The processor implements a classic 5-stage RISC pipeline:

1. **IF (Instruction Fetch)** - `if_stage.sv`
   - Fetches instruction from memory
   - Updates program counter (PC)

2. **ID (Instruction Decode)** - `id_stage.sv`
   - Decodes instruction
   - Reads register file
   - Generates control signals

3. **EX (Execute)** - `ex_stage.sv`
   - Performs ALU operations
   - Calculates branch targets
   - Generates ALU control signals

4. **MEM (Memory Access)** - `mem_stage.sv`
   - Accesses data memory for load/store
   - Handles memory read/write operations

5. **WB (Write Back)** - `wb_stage.sv`
   - Writes results back to register file
   - Selects data from memory or ALU

### Project Structure

```
MIPS_Pipeline/
├── Pipeline Stages
│   ├── if_stage.sv            # Instruction Fetch stage
│   ├── id_stage.sv            # Instruction Decode stage
│   ├── ex_stage.sv            # Execute stage
│   ├── mem_stage.sv           # Memory Access stage
│   └── wb_stage.sv            # Write Back stage
│
├── Pipeline Registers
│   ├── if_id_reg.sv           # IF/ID pipeline register
│   ├── id_ex_reg.sv           # ID/EX pipeline register
│   ├── ex_mem_reg.sv          # EX/MEM pipeline register
│   └── mem_wb_reg.sv          # MEM/WB pipeline register
│
├── Hazard Handling
│   ├── forwarding_unit.sv     # Data forwarding logic
│   ├── hazard_detection_unit.sv # Hazard detection and stalling
│   └── branch_predictor.sv    # Dynamic branch prediction
│
├── Core Components
│   ├── datapath_pipeline.sv   # Complete pipelined datapath
│   ├── controller_pipeline.sv # Pipeline control logic
│   ├── main_control.sv        # Main control unit
│   ├── ula_control.sv         # ALU control
│   ├── top_pipeline.sv        # Top-level integration
│   └── exception_handler.sv   # Exception handling
│
├── Memory
│   ├── instruction_memory.sv  # Instruction storage
│   └── data_memory.sv         # Data storage
│
├── Support Components
│   ├── regfile.sv             # Register file
│   ├── ula.sv                 # ALU
│   ├── adder.sv               # Adders
│   ├── mux2.sv, mux3.sv       # Multiplexers
│   ├── signext.sv             # Sign extension
│   ├── sl2.sv                 # Shifter
│   ├── flopr.sv               # Flip-flop
│   └── types_pkg.sv           # Type definitions
│
├── Performance Monitoring
│   └── performance_monitor.sv # Performance metrics tracking
│
├── Testing
│   ├── testbenchs/            # Component testbenches
│   ├── top_pipeline_tb.sv     # Complete system testbench
│   ├── branch_predictor_tb.sv # Branch predictor tests
│   ├── forwarding_unit_tb.sv  # Forwarding unit tests
│   └── memfile.dat            # Test program
│
└── Utilities
    └── run_sim.sh             # Simulation script
```

### Key Features

#### Performance Enhancements

✅ **Data Forwarding (Bypassing)**
- Forwards results directly from pipeline stages
- Eliminates most data hazard stalls
- Supports EX-to-EX and MEM-to-EX forwarding

✅ **Hazard Detection**
- Detects data hazards (RAW, WAR, WAW)
- Detects control hazards (branches, jumps)
- Inserts stalls only when necessary

✅ **Branch Prediction**
- Dynamic branch prediction
- Branch history table (BHT)
- Reduces branch penalty
- Improves overall throughput

✅ **Performance Monitoring**
- Tracks executed instructions
- Counts pipeline stalls
- Calculates CPI (Cycles Per Instruction)
- Measures branch prediction accuracy

#### Advanced Features

- Exception handling support
- Comprehensive pipeline control
- Optimized critical path
- Modular, testable design

### Pipeline Hazards and Solutions

#### 1. Data Hazards

**Problem**: Instruction depends on result from previous instruction still in pipeline.

**Solutions Implemented**:
- **Forwarding Unit**: Bypasses data from later stages to earlier stages
- **Stalling**: Inserts bubbles when forwarding is not possible (e.g., load-use hazard)

#### 2. Control Hazards

**Problem**: Branch/jump instructions affect instruction fetch.

**Solutions Implemented**:
- **Branch Prediction**: Predicts branch outcomes to reduce stalls
- **Branch Resolution**: Detects mispredictions and flushes pipeline
- **Delayed Branch**: Option to use branch delay slots

#### 3. Structural Hazards

**Problem**: Resource conflicts (avoided by design in this implementation).

**Solution**: Separate instruction and data memories (Harvard architecture)

### Running Simulations

#### Prerequisites
- SystemVerilog simulator (ModelSim, QuestaSim, Icarus Verilog, or Verilator)
- Bash shell

#### Steps

1. Navigate to this directory:
   ```bash
   cd MIPS_Pipeline
   ```

2. Make the script executable (first time only):
   ```bash
   chmod +x run_sim.sh
   ```

3. Run the simulation script:
   ```bash
   ./run_sim.sh
   ```

4. Select from the menu:
   - Test individual pipeline stages
   - Test hazard handling units
   - Test branch predictor
   - Test complete pipelined processor

### Performance Comparison

| Metric | Single-Cycle | Pipelined |
|--------|-------------|-----------|
| **CPI (ideal)** | 1.0 | ~1.0 |
| **CPI (with hazards)** | 1.0 | ~1.2-1.5 |
| **Clock Period** | Long | Short |
| **Throughput** | 1 inst/cycle | Up to 5 inst/cycle |
| **Latency** | 1 cycle | 5 cycles |

### Module Hierarchy

```
top_pipeline
├── instruction_memory
├── data_memory
├── performance_monitor
└── mips_pipeline
    ├── if_stage
    │   ├── instruction_memory interface
    │   └── PC logic
    ├── if_id_reg
    ├── id_stage
    │   ├── regfile
    │   ├── main_control
    │   └── signext
    ├── id_ex_reg
    ├── ex_stage
    │   ├── ula
    │   ├── ula_control
    │   └── adder (branch target)
    ├── ex_mem_reg
    ├── mem_stage
    │   └── data_memory interface
    ├── mem_wb_reg
    ├── wb_stage
    ├── forwarding_unit
    ├── hazard_detection_unit
    └── branch_predictor
```

### Testbenches

Comprehensive testbenches are provided for:

- Individual pipeline stages (IF, ID, EX, MEM, WB)
- Forwarding unit logic
- Hazard detection mechanisms
- Branch predictor accuracy
- Complete pipelined system
- Performance metrics validation

---

## Português

### Visão Geral

Esta pasta contém uma implementação avançada de um processador MIPS pipeline de 5 estágios em SystemVerilog. O design pipeline melhora significativamente o desempenho através de paralelismo em nível de instrução, permitindo que múltiplas instruções estejam em vários estágios de execução simultaneamente.

### Arquitetura Pipeline

O processador implementa um pipeline RISC clássico de 5 estágios:

1. **IF (Instruction Fetch - Busca de Instrução)** - `if_stage.sv`
   - Busca instrução da memória
   - Atualiza contador de programa (PC)

2. **ID (Instruction Decode - Decodificação)** - `id_stage.sv`
   - Decodifica instrução
   - Lê banco de registradores
   - Gera sinais de controle

3. **EX (Execute - Execução)** - `ex_stage.sv`
   - Realiza operações da ULA
   - Calcula alvos de desvio
   - Gera sinais de controle da ULA

4. **MEM (Memory Access - Acesso à Memória)** - `mem_stage.sv`
   - Acessa memória de dados para load/store
   - Gerencia operações de leitura/escrita

5. **WB (Write Back - Escrita de Volta)** - `wb_stage.sv`
   - Escreve resultados de volta ao banco de registradores
   - Seleciona dados da memória ou ULA

### Características Principais

#### Melhorias de Desempenho

✅ **Encaminhamento de Dados (Bypassing)**
- Encaminha resultados diretamente dos estágios do pipeline
- Elimina maioria dos stalls por hazards de dados
- Suporta forwarding EX-para-EX e MEM-para-EX

✅ **Detecção de Hazards**
- Detecta hazards de dados (RAW, WAR, WAW)
- Detecta hazards de controle (desvios, saltos)
- Insere stalls apenas quando necessário

✅ **Predição de Desvios**
- Predição dinâmica de desvios
- Tabela de histórico de desvios (BHT)
- Reduz penalidade de desvios
- Melhora throughput geral

✅ **Monitoramento de Desempenho**
- Rastreia instruções executadas
- Conta stalls do pipeline
- Calcula CPI (Ciclos Por Instrução)
- Mede precisão da predição de desvios

### Hazards de Pipeline e Soluções

#### 1. Hazards de Dados

**Problema**: Instrução depende de resultado de instrução anterior ainda no pipeline.

**Soluções Implementadas**:
- **Unidade de Forwarding**: Desvia dados de estágios posteriores para anteriores
- **Stalling**: Insere bolhas quando forwarding não é possível

#### 2. Hazards de Controle

**Problema**: Instruções de desvio/salto afetam busca de instruções.

**Soluções Implementadas**:
- **Predição de Desvios**: Prevê resultados de desvios para reduzir stalls
- **Resolução de Desvios**: Detecta predições erradas e limpa pipeline
- **Delayed Branch**: Opção de usar slots de atraso de desvio

### Executando Simulações

Veja a seção em inglês acima para instruções detalhadas.

### Comparação de Desempenho

| Métrica | Monociclo | Pipeline |
|---------|-----------|----------|
| **CPI (ideal)** | 1.0 | ~1.0 |
| **CPI (com hazards)** | 1.0 | ~1.2-1.5 |
| **Período de Clock** | Longo | Curto |
| **Throughput** | 1 inst/ciclo | Até 5 inst/ciclo |
| **Latência** | 1 ciclo | 5 ciclos |

---

**For more detailed information, see the `readme` file in this directory (Portuguese).**
