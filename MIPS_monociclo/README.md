# MIPS_monociclo - Single-Cycle MIPS Processor

[English](#english) | [Português](#português)

---

## English

### Overview

This folder contains a complete implementation of a single-cycle MIPS processor in SystemVerilog, following the Harvard architecture with separate memories for instructions and data. The processor supports a basic set of MIPS instructions, including arithmetic and logical operations, memory load/store, and branch/jump instructions.

### Architecture

The processor implements a single-cycle architecture where each instruction executes in one clock cycle through the following stages:

1. **Fetch**: Retrieve instruction from memory
2. **Decode**: Interpret instruction and configure control signals
3. **Execute**: Perform operation in the ALU
4. **Memory**: Read or write to data memory (if needed)
5. **Write Back**: Write result to register file (if needed)

### Project Structure

```
MIPS_monociclo/
├── Core Modules
│   ├── controller.sv           # Main control unit
│   ├── datapath.sv            # Data path logic
│   ├── instruction_memory.sv  # Instruction storage
│   ├── data_memory.sv         # Data storage
│   └── top.sv                 # Top-level integration
│
├── ALU Components
│   ├── ula.sv                 # Arithmetic Logic Unit
│   └── ula_control.sv         # ALU controller
│
├── Support Components
│   ├── regfile.sv             # 32-register file
│   ├── adder.sv               # Adder modules
│   ├── mux2.sv                # 2:1 multiplexer
│   ├── signext.sv             # Sign extension
│   ├── sl2.sv                 # 2-bit left shifter
│   ├── flopr.sv               # Flip-flop with reset
│   └── main_control.sv        # Main control unit
│
├── Testing
│   ├── testbenchs/            # All testbenches
│   ├── top_tb.sv              # Complete system testbench
│   └── memfile.dat            # MIPS program for testing
│
├── Documentation
│   ├── explicacoes/           # Detailed explanations (Portuguese)
│   └── readme                 # Detailed documentation (Portuguese)
│
└── Utilities
    └── run_sim.sh             # Simulation script
```

### Supported Instructions

#### R-Type Instructions (Register Format)
- `add` - Add registers
- `sub` - Subtract registers
- `and` - Logical AND
- `or` - Logical OR
- `slt` - Set Less Than (comparison)

#### I-Type Instructions (Immediate Format)
- `addi` - Add immediate
- `lw` - Load Word (load from memory)
- `sw` - Store Word (store to memory)
- `beq` - Branch if Equal (conditional branch)

#### J-Type Instructions (Jump Format)
- `j` - Jump (unconditional jump)

### Running Simulations

#### Prerequisites
- SystemVerilog simulator (ModelSim, QuestaSim, Icarus Verilog, or Verilator)
- Bash shell

#### Steps

1. Navigate to this directory:
   ```bash
   cd MIPS_monociclo
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
   - Test individual modules
   - Test complete processor
   - Custom module selection

### Test Program (memfile.dat)

The included `memfile.dat` contains a comprehensive test program with 18 instructions that exercise all processor capabilities:

- Arithmetic operations (add, sub, addi)
- Logical operations (and, or)
- Comparisons (slt)
- Memory access (lw, sw)
- Control flow (beq, j)

See the detailed `readme` file for complete instruction breakdown and analysis.

### Key Features

✅ Harvard architecture (separate instruction and data memories)  
✅ 32-bit data path  
✅ 32 general-purpose registers  
✅ Complete ALU with 5 operations  
✅ Support for R, I, and J-type instructions  
✅ Simple single-cycle control unit  
✅ Comprehensive testbenches  

### Performance Characteristics

**Advantages:**
- Simple, straightforward design
- Easy to understand and implement
- Simplified control logic

**Limitations:**
- Clock frequency limited by slowest instruction
- Lower performance compared to pipelined designs
- Inefficient hardware utilization

### Module Hierarchy

```
top
├── instruction_memory
├── data_memory
└── mips (controller + datapath)
    ├── controller
    │   ├── main_control
    │   └── ula_control
    └── datapath
        ├── regfile
        ├── ula
        ├── adder (PC increment)
        ├── adder (branch target)
        ├── mux2 (multiple instances)
        ├── signext
        ├── sl2
        └── flopr (PC register)
```

---

## Português

### Visão Geral

Esta pasta contém uma implementação completa de um processador MIPS monociclo em SystemVerilog, seguindo a arquitetura Harvard com memórias separadas para instruções e dados. O processador suporta um conjunto básico de instruções MIPS, incluindo operações aritméticas e lógicas, carregamento/armazenamento de memória e instruções de desvio/salto.

### Arquitetura

O processador implementa uma arquitetura monociclo onde cada instrução é executada em um único ciclo de clock através dos seguintes estágios:

1. **Busca**: Obtém instrução da memória
2. **Decodificação**: Interpreta instrução e configura sinais de controle
3. **Execução**: Realiza operação na ULA
4. **Memória**: Lê ou escreve na memória de dados (se necessário)
5. **Escrita de Volta**: Escreve resultado no banco de registradores (se necessário)

### Estrutura do Projeto

Veja a seção em inglês acima para a estrutura detalhada da árvore de arquivos.

### Instruções Suportadas

#### Instruções Tipo-R (Formato de Registrador)
- `add` - Adição de registradores
- `sub` - Subtração de registradores
- `and` - AND lógico
- `or` - OR lógico
- `slt` - Set Less Than (comparação)

#### Instruções Tipo-I (Formato Imediato)
- `addi` - Adição com imediato
- `lw` - Load Word (carregamento da memória)
- `sw` - Store Word (armazenamento na memória)
- `beq` - Branch if Equal (desvio condicional)

#### Instruções Tipo-J (Formato de Salto)
- `j` - Jump (salto incondicional)

### Executando Simulações

#### Pré-requisitos
- Simulador SystemVerilog (ModelSim, QuestaSim, Icarus Verilog ou Verilator)
- Shell Bash

#### Passos

1. Navegue para este diretório:
   ```bash
   cd MIPS_monociclo
   ```

2. Torne o script executável (apenas primeira vez):
   ```bash
   chmod +x run_sim.sh
   ```

3. Execute o script de simulação:
   ```bash
   ./run_sim.sh
   ```

4. Selecione no menu:
   - Testar módulos individuais
   - Testar processador completo
   - Seleção personalizada de módulos

### Programa de Teste (memfile.dat)

O arquivo `memfile.dat` incluído contém um programa de teste abrangente com 18 instruções que exercitam todas as capacidades do processador:

- Operações aritméticas (add, sub, addi)
- Operações lógicas (and, or)
- Comparações (slt)
- Acesso à memória (lw, sw)
- Controle de fluxo (beq, j)

Veja o arquivo `readme` detalhado para análise completa das instruções.

### Características Principais

✅ Arquitetura Harvard (memórias separadas para instruções e dados)  
✅ Caminho de dados de 32 bits  
✅ 32 registradores de uso geral  
✅ ULA completa com 5 operações  
✅ Suporte para instruções tipo-R, I e J  
✅ Unidade de controle monociclo simples  
✅ Testbenches abrangentes  

### Características de Desempenho

**Vantagens:**
- Design simples e direto
- Fácil de entender e implementar
- Lógica de controle simplificada

**Limitações:**
- Frequência de clock limitada pela instrução mais lenta
- Menor desempenho comparado a designs pipeline
- Utilização ineficiente de hardware

### Hierarquia de Módulos

```
top
├── instruction_memory
├── data_memory
└── mips (controller + datapath)
    ├── controller
    │   ├── main_control
    │   └── ula_control
    └── datapath
        ├── regfile
        ├── ula
        ├── adder (incremento do PC)
        ├── adder (alvo de desvio)
        ├── mux2 (múltiplas instâncias)
        ├── signext
        ├── sl2
        └── flopr (registrador PC)
```

---

**For more detailed information, see the `readme` file in this directory (Portuguese).**
