# MIPS_Pipeline_with_cache - Pipelined MIPS with Cache Memory

[English](#english) | [Português](#português)

---

## English

### Overview

This folder contains an enhanced pipelined MIPS processor with an integrated cache memory system. This implementation demonstrates how cache memory improves processor performance by reducing memory access latency and increasing effective memory bandwidth.

### Cache Architecture

The implementation features a two-level memory hierarchy:

1. **L1 Caches** (on-chip, fast)
   - **Instruction Cache (I-Cache)**: Dedicated cache for instructions
   - **Data Cache (D-Cache)**: Separate cache for data with write-back policy

2. **Main Memory** (off-chip, slower)
   - Handles cache misses
   - Stores complete program and data

### Project Structure

```
MIPS_Pipeline_with_cache/
├── Cache Components
│   ├── icache.sv              # Instruction cache
│   ├── dcache.sv              # Data cache with write-back
│   ├── cache_controller.sv    # Cache control logic
│   ├── cache_monitor.sv       # Performance monitoring
│   └── main_memory.sv         # Main memory model
│
├── Processor Components
│   ├── datapath_pipeline_with_cache.sv    # Modified datapath
│   ├── controller_pipeline_with_cache.sv  # Modified controller
│   └── top_pipeline_with_cache.sv         # Top-level integration
│
└── Support Components
    └── multicycle_alu.sv      # Multi-cycle ALU for cache operations
```

### Cache Design Details

#### Instruction Cache (I-Cache)

**Specifications:**
- **Type**: Direct-mapped or N-way set associative
- **Size**: Configurable (typically 4KB - 16KB)
- **Block Size**: 32 bytes (8 words)
- **Policy**: Read-only (instructions don't change during execution)

**Features:**
- Fast single-cycle hit
- Multi-cycle miss handling
- Prefetching support (optional)
- Simple replacement (no write-back needed)

#### Data Cache (D-Cache)

**Specifications:**
- **Type**: Direct-mapped or N-way set associative
- **Size**: Configurable (typically 4KB - 16KB)
- **Block Size**: 32 bytes (8 words)
- **Write Policy**: Write-back with write-allocate
- **Replacement**: LRU or FIFO (for associative caches)

**Features:**
- Single-cycle hit for reads and writes
- Multi-cycle miss handling
- Dirty bit tracking for write-back
- Write buffer (optional)

### Cache Controller

The cache controller manages all cache operations:

**Responsibilities:**
- **Hit/Miss Detection**: Determines if requested data is in cache
- **Cache Line Replacement**: Selects victim line on misses
- **Write-Back Handling**: Writes dirty lines to main memory
- **Coherency**: Ensures data consistency (if needed)

**States:**
- IDLE: Ready for new request
- COMPARE: Check for hit/miss
- ALLOCATE: Fetch data from main memory
- WRITE_BACK: Write dirty line to memory

### Cache Monitor

Tracks performance metrics:

**Metrics Collected:**
- Total cache accesses
- Cache hits and misses
- Hit rate percentage
- Miss penalty cycles
- Write-backs performed
- Average memory access time (AMAT)

**Formula:**
```
AMAT = Hit Time + (Miss Rate × Miss Penalty)
```

### Key Features

✅ **Separate I-Cache and D-Cache**
- Harvard architecture benefits
- Simultaneous instruction and data access
- Independent optimization of each cache

✅ **Write-Back Policy**
- Reduces memory bandwidth usage
- Better performance than write-through
- Requires dirty bit tracking

✅ **Configurable Cache Parameters**
- Adjustable cache size
- Configurable associativity
- Flexible block size

✅ **Performance Monitoring**
- Real-time hit/miss tracking
- Detailed statistics collection
- Performance analysis support

### Cache Performance Impact

#### Without Cache (Direct Memory Access)
- **Memory Access Time**: 100+ cycles (typical)
- **Instruction Fetch**: 100 cycles each
- **Data Access**: 100 cycles each
- **Effective CPI**: Very high (>100)

#### With Cache (This Implementation)
- **Cache Hit Time**: 1 cycle
- **Cache Miss Penalty**: 10-50 cycles (depending on memory)
- **Typical Hit Rate**: 90-99%
- **Effective CPI**: ~1.5-3.0

**Example Performance Calculation:**
```
Assumptions:
- Hit Rate: 95%
- Hit Time: 1 cycle
- Miss Penalty: 20 cycles

AMAT = 1 + (0.05 × 20) = 2 cycles
Speedup vs. no cache = 100 / 2 = 50x
```

### Integration with Pipeline

The cache system integrates with the pipeline as follows:

**Instruction Fetch (IF Stage):**
- Accesses I-Cache instead of direct memory
- Stalls pipeline on I-Cache miss
- Continues normally on I-Cache hit

**Memory Access (MEM Stage):**
- Accesses D-Cache for load/store
- Stalls pipeline on D-Cache miss
- Handles write-back if needed

**Pipeline Stalls:**
- Cache miss causes pipeline stall
- All stages freeze until data arrives
- Performance monitor tracks stall cycles

### Module Hierarchy

```
top_pipeline_with_cache
├── icache
│   ├── Tag memory
│   ├── Data memory
│   └── Valid bits
├── dcache
│   ├── Tag memory
│   ├── Data memory
│   ├── Valid bits
│   └── Dirty bits
├── cache_controller
│   └── State machine
├── cache_monitor
│   └── Performance counters
├── main_memory
├── datapath_pipeline_with_cache
│   └── (Pipeline stages with cache interface)
└── controller_pipeline_with_cache
    └── (Control logic with cache stall handling)
```

### Running Simulations

#### Prerequisites
- SystemVerilog simulator (ModelSim, QuestaSim, Icarus Verilog, or Verilator)
- Sufficient memory for cache and main memory models

#### Steps

1. Navigate to this directory:
   ```bash
   cd MIPS_Pipeline_with_cache
   ```

2. Run simulation with your simulator:
   ```bash
   # For ModelSim/QuestaSim
   vlog *.sv
   vsim top_pipeline_with_cache
   
   # For Icarus Verilog
   iverilog -g2012 -o sim *.sv
   vvp sim
   ```

3. Observe cache performance metrics in the output

### Performance Analysis

The cache monitor provides detailed statistics:

**Cache Statistics Example:**
```
Instruction Cache:
- Accesses: 10000
- Hits: 9800
- Misses: 200
- Hit Rate: 98.0%

Data Cache:
- Accesses: 3000
- Hits: 2850
- Misses: 150
- Hit Rate: 95.0%
- Write-backs: 45

Overall Performance:
- Total Cycles: 15000
- CPI: 1.5
- Speedup vs. no cache: 66.7x
```

### Cache Optimization Techniques

Implemented optimizations:

1. **Block Size Selection**
   - Larger blocks exploit spatial locality
   - Balance between miss rate and miss penalty

2. **Associativity**
   - Reduces conflict misses
   - Trade-off with hardware complexity and hit time

3. **Write Policy**
   - Write-back reduces memory traffic
   - Write-allocate improves performance for typical programs

4. **Prefetching** (optional)
   - Reduces compulsory misses
   - Can increase memory bandwidth usage

### Design Considerations

**Cache Size Trade-offs:**
- **Larger Cache**: Lower miss rate, higher cost, longer hit time
- **Smaller Cache**: Higher miss rate, lower cost, faster hit time

**Associativity Trade-offs:**
- **Direct-Mapped**: Simple, fast, more conflict misses
- **Set-Associative**: Fewer conflict misses, more complex
- **Fully-Associative**: Lowest miss rate, very complex, slow

**Block Size Trade-offs:**
- **Small Blocks**: Less data transferred per miss, less spatial locality
- **Large Blocks**: More data per miss, better spatial locality, higher miss penalty

---

## Português

### Visão Geral

Esta pasta contém um processador MIPS pipeline aprimorado com sistema de memória cache integrado. Esta implementação demonstra como a memória cache melhora o desempenho do processador reduzindo latência de acesso à memória e aumentando largura de banda efetiva.

### Arquitetura de Cache

A implementação apresenta uma hierarquia de memória de dois níveis:

1. **Caches L1** (on-chip, rápidos)
   - **Cache de Instruções (I-Cache)**: Cache dedicado para instruções
   - **Cache de Dados (D-Cache)**: Cache separado para dados com política write-back

2. **Memória Principal** (off-chip, mais lenta)
   - Gerencia misses de cache
   - Armazena programa e dados completos

### Detalhes do Design de Cache

#### Cache de Instruções (I-Cache)

**Especificações:**
- **Tipo**: Mapeamento direto ou associativo por conjunto N-way
- **Tamanho**: Configurável (tipicamente 4KB - 16KB)
- **Tamanho do Bloco**: 32 bytes (8 palavras)
- **Política**: Somente leitura (instruções não mudam durante execução)

#### Cache de Dados (D-Cache)

**Especificações:**
- **Tipo**: Mapeamento direto ou associativo por conjunto N-way
- **Tamanho**: Configurável (tipicamente 4KB - 16KB)
- **Tamanho do Bloco**: 32 bytes (8 palavras)
- **Política de Escrita**: Write-back com write-allocate
- **Substituição**: LRU ou FIFO (para caches associativos)

### Monitor de Cache

Rastreia métricas de desempenho:

**Métricas Coletadas:**
- Total de acessos à cache
- Hits e misses de cache
- Percentual de taxa de hit
- Ciclos de penalidade de miss
- Write-backs realizados
- Tempo médio de acesso à memória (AMAT)

### Impacto de Desempenho do Cache

#### Sem Cache (Acesso Direto à Memória)
- **Tempo de Acesso à Memória**: 100+ ciclos (típico)
- **CPI Efetivo**: Muito alto (>100)

#### Com Cache (Esta Implementação)
- **Tempo de Hit**: 1 ciclo
- **Penalidade de Miss**: 10-50 ciclos
- **Taxa de Hit Típica**: 90-99%
- **CPI Efetivo**: ~1.5-3.0

**Exemplo de Cálculo de Desempenho:**
```
Premissas:
- Taxa de Hit: 95%
- Tempo de Hit: 1 ciclo
- Penalidade de Miss: 20 ciclos

AMAT = 1 + (0.05 × 20) = 2 ciclos
Aceleração vs. sem cache = 100 / 2 = 50x
```

### Análise de Desempenho

O monitor de cache fornece estatísticas detalhadas incluindo:
- Acessos, hits, misses para I-Cache e D-Cache
- Taxas de hit
- Write-backs
- CPI geral
- Aceleração comparada com acesso direto à memória

---

**Note**: This implementation demonstrates realistic cache behavior and provides a foundation for studying memory hierarchy optimization in processor design.
