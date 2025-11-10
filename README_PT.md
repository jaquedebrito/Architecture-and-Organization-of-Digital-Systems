# Arquitetura e Organização de Sistemas Digitais

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![SystemVerilog](https://img.shields.io/badge/Linguagem-SystemVerilog-blue.svg)](https://www.systemverilog.io/)
[![MIPS](https://img.shields.io/badge/Arquitetura-MIPS-green.svg)](https://pt.wikipedia.org/wiki/Arquitetura_MIPS)

[English](./README.md) | [Português](#português)

---

## Português

### 📚 Visão Geral

Este repositório serve como um estudo abrangente do design, implementação e análise de sistemas digitais, explorando aspectos teóricos e práticos. O foco está em compreender arquiteturas digitais modernas, com ênfase principal em designs de processadores MIPS e tópicos avançados como System-on-Chip (SoC) e Network-on-Chip (NoC).

### 🎯 Objetivos do Projeto

- Implementar e entender arquiteturas de processadores MIPS
- Explorar designs de processadores monociclo e pipeline
- Estudar integração e otimização de memória cache
- Demonstrar design prático de hardware usando SystemVerilog
- Fornecer recursos educacionais para arquitetura de sistemas digitais

### 🚀 Início Rápido

#### Pré-requisitos

- **Simulador SystemVerilog**: ModelSim, QuestaSim, Icarus Verilog ou Verilator
- **Bash**: Para executar scripts de simulação (Linux/Mac/WSL)
- **Conhecimento básico**: Conceitos de design digital e arquitetura de computadores

#### Executando Simulações

1. **Clone o repositório**:
   ```bash
   git clone https://github.com/jaquedebrito/Architecture-and-Organization-of-Digital-Systems.git
   cd Architecture-and-Organization-of-Digital-Systems
   ```

2. **Navegue para a implementação desejada**:
   ```bash
   cd MIPS_monociclo    # Para processador monociclo
   # ou
   cd MIPS_Pipeline     # Para processador pipeline
   ```

3. **Execute as simulações**:
   ```bash
   chmod +x run_sim.sh  # Torne o script executável (apenas primeira vez)
   ./run_sim.sh         # Execute o menu interativo de simulação
   ```

4. **Selecione o módulo para testar** no menu interativo

---

## 📁 Estrutura do Repositório

### Organização do Projeto

```
Architecture-and-Organization-of-Digital-Systems/
├── MIPS_monociclo/              # Processador MIPS monociclo
├── MIPS_Pipeline/               # Processador MIPS pipeline com tratamento de hazards
├── MIPS_Pipeline_with_cache/    # MIPS pipeline com sistema de memória cache
├── README.md                    # Versão em inglês
├── README_PT.md                 # Este arquivo (Português)
├── LICENSE                      # Licença MIT
└── .gitignore                   # Regras do Git ignore
```

---

## 🔧 Implementações

### 1. MIPS_monociclo - Processador MIPS Monociclo

Uma implementação completa de um processador MIPS monociclo com arquitetura Harvard.

**Características Principais:**
- ✅ Arquitetura Harvard com memórias separadas para instruções e dados
- ✅ Suporte para instruções tipo-R, tipo-I e tipo-J
- ✅ ULA completa com operações aritméticas e lógicas
- ✅ Banco de 32 registradores (32 bits cada)
- ✅ Design de unidade de controle simples

**Módulos Principais:**
- `controller.sv` - Unidade de controle principal
- `datapath.sv` - Lógica do caminho de dados
- `instruction_memory.sv` - Armazenamento de instruções
- `data_memory.sv` - Armazenamento de dados
- `ula.sv` - Unidade Lógico-Aritmética
- `regfile.sv` - Banco de registradores
- `top.sv` - Integração de nível superior

**Instruções Suportadas:**
- **Aritméticas**: `add`, `sub`, `addi`
- **Lógicas**: `and`, `or`, `slt`
- **Memória**: `lw` (load word), `sw` (store word)
- **Controle**: `beq` (branch if equal), `j` (jump)

📖 **[Documentação Detalhada](./MIPS_monociclo/README.md)**

---

### 2. MIPS_Pipeline - Processador MIPS Pipeline

Implementação avançada de pipeline de 5 estágios com otimizações de desempenho e tratamento de hazards.

**Estágios do Pipeline:**
1. **IF** (Instruction Fetch - Busca de Instrução) - `if_stage.sv`
2. **ID** (Instruction Decode - Decodificação) - `id_stage.sv`
3. **EX** (Execute - Execução) - `ex_stage.sv`
4. **MEM** (Memory Access - Acesso à Memória) - `mem_stage.sv`
5. **WB** (Write Back - Escrita de Volta) - `wb_stage.sv`

**Recursos de Desempenho:**
- ✅ **Unidade de Forwarding** - Encaminhamento de dados para resolver hazards de dados
- ✅ **Unidade de Detecção de Hazards** - Detecta e trata hazards do pipeline
- ✅ **Preditor de Desvios** - Predição dinâmica de desvios para melhor desempenho
- ✅ **Monitor de Desempenho** - Rastreia CPI, stalls e outras métricas

**Módulos Principais:**
- `datapath_pipeline.sv` - Caminho de dados pipeline
- `controller_pipeline.sv` - Lógica de controle do pipeline
- `forwarding_unit.sv` - Gerencia encaminhamento de dados
- `hazard_detection_unit.sv` - Detecta hazards do pipeline
- `branch_predictor.sv` - Lógica de predição de desvios
- `performance_monitor.sv` - Rastreamento de desempenho

**Vantagens sobre Monociclo:**
- Maior throughput (múltiplas instruções em execução)
- Melhor potencial de frequência de clock
- Desempenho aprimorado com mitigação de hazards

📖 **[Documentação Detalhada](./MIPS_Pipeline/README.md)**

---

### 3. MIPS_Pipeline_with_cache - MIPS Pipeline com Cache

Processador pipeline aprimorado com sistema de memória cache integrado para melhor desempenho de memória.

**Recursos de Cache:**
- ✅ **Cache de Instruções (I-Cache)** - Cache dedicado para instruções
- ✅ **Cache de Dados (D-Cache)** - Cache separado com política write-back
- ✅ **Controlador de Cache** - Gerencia operações e coerência de cache
- ✅ **Monitor de Cache** - Monitoramento de desempenho (hits, misses, etc.)
- ✅ **Interface de Memória Principal** - Gerencia misses de cache

**Módulos Principais:**
- `icache.sv` - Implementação do cache de instruções
- `dcache.sv` - Implementação do cache de dados
- `cache_controller.sv` - Lógica de controle do cache
- `cache_monitor.sv` - Rastreamento de desempenho
- `main_memory.sv` - Modelo de memória principal
- `top_pipeline_with_cache.sv` - Integração completa do sistema

**Benefícios:**
- Latência reduzida de acesso à memória
- Maior largura de banda efetiva de memória
- Comportamento realista de processador moderno

📖 **[Documentação Detalhada](./MIPS_Pipeline_with_cache/README.md)**

---

## 📖 Cobertura Teórica

O repositório também demonstra compreensão de conceitos teóricos avançados:

### 1. **IP Cores**
- Blocos de design reutilizáveis para modularidade e escalabilidade
- Tipos: Soft Cores, Firm Cores e Hard Cores
- Permite iteração mais rápida de design e componentes verificados

### 2. **System-on-Chip (SoC)**
- Integração de processadores, memória, interfaces e periféricos em um único chip
- Evolução de ASICs para designs SoC modernos
- Demonstrado através de sistemas integrados de processador e memória

### 3. **Arquiteturas de Comunicação**
- Sistemas de barramento tradicionais (ex: PCI, AMBA) e suas limitações
- Transição para Network-on-Chip (NoC) para escalabilidade
- Comunicação paralela e largura de banda melhorada

### 4. **Tecnologias 3D**
- **3D-IC (Circuitos Integrados)**: Designs em camadas para maior densidade
- **3D-NoC (Network-on-Chip)**: Combinando NoC com 3D-IC
- Benefícios: comprimento de fio reduzido, desempenho melhorado, menor potência

---

## 🎓 Resultados de Aprendizagem

Este repositório demonstra as seguintes competências principais:

### Habilidades Práticas
- ✅ Implementação e teste de processadores MIPS (monociclo e pipeline)
- ✅ Domínio de princípios de design modular de hardware
- ✅ Técnicas de verificação usando testbenches SystemVerilog
- ✅ Análise e otimização de desempenho

### Conhecimento Avançado
- ✅ Compreensão de IP Cores, SoCs, NoCs e tecnologias 3D
- ✅ Estratégias de detecção e mitigação de hazards de pipeline
- ✅ Design de memória cache e otimização de desempenho
- ✅ Evolução e tendências em arquitetura digital

### Proficiência em Ferramentas
- ✅ Linguagem de descrição de hardware SystemVerilog
- ✅ Ferramentas de simulação (ModelSim, QuestaSim, etc.)
- ✅ Teste e verificação automatizados
- ✅ Monitoramento e análise de desempenho

### Documentação e Comunicação
- ✅ Documentação técnica clara
- ✅ Organização e modularidade de código
- ✅ Análise e apresentação de resultados de teste

---

## 🧪 Teste e Verificação

Cada implementação inclui testbenches abrangentes:

### Organização dos Testbenches
```
<implementação>/
├── testbenchs/              # Diretório contendo todos os testbenches
│   ├── adder_tb.sv         # Testes do somador da ULA
│   ├── controller_tb.sv    # Testes da unidade de controle
│   ├── datapath_tb.sv      # Testes do caminho de dados
│   └── ...                 # Outros testes de componentes
└── top_*_tb.sv             # Testbench do sistema completo
```

### Executando Testes

Use o script de simulação interativo:
```bash
./run_sim.sh
```

O script fornece:
- Teste de módulos individuais
- Simulação completa do sistema
- Seleção personalizada de testes
- Verificação automatizada de resultados

### Cobertura de Testes

Cada testbench inclui:
- Casos de teste de operação normal
- Teste de casos extremos
- Tratamento de condições de erro
- Coleta de métricas de desempenho

---

## 🤝 Contribuindo

Contribuições são bem-vindas! Veja como você pode ajudar:

### Formas de Contribuir

1. **Melhorar módulos existentes**: Otimizar designs ou adicionar recursos
2. **Adicionar novos testbenches**: Aumentar cobertura de testes
3. **Aprimorar documentação**: Melhorar clareza ou adicionar exemplos
4. **Corrigir bugs**: Relatar ou corrigir problemas encontrados
5. **Adicionar novos recursos**: Implementar instruções ou otimizações adicionais

### Diretrizes de Contribuição

1. **Fork** o repositório
2. **Crie** um branch de feature (`git checkout -b feature/recurso-incrivel`)
3. **Commit** suas mudanças (`git commit -m 'Adiciona recurso incrível'`)
4. **Push** para o branch (`git push origin feature/recurso-incrivel`)
5. **Abra** um Pull Request

### Padrões de Código

- Siga o estilo de código e convenções de nomenclatura existentes
- Comente lógica complexa e decisões importantes
- Inclua testbenches para novos módulos
- Atualize a documentação para mudanças significativas

---

## 📝 Licença

Este projeto está licenciado sob a Licença MIT - veja o arquivo [LICENSE](LICENSE) para detalhes.

### Resumo da Licença MIT

✅ Uso comercial  
✅ Modificação  
✅ Distribuição  
✅ Uso privado  

---

## 👤 Autora

**Jaqueline Ferreira de Brito**

- GitHub: [@jaquedebrito](https://github.com/jaquedebrito)

---

## 🌟 Agradecimentos

- Documentação e especificações da arquitetura MIPS
- Livros e recursos de arquitetura de computadores
- Comunidade e ferramentas SystemVerilog
- Comunidade de design de hardware open-source

---

## 📚 Referências

### Arquitetura MIPS
- [Visão Geral da Arquitetura MIPS](https://pt.wikipedia.org/wiki/Arquitetura_MIPS)
- [Conjunto de Instruções MIPS](https://www.mips.com/)

### SystemVerilog
- [Padrão IEEE SystemVerilog](https://standards.ieee.org/)
- [Tutorial SystemVerilog](https://www.chipverify.com/systemverilog/systemverilog-tutorial)

### Arquitetura de Computadores
- "Organização e Projeto de Computadores: A Interface Hardware/Software" por Patterson & Hennessy
- "Design Digital e Arquitetura de Computadores" por Harris & Harris

---

## 📊 Status do Projeto

| Componente | Status | Cobertura de Testes |
|-----------|--------|---------------------|
| MIPS_monociclo | ✅ Completo | Alta |
| MIPS_Pipeline | ✅ Completo | Alta |
| MIPS_Pipeline_with_cache | ✅ Completo | Média |

---

## 🔄 Histórico de Versões

- **v1.0** (Março 2025) - Lançamento inicial com todas as três implementações MIPS
  - Processador MIPS monociclo
  - Processador MIPS pipeline com tratamento de hazards
  - Processador MIPS pipeline com memória cache

---

**Nota**: Para a versão em inglês deste README, consulte [README.md](./README.md)
