#!/bin/bash
# File: run_sim.sh
# Author: Jaqueline Ferreira de Brito
# Date: 2025-03-20 13:29:12
# Description: Script to run SystemVerilog simulation for MIPS Pipeline with Cadence Xcelium

# Clear the screen
clear

# Current user and time
CURRENT_USER="jaquedebrito"
CURRENT_DATE="2025-03-20 13:29:12"

# Print header
echo "======================================================="
echo "     MIPS Pipeline Processor Testing Environment        "
echo "     By: Jaqueline Ferreira de Brito                   "
echo "     Date: $CURRENT_DATE UTC                           "
echo "     User: $CURRENT_USER                               "
echo "======================================================="
echo

# Define all pipeline modules
declare -a PIPELINE_MODULES=(
    "types_pkg.sv"
    "adder.sv"
    "branch_predictor.sv"
    "controller_pipeline.sv"
    "data_memory.sv"
    "datapath_pipeline.sv"
    "ex_mem_reg.sv"
    "ex_stage.sv"
    "exception_handler.sv"
    "flopr.sv"
    "forwarding_unit.sv"
    "hazard_detection_unit.sv"
    "id_ex_reg.sv"
    "id_stage.sv"
    "if_id_reg.sv"
    "if_stage.sv"
    "instruction_memory.sv"
    "main_control.sv"
    "mem_stage.sv"
    "mem_wb_reg.sv"
    "mux2.sv"
    "mux3.sv"
    "performance_monitor.sv"
    "regfile.sv"
    "signext.sv"
    "sl2.sv"
    "top_pipeline.sv"
    "ula.sv"
    "ula_control.sv"
    "wb_stage.sv"
)

# Function to verify file existence
verify_files() {
    local missing_files=0
    
    echo "Verificando arquivos necessários..."
    for module in "${PIPELINE_MODULES[@]}"; do
        if [ ! -f "$module" ]; then
            echo "ERRO: Arquivo não encontrado: $module"
            missing_files=$((missing_files + 1))
        fi
    done
    
    if [ ! -f "top_pipeline_tb.sv" ]; then
        echo "ERRO: Testbench não encontrado: top_pipeline_tb.sv"
        missing_files=$((missing_files + 1))
    fi
    
    if [ $missing_files -gt 0 ]; then
        echo "ERRO: $missing_files arquivo(s) necessário(s) não encontrado(s)."
        return 1
    fi
    
    echo "Todos os arquivos necessários encontrados."
    return 0
}

# Function to run simulation
run_simulation() {
    echo "Iniciando simulação do MIPS Pipeline..."
    echo "Data: $CURRENT_DATE"
    echo "Usuário: $CURRENT_USER"
    echo

    # Construct the xrun command with all modules
    CMD="xrun -gui -access +rw"
    
    # Add all modules to the command
    for module in "${PIPELINE_MODULES[@]}"; do
        CMD="$CMD $module"
    done
    
    # Add testbench
    CMD="$CMD top_pipeline_tb.sv"
    
    # Execute simulation
    echo "Executando comando: $CMD"
    eval $CMD
    
    # Check simulation result
    if [ $? -eq 0 ]; then
        echo "Simulação concluída com sucesso."
        return 0
    else
        echo "ERRO: Simulação falhou."
        return 1
    fi
}

# Main execution
echo "Iniciando ambiente de teste do MIPS Pipeline..."
echo

# Verify files first
if verify_files; then
    echo "Iniciando simulação..."
    if run_simulation; then
        echo "======================================================="
        echo "Simulação finalizada com sucesso!"
        echo "Data/Hora: $CURRENT_DATE"
        echo "Usuário: $CURRENT_USER"
        echo "======================================================="
    else
        echo "======================================================="
        echo "ERRO: Falha na simulação!"
        echo "Data/Hora: $CURRENT_DATE"
        echo "Usuário: $CURRENT_USER"
        echo "======================================================="
        exit 1
    fi
else
    echo "======================================================="
    echo "ERRO: Verificação de arquivos falhou!"
    echo "Data/Hora: $CURRENT_DATE"
    echo "Usuário: $CURRENT_USER"
    echo "======================================================="
    exit 1
fi

exit 0
