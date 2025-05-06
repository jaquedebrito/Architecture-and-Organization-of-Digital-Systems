#!/bin/bash
# File: run_sim.sh
# Author: Jaqueline Ferreira de Brito
# Date: 2025-03-11
# Description: Script to select and run SystemVerilog testbenches with Cadence Xcelium

# Clear the screen
clear

# Current user and time
CURRENT_USER="jaquedebritota"
CURRENT_DATE=$(date -u '+%Y-%m-%d %H:%M:%S')

# Print header
echo "======================================================"
echo "     MIPS Processor Testing Environment              "
echo "     By: Jaqueline Ferreira de Brito                 "
echo "     Date: $CURRENT_DATE UTC                         "
echo "     User: $CURRENT_USER                             "
echo "======================================================"
echo

# Define all available modules and testbenches
declare -a MODULES=(
    "adder.sv"
    "controller.sv"
    "data_memory.sv"
    "datapath.sv"
    "flopr.sv"
    "instruction_memory.sv"
    "main_control.sv"
    "mux2.sv"
    "regfile.sv"
    "signext.sv"
    "sl2.sv"
    "top.sv"
    "ula.sv"
    "ula_control.sv"
)

declare -a TESTBENCHES=(
    "adder_tb.sv"
    "controller_tb.sv"
    "data_memory_tb.sv"
    "datapath_tb.sv"
    "flopr_tb.sv"
    "instruction_memory_tb.sv"
    "main_control_tb.sv"
    "mux2_tb.sv"
    "regfile_tb.sv"
    "signext_tb.sv"
    "sl2_tb.sv"
    "top_tb.sv"
    "ula_tb.sv"
    "ula_control_tb.sv"
)

# Function to run the simulation
run_simulation() {
    local impl_file="$1"
    local tb_file="$2"
    
    echo "Running simulation with $impl_file and $tb_file..."
    
    # Check for special cases where additional files are needed
    case "$impl_file" in
        "top.sv")
            echo "Running top-level simulation (includes multiple files)..."
            xrun adder.sv controller.sv data_memory.sv datapath.sv flopr.sv instruction_memory.sv main_control.sv mux2.sv regfile.sv signext.sv sl2.sv top.sv ula.sv ula_control.sv "$tb_file"
            ;;
        "datapath.sv")
            echo "Running datapath simulation (includes components)..."
            xrun adder.sv flopr.sv mux2.sv regfile.sv signext.sv sl2.sv ula.sv "$impl_file" "$tb_file"
            ;;
        "controller.sv")
            echo "Running controller simulation (includes components)..."
            xrun main_control.sv ula_control.sv "$impl_file" "$tb_file"
            ;;
        *)
            # Standard simulation with just the implementation and testbench
            xrun "$impl_file" "$tb_file"
            ;;
    esac
    
    echo "Simulation completed."
    echo "Press Enter to continue..."
    read
}

# Display main menu with modules
echo "Available test combinations:"

# Single module tests
for i in "${!MODULES[@]}"; do
    echo "$((i+1))) Test ${MODULES[$i]%.sv}: ${MODULES[$i]} & ${TESTBENCHES[$i]}"
done

# Special options
echo "$((${#MODULES[@]}+1))) Run all tests"
echo "$((${#MODULES[@]}+2))) Run top-level test only (full processor)"
echo "$((${#MODULES[@]}+3))) Custom selection"
echo "$((${#MODULES[@]}+4))) Exit"
echo

# Get user choice
read -p "Enter your choice [1-$((${#MODULES[@]}+4))]: " choice

# Process user choice
if [[ "$choice" =~ ^[0-9]+$ ]]; then
    if [ "$choice" -ge 1 ] && [ "$choice" -le "${#MODULES[@]}" ]; then
        # Run specific test
        idx=$((choice-1))
        run_simulation "${MODULES[$idx]}" "${TESTBENCHES[$idx]}"
    elif [ "$choice" -eq $((${#MODULES[@]}+1)) ]; then
        # Run all tests
        echo "Running all tests sequentially..."
        for (( i=0; i<${#MODULES[@]}; i++ )); do
            echo "==============================================="
            echo "Test ${i+1}/${#MODULES[@]}: ${MODULES[$i]} with ${TESTBENCHES[$i]}"
            echo "==============================================="
            
            # Handle special cases
            case "${MODULES[$i]}" in
                "top.sv")
                    xrun adder.sv controller.sv data_memory.sv datapath.sv flopr.sv instruction_memory.sv main_control.sv mux2.sv regfile.sv signext.sv sl2.sv top.sv ula.sv ula_control.sv "${TESTBENCHES[$i]}"
                    ;;
                "datapath.sv")
                    xrun adder.sv flopr.sv mux2.sv regfile.sv signext.sv sl2.sv ula.sv "${MODULES[$i]}" "${TESTBENCHES[$i]}"
                    ;;
                "controller.sv")
                    xrun main_control.sv ula_control.sv "${MODULES[$i]}" "${TESTBENCHES[$i]}"
                    ;;
                *)
                    xrun "${MODULES[$i]}" "${TESTBENCHES[$i]}"
                    ;;
            esac
            
            echo "Press Enter to continue to next test..."
            read
        done
    elif [ "$choice" -eq $((${#MODULES[@]}+2)) ]; then
        # Run top-level test only
        echo "Running top-level processor test..."
        xrun adder.sv controller.sv data_memory.sv datapath.sv flopr.sv instruction_memory.sv main_control.sv mux2.sv regfile.sv signext.sv sl2.sv top.sv ula.sv ula_control.sv top_tb.sv
    elif [ "$choice" -eq $((${#MODULES[@]}+3)) ]; then
        # Custom selection
        echo "Custom selection mode"
        echo "Available implementation files:"
        for i in "${!MODULES[@]}"; do
            echo "$((i+1))) ${MODULES[$i]}"
        done
        read -p "Select implementation file [1-${#MODULES[@]}]: " impl_choice
        
        # Validate implementation choice
        if [ "$impl_choice" -lt 1 ] || [ "$impl_choice" -gt "${#MODULES[@]}" ]; then
            echo "Invalid choice. Exiting."
            exit 1
        fi
        
        echo "Available testbench files:"
        for i in "${!TESTBENCHES[@]}"; do
            echo "$((i+1))) ${TESTBENCHES[$i]}"
        done
        read -p "Select testbench file [1-${#TESTBENCHES[@]}]: " tb_choice
        
        # Validate testbench choice
        if [ "$tb_choice" -lt 1 ] || [ "$tb_choice" -gt "${#TESTBENCHES[@]}" ]; then
            echo "Invalid choice. Exiting."
            exit 1
        fi
        
        # Run simulation with selected files
        impl_file="${MODULES[$((impl_choice-1))]}"
        tb_file="${TESTBENCHES[$((tb_choice-1))]}"
        run_simulation "$impl_file" "$tb_file"
    elif [ "$choice" -eq $((${#MODULES[@]}+4)) ]; then
        # Exit
        echo "Exiting the MIPS Processor Testing Environment."
        exit 0
    else
        echo "Invalid choice. Exiting."
        exit 1
    fi
else
    echo "Invalid input. Please enter a number."
    exit 1
fi

# Final message
echo "Thank you for using the MIPS Processor Testing Environment!"
