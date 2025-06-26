# TM Tape to Number: Formalizing Turing Machine Integer Sequences

[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)](https://github.com/user/TM_Tape_to_Number)
[![Lean 4](https://img.shields.io/badge/Lean-4.21.0-blue)](https://lean-lang.org/)
[![Progress](https://img.shields.io/badge/progress-92%25-green)](./PROJECT_STATUS.md)

A formal verification project in Lean 4 that formalizes Turing machines generating integer sequences through tape content encoding.

## 🎯 Project Overview

This project explores a fascinating connection between Turing machines and integer sequences. Instead of studying what Turing machines *compute*, we study the *sequences of numbers* they generate by encoding their tape contents at each computation step.

### The Core Idea

**Traditional View**: Turing machines are studied for their computational outputs - what final result they produce.

**Our Approach**: We encode the *entire tape content* as a natural number at each step, creating an integer sequence that captures the machine's evolving internal state.

### Key Innovation: Absolute Position Encoding

We implement a **leftward-unbounded tape model** where:
- The tape head is constrained to positions ≤ 0 (positions 0, -1, -2, -3, ...)
- Tape positions have **absolute coordinates** that never change, regardless of head movement
- Each position contributes to the encoding based on its absolute coordinate:
  - Position 0 → contributes 2⁰ = 1 (ones place)
  - Position -1 → contributes 2¹ = 2 (twos place)  
  - Position -2 → contributes 2² = 4 (fours place)
  - And so on...

This creates a **binary encoding** where the tape content directly maps to a natural number, independent of the machine's execution state.

### Example: Powers of Two Machine

Consider a machine that:
1. Writes `true` at position 0, then moves left
2. Finds the leftmost `true`, moves left once more, writes `true`
3. Repeats this process

**Tape Evolution**:
```
Step 0: [T] at position 0           → Encoding: 1
Step 1: [T][T] at positions -1,0    → Encoding: 3  
Step 2: [T][T][T] at positions -2,-1,0 → Encoding: 7
```

**Generated Sequence**: 1, 3, 7, 15, 31, ... (numbers of form 2ⁿ - 1)

## 📁 Project Structure

```
TMTapeToNumber/
├── Basic.lean                       # Main entry point and imports
├── Examples/
│   └── PowersOfTwo.lean            # Example: Powers of two machine
├── LeftTM0/                        # Core Turing machine infrastructure
│   ├── LeftwardTape.lean           # Leftward-constrained tape type
│   ├── Machine.lean                # Machine definition and configuration  
│   └── Step.lean                   # Step function and execution
├── LeftwardEncoding/               # Tape encoding system
│   ├── Basic.lean                  # Core encoding definitions
│   └── Properties.lean             # Encoding theorems and properties
└── LeftwardSequences/              # Sequence generation
    ├── Basic.lean                  # Sequence definitions
    └── Theorems.lean               # Growth bounds and convergence
```

### Module Overview

#### **LeftTM0/** - Core Infrastructure
- **`LeftwardTape.lean`**: Implements tape constrained to positions ≤ 0
  - Absolute position tracking independent of head movement
  - Move operations that respect the leftward constraint
  - Finite support guarantees for encoding

- **`Machine.lean`**: Defines machine types and configurations
  - Standard TM0 machine extended with position constraints
  - Configuration type combining state and constrained tape

- **`Step.lean`**: Execution semantics preserving constraints
  - Step function that halts if constraint would be violated
  - Multi-step execution and termination detection

#### **LeftwardEncoding/** - Tape → Number Encoding
- **`Basic.lean`**: Core encoding functionality
  - `encode: LeftwardTape Bool → ℕ` - converts tape to natural number
  - Encoding based on absolute positions of `true` values
  - Step-wise encoding difference bounds

- **`Properties.lean`**: Mathematical properties of encoding
  - Encoding bounds based on leftmost true position
  - Invariance under head movements
  - Injectivity and determinism results

#### **LeftwardSequences/** - Sequence Generation  
- **`Basic.lean`**: Sequence generation from machine execution
  - `sequence: Machine → Config → ℕ → ℕ` - generates integer sequences
  - Bounded execution and termination handling

- **`Theorems.lean`**: Growth bounds and convergence properties
  - Exponential growth bounds based on reachable positions
  - Sequence stability when machines halt

## 🎯 Mathematical Results

### Core Theorems

1. **Encoding Bounds**: If all positions left of `-n` are false, then `encode(tape) < 2^(n+1)`

2. **Step Difference Bounds**: Any single machine step changes the encoding by at most `2^k` for some `k`

3. **Sequence Growth**: Generated sequences have exponential growth bounds based on initial tape content

4. **Movement Invariance**: Head movements don't change the encoding (only writes do)

### Applications

This framework enables:
- **Sequence Classification**: Categorizing integer sequences by their generating machines
- **Computational Complexity**: Studying growth rates of mechanically generated sequences  
- **Algorithmic Information**: Connecting tape complexity to sequence properties

## 🚀 Current Status

- **Build Status**: ✅ All modules compile successfully
- **Progress**: 92% complete (23/25 proofs done)
- **Remaining Work**: 2 theorem completions in encoding and sequence bounds

See [PROJECT_STATUS.md](./PROJECT_STATUS.md) for detailed progress tracking.

## 🛠️ Building and Usage

### Prerequisites
- [Lean 4.21.0](https://lean-lang.org/lean4/doc/quickstart.html)
- [Lake](https://github.com/leanprover/lake) (Lean's build system)

### Building
```bash
git clone https://github.com/user/TM_Tape_to_Number.git
cd TM_Tape_to_Number
lake build
```

### Exploring the Code
```lean
-- Import the main module
import TMTapeToNumber

-- Example: Create a tape and encode it
#check LeftwardTape.mk_initial [true, false, true]
#check LeftwardTape.encode

-- Example: Define and run a machine
#check LeftTM0.sequence
```

## 📚 Theoretical Background

This work builds on:
- **Turing Machine Theory**: Classical computational models
- **Formal Language Theory**: Tape representation and encoding
- **Sequence Analysis**: Growth bounds and convergence properties
- **Lean 4 Formalization**: Modern proof assistant techniques

The approach provides a novel perspective on mechanical sequence generation, connecting abstract machine computation to concrete integer sequences through rigorous mathematical formalization.

## 🤝 Contributing

This is a research project in formal verification. Contributions welcome for:
- Completing remaining theorem proofs
- Adding new example machines
- Extending to other tape models
- Performance optimizations

## 📄 License

[MIT License](./LICENSE)

---

**A formal exploration of the beautiful mathematics hiding in Turing machine tape evolution.**