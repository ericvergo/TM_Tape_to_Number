# TM Tape to Number

A Lean 4 formalization of leftward-unbounded Turing machines that generate integer sequences by encoding their tape contents as natural numbers.

## Overview

This project provides a mathematical framework for studying Turing machines that:
- Operate on a tape that extends infinitely to the left but is bounded at position 0 on the right
- Use binary (Boolean) tape symbols
- Generate integer sequences by interpreting their tape contents as binary numbers

The key insight is that we can track the evolution of a Turing machine by encoding its tape as a natural number at each step, creating a sequence of integers that characterizes the machine's behavior.

## Encoding Scheme

The tape is encoded as a binary number where:
- **Absolute tape position 0** → 2⁰ = 1 (ones place)
- **Absolute tape position -1** → 2¹ = 2 (twos place)  
- **Absolute tape position -2** → 2² = 4 (fours place)
- And so on...

For example, a tape with `true` values at positions 0 and -2 encodes to 1 + 4 = 5.

Importantly, the encoding is based on **absolute tape positions**, not positions relative to the head. This ensures consistent encoding regardless of where the machine's head is currently positioned.

## Project Structure

```
TMTapeToNumber/
├── Basic.lean                    # Public API and exports
├── LeftwardTape.lean            # Leftward-bounded tape with position constraints
└── LeftTM0/
    ├── Machine.lean             # Machine definitions using mathlib's TM0
    ├── Step.lean                # Step execution semantics
    ├── Encoding.lean            # Tape-to-number encoding functions
    ├── Sequences.lean           # Sequence generation from machine execution
    └── Examples/
        └── PowersOfTwo.lean     # Example: machine generating powers of 2
```

## Key Components

### LeftwardTape

A wrapper around mathlib's `Tape` type that enforces the constraint that the head position must be ≤ 0:

```lean
structure LeftwardTape (Γ : Type*) [Inhabited Γ] where
  tape : Tape Γ
  head_pos : ℤ
  head_nonpos : head_pos ≤ 0
```

### Encoding

The encoding function sums over all absolute tape positions ≤ 0 where the tape contains `true`:

```lean
noncomputable def encode (T : LeftwardTape Bool) : ℕ :=
  ∑ i ∈ true_positions_absolute T, 2^(Int.natAbs (-i))
```

### Sequence Generation

Given a Turing machine and initial configuration, we can generate a sequence of natural numbers:

```lean
noncomputable def sequence (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) : ℕ → ℕ :=
  fun n ↦ encode_config (steps M n init_cfg)
```

## Example: Powers of Two

The project includes an example of a Turing machine that generates the sequence 1, 2, 4, 8, 16, ... (powers of 2). The machine works by repeatedly shifting all `true` values one position to the left, effectively doubling the encoded value at each step.

## Building

This project uses Lake, Lean 4's build system. To build:

```bash
lake build
```

## Dependencies

- Lean 4
- mathlib4 (for Turing machine foundations and mathematical structures)

## Current Status

The core infrastructure is complete and all modules compile successfully. The project includes:
- ✅ Leftward-bounded tape implementation
- ✅ Tape-to-number encoding using absolute positions  
- ✅ Sequence generation from machine execution
- ✅ Example machine (powers of 2)
- 🚧 Theorem proofs (currently using `sorry` placeholders)

## Mathematical Properties

The encoding satisfies several important properties:

1. **Position Independence**: The encoding depends only on the tape contents, not the head position
2. **Binary Representation**: A tape encodes to the natural number whose binary representation matches the tape
3. **Monotonicity**: Adding a `true` at any position increases the encoding
4. **Shift Property**: Shifting all content left by one position doubles the encoding

## Future Work

- Complete formal proofs for all theorems
- Add more example machines (binary counter, Fibonacci generator, etc.)
- Prove characterization theorems about which sequences can be generated
- Explore connections to computational complexity and decidability

## Contributing

This project is part of ongoing research in formal methods and computational mathematics. Contributions are welcome, particularly:
- Completing theorem proofs
- Adding new example machines
- Improving documentation
- Optimizing the implementation

## License

[License information to be added]

## References

This work builds on mathlib's formalization of Turing machines, particularly the `Computability.TuringMachine` module.
