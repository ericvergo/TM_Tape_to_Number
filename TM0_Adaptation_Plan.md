# TM0 Adaptation Plan: Leftward-Unbounded Turing Machines

## Overview

This document outlines the plan to refactor our leftward-unbounded Turing machine implementation to build on top of mathlib's existing TM0 infrastructure instead of our custom definitions. This approach will provide better integration with mathlib's proven theorems and infrastructure while maintaining our specific leftward-unbounded semantics.

## Current State Analysis

### Mathlib's TM0 Provides:
- `TM0.Machine Γ Λ` = `Λ → Γ → Option (Λ × TM0.Stmt Γ)`
- `TM0.Cfg Γ Λ` with `q : Λ` (state) and `Tape : Tape Γ` (bidirectional tape)
- `TM0.step`, `TM0.init`, `TM0.eval`, `TM0.Reaches` functions
- Clean modular design with proper abstractions
- Well-tested infrastructure with existing theorems

### Our Current Custom Implementation:
- `LeftTape` using `ℤ →₀ Bool`
- `LeftTMConfig` with custom state management
- Custom transition functions
- Powers of 2 example working but isolated from mathlib

## Proposed Project Structure

```
TMTapeToNumber/
├── Basic.lean                    # Main exports and high-level interface
├── LeftwardTape.lean            # Leftward-constrained tape wrapper
├── LeftTM0/
│   ├── Machine.lean             # Machine definition and basic operations
│   ├── Step.lean                # Step function and execution semantics
│   ├── Encoding.lean            # Integer encoding from tape contents
│   ├── Sequences.lean           # Sequence generation infrastructure
│   └── Examples/
│       ├── PowersOfTwo.lean     # Powers of 2 generator
│       └── SimpleExamples.lean  # Other basic examples
├── Theorems/
│   ├── BasicProperties.lean     # Fundamental properties and bounds
│   ├── Reachability.lean       # Reachability and termination
│   └── SequenceProperties.lean  # Properties of generated sequences
└── Integration/
    ├── TM0Equiv.lean            # Equivalence with standard TM0
    └── MathlibCompat.lean       # Compatibility layer with mathlib
```

## Detailed Implementation Plan

### Phase 1: Core Infrastructure (Files 1-3)

#### 1. `TMTapeToNumber/LeftwardTape.lean`

**Purpose**: Wrapper around mathlib's `Tape Γ` that enforces leftward-unbounded constraints.

```lean
import Mathlib.Computability.Tape

/-- A leftward-unbounded tape that restricts operations to positions ≤ 0 -/
structure LeftwardTape (Γ : Type*) [Inhabited Γ] where
  tape : Tape Γ
  head_pos : ℤ  -- Current head position
  head_nonpos : head_pos ≤ 0  -- Invariant: head must be ≤ 0

namespace LeftwardTape

-- Basic operations
def read (T : LeftwardTape Γ) : Γ := T.tape.head

def write (T : LeftwardTape Γ) (a : Γ) : LeftwardTape Γ :=
  { T with tape := T.tape.write a }

def move_left (T : LeftwardTape Γ) : LeftwardTape Γ :=
  { tape := T.tape.move Dir.left
    head_pos := T.head_pos - 1
    head_nonpos := by linarith [T.head_nonpos] }

def move_right (T : LeftwardTape Γ) : LeftwardTape Γ :=
  if h : T.head_pos < 0 then
    { tape := T.tape.move Dir.right
      head_pos := T.head_pos + 1  
      head_nonpos := by linarith [h] }
  else T  -- Cannot move right from position 0

-- Integer encoding for Bool tapes
noncomputable def encode [DecidableEq Γ] (blank : Γ) (T : LeftwardTape Γ) : ℕ :=
  -- Sum over positions i ≤ 0 where T.tape.nth i ≠ blank
  -- Position i contributes 2^(-i) to the sum
  sorry -- Implementation details

end LeftwardTape
```

#### 2. `TMTapeToNumber/LeftTM0/Machine.lean`

**Purpose**: TM0-based machine definition with leftward constraints.

```lean
import Mathlib.Computability.PostTuringMachine
import TMTapeToNumber.LeftwardTape

namespace LeftTM0

/-- A leftward-unbounded TM0 machine -/
def Machine (Γ Λ : Type*) [Inhabited Γ] [Inhabited Λ] := TM0.Machine Γ Λ

/-- Configuration for leftward-unbounded TM -/
structure Cfg (Γ Λ : Type*) [Inhabited Γ] where
  q : Λ  -- Current state
  tape : LeftwardTape Γ  -- Leftward-constrained tape

-- Conversion functions between standard TM0 and LeftTM0
def cfg_to_tm0 [Inhabited Γ] (cfg : Cfg Γ Λ) : TM0.Cfg Γ Λ :=
  ⟨cfg.q, cfg.tape.tape⟩

def cfg_from_tm0 [Inhabited Γ] (cfg : TM0.Cfg Γ Λ) (h : tape_head_pos cfg.Tape ≤ 0) : Cfg Γ Λ :=
  ⟨cfg.q, ⟨cfg.Tape, tape_head_pos cfg.Tape, h⟩⟩

end LeftTM0
```

#### 3. `TMTapeToNumber/LeftTM0/Step.lean`

**Purpose**: Step function and execution semantics.

```lean
import TMTapeToNumber.LeftTM0.Machine

namespace LeftTM0

/-- Step function that enforces leftward constraints -/
def step [Inhabited Γ] (M : Machine Γ Λ) : Cfg Γ Λ → Option (Cfg Γ Λ) :=
  fun cfg ↦ 
    match TM0.step M (cfg_to_tm0 cfg) with
    | none => none
    | some cfg' => 
        if h : tape_head_pos cfg'.Tape ≤ 0 then
          some (cfg_from_tm0 cfg' h)
        else none  -- Halt if trying to go beyond position 0

/-- Multi-step execution -/
def steps [Inhabited Γ] (M : Machine Γ Λ) (n : ℕ) : Cfg Γ Λ → Cfg Γ Λ :=
  Function.iterate (step M) n

/-- Reachability relation -/
def Reaches [Inhabited Γ] (M : Machine Γ Λ) : Cfg Γ Λ → Cfg Γ Λ → Prop :=
  ReflTransGen (fun a b ↦ b ∈ step M a)

end LeftTM0
```

### Phase 2: Encoding and Examples (Files 4-6)

#### 4. `TMTapeToNumber/LeftTM0/Encoding.lean`

**Purpose**: Integer encoding from tape contents.

```lean
import TMTapeToNumber.LeftTM0.Step

namespace LeftTM0

/-- Encode a configuration's tape as a natural number -/
noncomputable def encode_config [Inhabited Γ] [DecidableEq Γ] (blank : Γ) 
    (cfg : Cfg Γ Λ) : ℕ :=
  cfg.tape.encode blank

/-- Properties of encoding -/
theorem encode_config_zero [Inhabited Γ] [DecidableEq Γ] (blank : Γ) (cfg : Cfg Γ Λ) :
    cfg.tape.tape.nth 0 = blank → encode_config blank cfg = 0 := sorry

theorem encode_config_single [Inhabited Γ] [DecidableEq Γ] (blank : Γ) (a : Γ) 
    (ha : a ≠ blank) (cfg : Cfg Γ Λ) :
    cfg.tape.tape.nth 0 = a → 
    (∀ i < 0, cfg.tape.tape.nth i = blank) →
    encode_config blank cfg = 1 := sorry

end LeftTM0
```

#### 5. `TMTapeToNumber/LeftTM0/Sequences.lean`

**Purpose**: Sequence generation infrastructure.

```lean
import TMTapeToNumber.LeftTM0.Encoding

namespace LeftTM0

/-- Generate sequence by running machine and encoding each step -/
noncomputable def sequence [Inhabited Γ] [DecidableEq Γ] (blank : Γ) 
    (M : Machine Γ Λ) (init_cfg : Cfg Γ Λ) : ℕ → ℕ :=
  fun n ↦ encode_config blank (steps M n init_cfg)

/-- Properties of sequences -/
theorem sequence_zero [Inhabited Γ] [DecidableEq Γ] (blank : Γ) 
    (M : Machine Γ Λ) (init_cfg : Cfg Γ Λ) :
    sequence blank M init_cfg 0 = encode_config blank init_cfg := rfl

theorem sequence_monotone_steps [Inhabited Γ] [DecidableEq Γ] (blank : Γ) 
    (M : Machine Γ Λ) (init_cfg : Cfg Γ Λ) (n m : ℕ) :
    steps M n init_cfg = steps M m init_cfg → 
    ∀ k ≥ n, sequence blank M init_cfg k = sequence blank M init_cfg n := sorry

end LeftTM0
```

#### 6. `TMTapeToNumber/LeftTM0/Examples/PowersOfTwo.lean`

**Purpose**: Powers of 2 generator implementation.

```lean
import TMTapeToNumber.LeftTM0.Sequences

namespace LeftTM0.Examples

/-- States for the powers of 2 machine -/
inductive PowersState where
  | q0  -- Scan right looking for rightmost 1  
  | q1  -- Move back left writing 1s

/-- The powers of 2 machine -/
def powers_machine : Machine Bool PowersState :=
  fun state symbol ↦
    match state, symbol with
    | PowersState.q0, true  => some (PowersState.q1, TM0.Stmt.write false)
    | PowersState.q0, false => some (PowersState.q0, TM0.Stmt.move Dir.left)
    | PowersState.q1, true  => some (PowersState.q1, TM0.Stmt.move Dir.left)  
    | PowersState.q1, false => some (PowersState.q0, TM0.Stmt.write true)

/-- Initial configuration: single 1 at position 0 -/
noncomputable def powers_initial : Cfg Bool PowersState :=
  ⟨PowersState.q0, ⟨Tape.mk₁ [true], 0, by norm_num⟩⟩

/-- The powers of 2 sequence -/
noncomputable def powers_sequence : ℕ → ℕ :=
  sequence false powers_machine powers_initial

-- Basic correctness properties
theorem powers_sequence_zero : powers_sequence 0 = 1 := by sorry

theorem powers_sequence_generates_powers : 
    ∀ n, ∃ k, powers_sequence n = 2^k := by sorry

end LeftTM0.Examples
```

### Phase 3: Theoretical Properties (Files 7-9)

#### 7. `TMTapeToNumber/Theorems/BasicProperties.lean`

**Purpose**: Fundamental properties and bounds.

```lean
import TMTapeToNumber.LeftTM0.Examples.PowersOfTwo

namespace LeftTM0.Theorems

-- Growth bounds
theorem sequence_growth_bound [Inhabited Γ] [DecidableEq Γ] [Fintype Γ] 
    (blank : Γ) (M : Machine Γ Λ) [Fintype Λ] (init_cfg : Cfg Γ Λ) (t : ℕ) :
    sequence blank M init_cfg t ≤ 2^(t + leftmost_initial_nonblank init_cfg) - 1 := sorry

-- Single step differences  
theorem sequence_step_diff [Inhabited Γ] [DecidableEq Γ] 
    (blank : Γ) (M : Machine Γ Λ) (init_cfg : Cfg Γ Λ) (t : ℕ) :
    ∃ i : ℕ, sequence blank M init_cfg (t+1) - sequence blank M init_cfg t ∈ 
      {0} ∪ {2^i, -(2^i : ℤ)} := sorry

end LeftTM0.Theorems
```

### Phase 4: Integration and Compatibility (Files 10-11)

#### 8. `TMTapeToNumber/Integration/TM0Equiv.lean`

**Purpose**: Equivalence theorems with standard TM0.

```lean
import TMTapeToNumber.LeftTM0.Sequences
import Mathlib.Computability.PostTuringMachine

namespace LeftTM0.Integration

/-- Any LeftTM0 machine can be simulated by a standard TM0 machine -/
theorem lefttm0_to_tm0_simulation [Inhabited Γ] [Inhabited Λ] 
    (M : LeftTM0.Machine Γ Λ) :
    ∃ (M' : TM0.Machine Γ Λ), ∀ cfg, 
      LeftTM0.Reaches M cfg₁ cfg₂ → TM0.Reaches M' (cfg_to_tm0 cfg₁) (cfg_to_tm0 cfg₂) := sorry

/-- Converse: TM0 machines with leftward-bounded execution simulate LeftTM0 -/
theorem tm0_to_lefttm0_simulation [Inhabited Γ] [Inhabited Λ] 
    (M : TM0.Machine Γ Λ) (leftward_bounded : ∀ cfg cfg', TM0.Reaches M cfg cfg' → 
      tape_head_pos cfg'.Tape ≤ max 0 (tape_head_pos cfg.Tape)) :
    ∃ (M' : LeftTM0.Machine Γ Λ), ∀ cfg₁ cfg₂,
      leftward_bounded_reaches M cfg₁ cfg₂ → LeftTM0.Reaches M' (adapt_cfg cfg₁) (adapt_cfg cfg₂) := sorry

end LeftTM0.Integration
```

#### 9. `TMTapeToNumber/Basic.lean` (Updated)

**Purpose**: Main exports and high-level interface.

```lean
-- Main exports
import TMTapeToNumber.LeftTM0.Sequences
import TMTapeToNumber.LeftTM0.Examples.PowersOfTwo
import TMTapeToNumber.Theorems.BasicProperties
import TMTapeToNumber.Integration.TM0Equiv

-- Re-export key definitions for easy access
namespace TMTapeToNumber

-- Core types
export LeftTM0 (Machine Cfg sequence)
export LeftwardTape (LeftwardTape)

-- Main example
export LeftTM0.Examples (powers_sequence powers_machine)

-- Key theorems
export LeftTM0.Theorems (sequence_growth_bound sequence_step_diff)

end TMTapeToNumber
```

## Implementation Roadmap

### Phase 1: Foundation (Week 1)
1. Implement `LeftwardTape.lean` with basic operations
2. Create `LeftTM0/Machine.lean` with type definitions
3. Implement `LeftTM0/Step.lean` with step function
4. Write basic tests to ensure compilation

### Phase 2: Core Functionality (Week 2)  
1. Implement `LeftTM0/Encoding.lean` with integer encoding
2. Create `LeftTM0/Sequences.lean` with sequence generation
3. Port powers of 2 example to new framework
4. Verify examples produce correct outputs

### Phase 3: Theory (Week 3)
1. Prove basic properties and bounds
2. Establish reachability theorems
3. Prove sequence properties
4. Document key theoretical results

### Phase 4: Integration (Week 4)
1. Prove equivalence with TM0
2. Create compatibility layer
3. Update documentation
4. Final testing and cleanup

## Benefits of This Approach

### Technical Benefits
1. **Proven Infrastructure**: Builds on mathlib's well-tested TM0 implementation
2. **Theorem Reuse**: Can adapt existing TM0 theorems with minimal changes
3. **Type Safety**: Leverages Lean's type system for position constraints
4. **Modularity**: Clean separation between tape constraints and machine logic

### Maintenance Benefits  
1. **Mathlib Compatibility**: Automatic benefits from mathlib improvements
2. **Standard Interface**: Familiar API for anyone who knows TM0
3. **Easier Debugging**: Can relate issues back to standard TM0 behavior
4. **Future Extensions**: Easy to add new machine variants

### Research Benefits
1. **Broader Context**: Clear relationship to standard computational models
2. **Transferable Results**: Theorems about our machines apply to broader class
3. **Collaboration**: Others can easily understand and extend the work
4. **Publication Ready**: Clean mathematical presentation

## Migration Strategy

### From Current Implementation
1. **Preserve Interface**: Keep existing function names where possible
2. **Gradual Transition**: Implement new version alongside old, then switch
3. **Test Compatibility**: Ensure examples produce same results
4. **Document Changes**: Clear explanation of what changed and why

### Compatibility Layer
If needed, provide adapter functions:
```lean
-- Compatibility with old interface
def old_LeftTape_to_new (old : OldLeftTape) : LeftwardTape Bool := sorry
def old_sequence_to_new (old_seq : ℕ → ℕ) : ℕ → ℕ := sorry
```

## Conclusion

This plan provides a robust foundation for leftward-unbounded Turing machine formalization that integrates cleanly with mathlib while maintaining our specific requirements. The modular structure allows for incremental development and easy extension to new examples and theoretical results.

The key insight is that we can achieve our goals more effectively by building on proven infrastructure rather than creating everything from scratch. This approach will result in more maintainable, extensible, and mathematically sound formalization.