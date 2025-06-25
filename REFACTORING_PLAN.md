# TM Tape to Number: Simplification Plan

## Overview

We're simplifying the project by removing unnecessary complexity. The key insight is that mathlib's TM0 already provides integer-indexed tapes, so we don't need custom wrapper types or position restrictions.

## Current Architecture (Overly Complex)

```
LeftwardTape (custom wrapper) → Encoding with bounds → Integer sequences
```

Problems:
- Unnecessary `LeftwardTape` wrapper type
- Artificial position constraints (≤ 0)
- Hard-coded encoding bounds (100)
- Complex proofs about position preservation

## New Architecture (Simple & Direct)

```
TM0.Tape → Direct encoding function → Integer sequences
```

Benefits:
- Use standard mathlib types directly
- No position restrictions needed
- No hard-coded bounds
- Simpler, more general proofs

## Key Changes

### 1. Remove `LeftwardTape` Structure

**Delete:**
- `TMTapeToNumber/LeftwardTape.lean`
- All references to `LeftwardTape`
- Position constraint checks

**Replace with:**
- Direct use of `TM0.Tape Bool`
- Standard `TM0.Cfg` configurations

### 2. Define Direct Encoding Function

```lean
-- Option 1: Natural mapping (position → exponent)
def encode_tape_v1 (tape : Tape Bool) : ℕ :=
  -- For each position i where tape.nth i = true, contribute 2^f(i)
  -- where f : ℤ → ℕ is a bijection
  sorry

-- Option 2: Absolute value mapping
def encode_tape_v2 (tape : Tape Bool) : ℕ :=
  -- Position i contributes 2^|i| when tape.nth i = true
  sorry

-- Option 3: Custom bijection for specific properties
def position_to_exponent : ℤ → ℕ
  | (n : ℕ) => 2 * n          -- 0, 1, 2, ... → 0, 2, 4, ...
  | -(n + 1 : ℕ) => 2 * n + 1 -- -1, -2, -3, ... → 1, 3, 5, ...

def encode_tape (tape : Tape Bool) : ℕ :=
  -- Using custom bijection for unique representation
  sorry
```

### 3. Simplify Module Structure

**New structure:**
```
TMTapeToNumber/
├── Basic.lean           # Public API
├── Encoding.lean        # Direct tape → ℕ encoding
├── Sequences.lean       # TM execution → sequence generation
├── Examples/
│   ├── PowersOfTwo.lean
│   ├── BinaryCounter.lean
│   └── Fibonacci.lean
└── Theorems/
    ├── EncodingProperties.lean
    └── SequenceProperties.lean
```

### 4. Update Core Definitions

```lean
-- Old (complex)
def sequence (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) : ℕ → ℕ :=
  fun n ↦ encode_config (steps M n init_cfg)

-- New (simple)
def sequence (M : TM0.Machine Bool Λ) (init : TM0.Cfg Bool Λ) : ℕ → ℕ :=
  fun n ↦ encode_tape (TM0.steps M n init).tape
```

## Execution Plan

### Phase 1: Create New Core Files

#### 1.1 Create `TMTapeToNumber/Encoding.lean`
- Define position-to-exponent bijection (e.g., interleaving: 0→0, -1→1, 1→2, -2→3, ...)
- Implement `encode_tape : TM0.Tape Bool → ℕ` using finite support
- Prove basic properties (injective on finite support tapes)

#### 1.2 Create `TMTapeToNumber/Sequences.lean`
- Define `sequence : TM0.Machine Bool Λ → TM0.Cfg Bool Λ → ℕ → ℕ`
- Use new `encode_tape` function directly
- Remove all position constraints

#### 1.3 Update `TMTapeToNumber/Basic.lean`
- Export new API functions
- Remove imports of LeftwardTape

### Phase 2: Remove Old Infrastructure

#### 2.1 Delete Files
- `TMTapeToNumber/LeftwardTape.lean`
- Entire `TMTapeToNumber/LeftTM0/` directory

#### 2.2 Update Imports
- Remove all references to LeftwardTape and LeftTM0
- Update to use standard TM0 types

### Phase 3: Update Theorems

#### 3.1 Create `TMTapeToNumber/Theorems/EncodingProperties.lean`
- Port encoding theorems without position constraints
- Add new theorems for bijection properties
- Simplify proofs (many become trivial)

#### 3.2 Create `TMTapeToNumber/Theorems/SequenceProperties.lean`
- Update sequence theorems for new encoding
- Remove position-related constraints

### Phase 4: Update Examples

#### 4.1 Create `TMTapeToNumber/Examples/PowersOfTwo.lean`
- Reimplement using standard TM0
- Show it generates sequence 1, 2, 4, 8, ...

#### 4.2 Add New Examples
- Binary counter example
- Other sequence generators

## Implementation Details

### Position-to-Exponent Bijection
```lean
def position_to_exponent : ℤ → ℕ
  | (n : ℕ) => 2 * n          -- 0, 1, 2, ... → 0, 2, 4, ...
  | -(n + 1 : ℕ) => 2 * n + 1 -- -1, -2, -3, ... → 1, 3, 5, ...
```

### New Encoding Function
```lean
def encode_tape (tape : TM0.Tape Bool) : ℕ :=
  -- Sum over positions where tape has true
  -- Using finite support assumption
```

## Benefits of This Approach
1. **Simplicity**: Removes entire abstraction layer
2. **Generality**: Works with any tape positions
3. **Maintainability**: Less code, simpler proofs
4. **Flexibility**: Easy to experiment with different encodings

## Risks & Mitigations
- **Risk**: Breaking existing proofs
  - **Mitigation**: Careful mapping of old theorems to new structure
- **Risk**: Missing edge cases in new encoding
  - **Mitigation**: Comprehensive testing with examples

## Success Criteria
- All tests pass
- Examples produce correct sequences
- Code is significantly simpler
- No position restrictions remain

## Advantages of This Approach

1. **Simplicity**: Removes entire layers of abstraction
2. **Generality**: Works with any tape positions, not just ≤ 0
3. **Maintainability**: Less code to maintain and verify
4. **Flexibility**: Easy to experiment with different encodings
5. **Mathlib alignment**: Uses standard mathlib types directly

## Potential Encoding Schemes

### Bijection Options

1. **Standard Cantor pairing**: Maps ℤ → ℕ uniquely
2. **Interleaving**: Even naturals for non-negative, odd for negative
3. **Spiral**: 0, -1, 1, -2, 2, ... → 0, 1, 2, 3, 4, ...

### Encoding Properties to Preserve

- Injective on tapes with finite support
- Computable/decidable where possible
- Natural relationship to machine operations

## Questions to Resolve

1. Which position → exponent mapping is most natural?
2. Do we want any constraints on machines (e.g., finite support)?
3. Should encoding be parameterized by the mapping function?

## Expected Outcome

A much cleaner, more maintainable project that:
- Achieves the same mathematical goals
- Uses standard mathlib infrastructure
- Has simpler, more general proofs
- Is easier to extend and experiment with