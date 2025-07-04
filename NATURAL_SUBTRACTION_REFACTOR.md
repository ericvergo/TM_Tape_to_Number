# Natural Subtraction Refactoring Plan

## Problem Statement

The codebase has multiple instances where natural number subtraction is used for encoding differences, which causes information loss when the encoding decreases. In natural numbers, `a - b = 0` when `a < b`, losing the actual difference value.

## Key Issues Identified

### 1. **`sequence_diff_is_power_of_two`** in SequenceProperties.lean
- Current: `∃ k : ℕ, seq (t + 1) - seq t = 0 ∨ seq (t + 1) - seq t = 2^k`
- Issue: Loses information when sequence decreases

### 2. **`encode_diff_at_write`** in EncodingDifference.lean
- Current: `let diff := encode_config cfg' - encode_config cfg` (natural subtraction)
- Issue: `diff = 0` when `cfg' < cfg`, but then `(diff : ℤ) ≠ -2^k`

### 3. **`encode_write_diff_value`** in EncodingProperties.lean
- Current: Claims `diff = 0` when writing false over true
- Issue: Should capture that it decreased by `2^k`

### 4. **`encode_diff_at_write_simple`** in EncodingProperties.lean
- Current: `(cfg.tape.nth 0 = true ∧ a = false ∧ diff = 0)`
- Issue: Misses the actual decrease amount

## Recommended Solutions

### 1. Define Integer Difference Function
```lean
def encode_diff (cfg cfg' : Cfg Bool Λ) : ℤ :=
  (encode_config cfg' : ℤ) - (encode_config cfg : ℤ)
```

### 2. Refactor Core Lemmas

#### `encode_diff_at_write` (EncodingDifference.lean)
```lean
lemma encode_diff_at_write (cfg : Cfg Bool Λ) (a : Bool) :
    let cfg' := ⟨cfg.q, cfg.tape.write a⟩
    let diff := encode_diff cfg cfg'
    diff = 0 ∨ ∃ k : ℕ, diff = 2^k ∨ diff = -2^k := by
```

#### `sequence_diff_is_power_of_two` (SequenceProperties.lean)
```lean
lemma sequence_diff_is_power_of_two (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ) :
    let seq := sequence M init_cfg
    seq (t + 1) = seq t ∨ 
    (∃ k : ℕ, seq (t + 1) = seq t + 2^k) ∨
    (∃ k : ℕ, seq t ≥ 2^k ∧ seq (t + 1) = seq t - 2^k) := by
```

#### `encode_write_diff_value` (EncodingProperties.lean)
```lean
lemma encode_write_diff_value (cfg : Cfg Bool Λ) (a : Bool) :
    let cfg' := ⟨cfg.q, cfg.tape.write a⟩
    let diff := encode_diff cfg cfg'
    let k := Int.natAbs (-cfg.tape.head_pos)
    (cfg.tape.nth 0 = a → diff = 0) ∧
    (cfg.tape.nth 0 = false ∧ a = true → diff = 2^k) ∧
    (cfg.tape.nth 0 = true ∧ a = false → diff = -(2^k : ℤ)) := by
```

### 3. Update Dependent Lemmas

Need to update lemmas that depend on the natural subtraction versions to use the integer difference versions.

## Execution Plan

1. **Phase 1**: Add integer difference definition
   - Add `encode_diff` function to Basic.lean or EncodingDifference.lean

2. **Phase 2**: Refactor core encoding lemmas
   - Update `encode_diff_at_write` to use integer differences
   - Update related helper lemmas

3. **Phase 3**: Refactor sequence properties
   - Update `sequence_diff_is_power_of_two` to avoid natural subtraction
   - Update dependent lemmas

4. **Phase 4**: Fix encoding properties
   - Update `encode_write_diff_value` to correctly handle decreases
   - Update `encode_diff_at_write_simple` similarly

5. **Phase 5**: Update proofs
   - Fix proofs that rely on the old natural subtraction behavior
   - Simplify proofs that had to work around the subtraction issue

## Benefits

1. **Correctness**: Captures actual differences instead of truncating to 0
2. **Simplicity**: Removes need for complex workarounds in proofs
3. **Clarity**: Makes the mathematical intent clearer
4. **Consistency**: Uniform treatment of increases and decreases