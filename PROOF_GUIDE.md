# Detailed Proof Guide for Binary Step Sequences

This guide provides detailed strategies for completing the 10 remaining proofs in the binary step sequences formalization.

## 🎯 Overall Proof Architecture

The proofs form a dependency chain:
```
extract_k_value_pow → binary_step_diff_power_of_two
                    ↓
encode_diff_at_write → sequence_diff_is_power_of_two → sequence_k_equals_position
                                                     ↓
                                           sequence_k_bound & sequence_k_movement_constraint
                                                     ↓
                                         tm_sequence_is_binary_step_sequence (already done!)
                                                     ↓
                                         binary_step_sequence_growth_bound
                                                     ↓
                     construct_tm_for_sequence → finite_binary_step_sequence_generable
```

## 📝 Detailed Proof Strategies

### 1. `extract_k_value_pow` ✅ Foundation
**File**: `BinaryStepSequences/Basic.lean:108`

```lean
theorem extract_k_value_pow (k : ℕ) :
    extract_k_value (2^k : ℤ) = some k ∧ extract_k_value (-(2^k : ℤ)) = some k := by
  constructor
  · -- Case: 2^k
    simp only [extract_k_value]
    -- 2^k ≠ 0
    have h_ne : (2^k : ℤ) ≠ 0 := by
      simp [pow_ne_zero]
    simp [h_ne]
    -- Int.natAbs (2^k) = 2^k
    have h_abs : Int.natAbs (2^k : ℤ) = 2^k := by
      simp [Int.natAbs_of_nonneg, Nat.zero_le]
    simp [h_abs]
    constructor
    · -- 2^k > 0
      exact Nat.pow_pos (by norm_num : 0 < 2) k
    · constructor
      · -- (2^k).land (2^k - 1) = 0
        -- This is the key property: 2^k in binary is 1 followed by k zeros
        -- 2^k - 1 in binary is k ones
        -- Their AND is 0
        exact Nat.land_pow_two_sub_one k
      · -- (2^k).log2 = k
        exact Nat.log2_pow (by norm_num : 1 < 2) k
  · -- Case: -(2^k)
    -- Similar proof using Int.natAbs_neg
```

**Key Mathlib theorems**:
- `Nat.pow_pos`: Shows 2^k > 0
- `Nat.land_pow_two_sub_one`: Shows 2^k AND (2^k-1) = 0
- `Nat.log2_pow`: Shows log₂(2^k) = k
- `Int.natAbs_neg`: Shows |(-n)| = |n|

### 2. `binary_step_diff_power_of_two` ✅ Easy
**File**: `BinaryStepSequences/Basic.lean:121`

```lean
theorem binary_step_diff_power_of_two (s : ℕ → ℕ) (h : is_binary_step_sequence s) (t : ℕ) :
    sequence_difference s t = 0 ∨ is_power_of_two (Int.natAbs (sequence_difference s t)) := by
  -- Extract from h.2
  have h_diff := h.2.1 t
  cases h_diff with
  | inl h_zero =>
    left
    exact h_zero
  | inr h_pow =>
    right
    obtain ⟨k, h_k⟩ := h_pow
    use k
    cases h_k with
    | inl h_pos =>
      -- sequence_difference s t = 2^k
      rw [h_pos]
      simp [Int.natAbs_of_nonneg]
    | inr h_neg =>
      -- sequence_difference s t = -(2^k)
      rw [h_neg]
      simp [Int.natAbs_neg]
```

### 3. `encode_diff_at_write` 🔑 Critical
**File**: `BinaryStepSequences/Theorems.lean:14`

```lean
lemma encode_diff_at_write (cfg : Cfg Bool Λ) (cfg' : Cfg Bool Λ) 
    (h_step : ∃ a, cfg' = ⟨cfg.q, cfg.tape.write a⟩) :
    encode_config cfg' - encode_config cfg = 0 ∨
    ∃ k : ℕ, (encode_config cfg' : ℤ) - encode_config cfg = 2^k ∨ 
             (encode_config cfg' : ℤ) - encode_config cfg = -(2^k : ℤ) := by
  obtain ⟨a, ha⟩ := h_step
  rw [ha]
  simp only [encode_config]
  
  -- Key insight: writing only changes the bit at head position
  let pos := cfg.tape.head_pos
  have h_pos_nonpos : pos ≤ 0 := cfg.tape.head_nonpos
  let k := Int.natAbs (-pos)
  
  -- Case split on what we're writing over
  cases h_read : cfg.tape.read with
  | false =>
    -- Currently false at head position
    cases a with
    | false =>
      -- Writing false over false: no change
      left
      simp [LeftwardTape.write, encode]
      -- Use encode_write_false_at_false
    | true =>
      -- Writing true over false: adds 2^k
      right
      use k
      left
      -- Show encoding increases by 2^k
      have h_inc : encode (cfg.tape.write true) = encode cfg.tape + 2^k := by
        apply encode_write_true_at_false
        exact h_read
      simp [h_inc]
      
  | true =>
    -- Currently true at head position
    cases a with
    | true =>
      -- Writing true over true: no change
      left
      simp [LeftwardTape.write, encode]
      -- Use encode_write_true_at_true
    | false =>
      -- Writing false over true: removes 2^k
      right
      use k
      right
      -- Show encoding decreases by 2^k
      have h_dec : encode (cfg.tape.write false) = encode cfg.tape - 2^k := by
        apply encode_write_false_at_true
        exact h_read
      simp [h_dec]
      ring
```

**Required lemmas from LeftwardEncoding**:
- `encode_write_true_at_false`: Writing true where false adds 2^|pos|
- `encode_write_false_at_true`: Writing false where true subtracts 2^|pos|
- These may need to be added if not already present

### 4. `sequence_diff_is_power_of_two` 
**File**: `BinaryStepSequences/Theorems.lean:22`

```lean
lemma sequence_diff_is_power_of_two (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ) :
    sequence_difference (sequence M init_cfg) t = 0 ∨
    ∃ k : ℕ, sequence_difference (sequence M init_cfg) t = 2^k ∨ 
             sequence_difference (sequence M init_cfg) t = -(2^k : ℤ) := by
  simp only [sequence_difference, sequence]
  
  -- Consider what happens at step t
  cases h_step : step M (steps M t init_cfg) with
  | none =>
    -- Machine halted, configuration unchanged
    left
    simp [step_or_stay, h_step]
    ring
  | some cfg' =>
    -- Machine took a step
    have h_next : steps M (t + 1) init_cfg = cfg' := by
      simp [steps_succ, step_or_stay, h_step]
    
    -- Analyze what the machine did
    -- Extract the action from the machine
    have h_cfg : cfg' = step_result M (steps M t init_cfg) := by
      -- From h_step
      sorry
    
    -- Case on whether it was a move or write
    cases h_action : M (steps M t init_cfg).q (steps M t init_cfg).tape.read with
    | none =>
      -- No action, shouldn't happen given h_step
      sorry
    | some (q', stmt) =>
      cases stmt with
      | move dir =>
        -- Movement doesn't change encoding
        left
        have h_move : encode_config cfg' = encode_config (steps M t init_cfg) := by
          -- Use encode_move_preserves
          sorry
        simp [h_move]
        ring
      | write a =>
        -- Writing changes encoding by ±2^k
        apply encode_diff_at_write
        use a
        -- Show cfg' is the result of writing
        sorry
```

### 5-7. Position and Movement Lemmas
These follow naturally from the head movement bounds already proven in `LeftwardSequences/Theorems.lean`.

### 8. `binary_step_sequence_growth_bound` 🎯 Main Result
**File**: `BinaryStepSequences/Theorems.lean:104`

```lean
theorem binary_step_sequence_growth_bound (s : ℕ → ℕ) (h : is_binary_step_sequence s) :
    ∀ t : ℕ, s t < 2^(t + 1) := by
  intro t
  -- Key insight: s_t = s_0 + sum of differences
  have h_sum : s t = s 0 + (Finset.range t).sum (fun i => 
    if h : s (i + 1) > s i then s (i + 1) - s i else 0) := by
    -- Telescoping sum
    sorry
  
  -- s_0 = 0
  rw [h.1] at h_sum
  simp at h_sum
  
  -- Each positive difference is at most 2^i
  have h_bound_diff : ∀ i < t, 
    (if h : s (i + 1) > s i then s (i + 1) - s i else 0) ≤ 2^i := by
    intro i hi
    split_ifs with h_inc
    · -- s (i + 1) > s i, so difference is positive
      have h_diff := h.2.1 i
      cases h_diff with
      | inl h_zero =>
        -- Contradiction: difference is 0 but s(i+1) > s(i)
        sorry
      | inr h_pow =>
        obtain ⟨k, hk⟩ := h_pow
        cases hk with
        | inl h_pos =>
          -- difference = 2^k and k ≤ i
          have h_k_bound : k ≤ i := by
            -- Use h.2.2 (movement constraints)
            sorry
          -- Therefore difference ≤ 2^i
          sorry
        | inr h_neg =>
          -- Contradiction: negative difference but s(i+1) > s(i)
          sorry
    · -- No increase, contributes 0
      simp
  
  -- Sum is at most geometric series
  have h_sum_bound : (Finset.range t).sum (fun i => 
    if h : s (i + 1) > s i then s (i + 1) - s i else 0) ≤ 
    (Finset.range t).sum (fun i => 2^i) := by
    apply Finset.sum_le_sum
    intros i hi
    exact h_bound_diff i (Finset.mem_range.mp hi)
  
  -- Geometric series sum
  have h_geom : (Finset.range t).sum (fun i => 2^i) = 2^t - 1 := by
    -- Use Finset.sum_range_pow
    sorry
  
  -- Conclude
  calc s t 
    = 0 + (Finset.range t).sum _ := h_sum
    _ ≤ (Finset.range t).sum (fun i => 2^i) := by simp [h_sum_bound]
    _ = 2^t - 1 := h_geom
    _ < 2^t := by omega
    _ < 2^(t + 1) := by simp [pow_lt_pow_right]
```

### 9-10. Construction Proofs
These require building the actual Turing machine that generates a given sequence. The key is to use the path construction helpers already defined.

## 🔨 Implementation Tips

### Working with Encodings
```lean
-- Common pattern for encode proofs
have h_encode : encode tape' = encode tape + 2^k := by
  rw [encode]
  simp only [LeftwardTape.true_positions_absolute]
  -- Work with Finset.sum
```

### Working with Positions
```lean
-- Remember: positions are non-positive
have h_pos : cfg.tape.head_pos ≤ 0 := cfg.tape.head_nonpos
-- Absolute value of position
let k := Int.natAbs (-cfg.tape.head_pos)
```

### Proof Debugging
1. Use `sorry` liberally to check types
2. Build incrementally with `have` statements
3. Use `#print` to see definitions
4. Check similar proofs in LeftwardEncoding/Properties.lean

## 📚 References

Key files to study:
- `LeftwardEncoding/Properties.lean`: Similar encoding proofs
- `LeftwardSequences/Theorems.lean`: Head movement bounds
- Mathlib's `Data.Nat.Log`: For logarithm properties
- Mathlib's `Data.Nat.Bitwise`: For bitwise operations

## 🎯 Success Criteria

Each proof is complete when:
1. No `sorry` remains
2. It compiles without errors
3. The proof is reasonably efficient (no timeout)
4. The proof follows the intended strategy

Start with `extract_k_value_pow` and work through in order!