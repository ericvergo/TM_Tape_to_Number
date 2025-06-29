import TMTapeToNumber.BinaryStepSequences.Basic
import TMTapeToNumber.LeftwardSequences.Theorems
import TMTapeToNumber.LeftTM0.LeftwardTape
import Mathlib.Data.Nat.Log

namespace LeftTM0

open LeftTM0.Theorems

variable {Λ : Type*} [Inhabited Λ]

-- Helper lemmas for encode_diff_at_write

open LeftwardTape

-- Forward Characterization: TM sequences are binary step sequences

/-- The difference in encoding when writing at a position is ±2^k where k is the absolute position -/
lemma encode_diff_at_write (cfg : Cfg Bool Λ) (cfg' : Cfg Bool Λ)
    (h_step : ∃ a, cfg' = ⟨cfg.q, cfg.tape.write a⟩) :
    encode_config cfg' - encode_config cfg = 0 ∨
    ∃ k : ℕ, (encode_config cfg' : ℤ) - encode_config cfg = 2^k ∨
             (encode_config cfg' : ℤ) - encode_config cfg = -(2^k : ℤ) := by
  -- Extract the value being written
  obtain ⟨a, h_cfg'⟩ := h_step
  rw [h_cfg']
  unfold encode_config

  -- The encoding is a sum over positions with true values
  -- Writing at the head position either:
  -- 1. Changes false to true (adds 2^k)
  -- 2. Changes true to false (subtracts 2^k)
  -- 3. Writes the same value (no change)
  -- where k = |head_pos|

  -- The key insight: write only changes the value at the head position
  -- Let's analyze the encoding change

  -- Get the current value at the head position
  let current_val := cfg.tape.nth 0  -- 0 is relative position of head

  -- The encoding sums over all positions with true values
  -- Writing at head position (absolute position cfg.tape.head_pos) changes only that bit

  -- Case analysis on the current and new values
  by_cases h_current : current_val = true
  · -- Current value is true
    by_cases h_new : a = true
    · -- Writing true over true: no change
      left
      -- Show encoding doesn't change
      -- Show the encoding difference is 0
      simp only [h_cfg']
      have h_read : cfg.tape.tape.nth 0 = current_val := rfl
      rw [h_current] at h_read
      -- h_read : cfg.tape.tape.nth 0 = true
      -- We're writing a = true (from h_new)
      -- So the tape doesn't change
      have h_write_eq : cfg.tape.tape.write a = cfg.tape.tape := by
        rw [h_new]  -- Now we need to show cfg.tape.tape.write true = cfg.tape.tape
        apply Turing.Tape.ext
        intro i
        by_cases h_pos : i = 0
        · -- At position 0, we're writing true where there's already true
          rw [h_pos, Turing.Tape.write_nth]
          simp
          exact h_read
        · -- At other positions, write doesn't change the value
          rw [Turing.Tape.write_nth]
          simp [h_pos]
      simp only [encode_config, LeftwardTape.write]
      rw [h_write_eq]
      simp
    · -- Writing false over true: removes 2^k
      right
      use Int.natAbs (-cfg.tape.head_pos)
      right
      -- The encoding decreases by 2^|head_pos|
      have h_a_false : a = false := by
        cases a with
        | false => rfl
        | true => 
          -- If a = true, then h_new says ¬a = true, i.e., ¬true = true
          -- This is False
          exfalso
          exact h_new rfl
      
      -- The key insight: encoding sums 2^|pos| for all positions ≤ 0 with true
      -- Writing false at head position removes that contribution
      
      -- Unfold the encoding definitions
      simp only [encode_config, LeftwardTape.encode, LeftwardTape.write]
      
      -- The encoding changes by removing the contribution from the head position
      -- First, let's establish that the head is at absolute position cfg.tape.head_pos
      -- and since head_pos ≤ 0, we have |head_pos| = -head_pos
      
      -- The new tape has false at head position, old tape has true
      -- So true_positions_absolute of new tape = old tape's true_positions \ {cfg.tape.head_pos}
      
      -- Need to show the difference is -2^(-cfg.tape.head_pos)
      have h_head_pos_nonpos : cfg.tape.head_pos ≤ 0 := cfg.tape.head_nonpos
      
      -- The key insight: writing false at position 0 (relative) removes cfg.tape.head_pos from true_positions
      -- because nth_absolute cfg.tape.head_pos = nth 0 = current_val = true (old)
      -- and after writing false, nth_absolute cfg.tape.head_pos = false (new)
      
      -- Step 1: The old tape has true at absolute position cfg.tape.head_pos
      have h_old_true : cfg.tape.nth_absolute cfg.tape.head_pos = true := by
        simp only [nth_absolute, sub_self]
        -- nth_absolute head_pos = nth (head_pos - head_pos) = nth 0
        -- and current_val = cfg.tape.nth 0 = true
        exact h_current
      
      -- Step 2: The new tape has false at absolute position cfg.tape.head_pos
      have h_new_false : (cfg.tape.write a).nth_absolute cfg.tape.head_pos = false := by
        simp only [nth_absolute, write, sub_self]
        rw [Turing.Tape.write_nth]
        simp only [if_pos rfl]
        exact h_a_false
      
      -- Step 3: Other positions are unchanged by write
      have h_unchanged : ∀ i ≠ cfg.tape.head_pos, 
        (cfg.tape.write a).nth_absolute i = cfg.tape.nth_absolute i := by
        intro i hi
        simp only [nth_absolute, write]
        rw [Turing.Tape.write_nth]
        split_ifs with h
        · -- If i - head_pos = 0, then i = head_pos, contradiction
          have : i = cfg.tape.head_pos := by linarith
          contradiction
        · rfl
      
      -- Step 4: Show that true_positions differ only at cfg.tape.head_pos
      have h_diff : (cfg.tape.write a).true_positions_absolute = 
                    cfg.tape.true_positions_absolute \ {cfg.tape.head_pos} := by
        ext i
        simp only [true_positions_absolute, Finset.mem_filter, Set.Finite.mem_toFinset, 
                   Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · intro ⟨hi_mem, hi_le, hi_true⟩
          constructor
          · -- Show i ∈ cfg.tape.true_positions_absolute
            refine ⟨?_, hi_le, ?_⟩
            · simp only [Set.mem_setOf, has_content_at_absolute]
              by_cases h : i = cfg.tape.head_pos
              · rw [h, h_old_true]
                trivial
              · rw [← h_unchanged i h]
                simp only [has_content_at_absolute] at hi_mem
                exact hi_mem
            · by_cases h : i = cfg.tape.head_pos
              · rw [h] at hi_true
                rw [h_new_false] at hi_true
                simp at hi_true
              · rw [← h_unchanged i h]
                exact hi_true
          · -- Show i ≠ cfg.tape.head_pos
            intro h
            rw [h] at hi_true
            rw [h_new_false] at hi_true
            simp at hi_true
        · intro ⟨⟨hi_mem, hi_le, hi_true⟩, hi_neq⟩
          refine ⟨?_, hi_le, ?_⟩
          · simp only [Set.mem_setOf, has_content_at_absolute]
            rw [h_unchanged i hi_neq]
            simp only [has_content_at_absolute] at hi_mem
            exact hi_mem
          · rw [h_unchanged i hi_neq]
            exact hi_true
      
      -- Step 5: Calculate the encoding difference
      -- The encoding of the new tape structure
      have h_new_encode : (⟨Turing.Tape.write a cfg.tape.tape, 
                           cfg.tape.head_pos,
                           cfg.tape.head_nonpos⟩ : LeftwardTape Bool).true_positions_absolute = 
                          (cfg.tape.write a).true_positions_absolute := by
        -- Both are the same tape structure
        rfl
      
      -- Rewrite the goal using this equality
      rw [h_new_encode, h_diff]
      
      -- The sum over A \ {x} = sum over A - (if x ∈ A then 2^f(x) else 0)
      have h_in : cfg.tape.head_pos ∈ cfg.tape.true_positions_absolute := by
        simp only [true_positions_absolute, Finset.mem_filter, Set.Finite.mem_toFinset]
        refine ⟨?_, h_head_pos_nonpos, h_old_true⟩
        simp only [Set.mem_setOf, has_content_at_absolute, h_old_true]
        trivial
      
      -- Use the formula: sum(A) = sum(A\{x}) + sum({x}) when x ∈ A
      have h_sum_eq : (∑ i ∈ cfg.tape.true_positions_absolute, 2 ^ (-i).natAbs) =
                      (∑ i ∈ cfg.tape.true_positions_absolute \ {cfg.tape.head_pos}, 2 ^ (-i).natAbs) +
                      (∑ i ∈ ({cfg.tape.head_pos} : Finset ℤ), 2 ^ (-i).natAbs) := by
        rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr h_in)]
      
      rw [h_sum_eq]
      simp only [Finset.sum_singleton]
      -- Now we have: sum(A\{x}) - (sum(A\{x}) + 2^|x|) = -2^|x|
      -- Cast to integers for the arithmetic
      push_cast
      ring
  · -- Current value is false
    by_cases h_new : a = true
    · -- Writing true over false: adds 2^k
      right
      use Int.natAbs (-cfg.tape.head_pos)
      left
      -- The encoding increases by 2^|head_pos|
      -- The key insight: encoding sums 2^|pos| for all positions ≤ 0 with true
      -- Writing true at head position adds that contribution
      
      -- Similar to the previous case, but now we're adding instead of removing
      have h_current_false : current_val = false := by
        cases h_current_eq : current_val with
        | false => rfl
        | true => 
          -- In this case branch, current_val = true (from h_current_eq)
          -- But h_current says ¬current_val = true, i.e., ¬true = true
          -- This is a contradiction
          exfalso
          rw [h_current_eq] at h_current
          exact h_current rfl
      
      have h_a_true : a = true := by
        cases a with
        | false => 
          -- If a = false, then h_new : a = true says false = true
          -- This is impossible
          exact absurd h_new (Bool.false_ne_true)
        | true => rfl
      
      -- The old tape has false at head position, new tape has true
      have h_old_false : cfg.tape.nth_absolute cfg.tape.head_pos = false := by
        simp only [nth_absolute, sub_self]
        exact h_current_false
      
      have h_new_true : (cfg.tape.write a).nth_absolute cfg.tape.head_pos = true := by
        simp only [nth_absolute, write, sub_self]
        rw [Turing.Tape.write_nth]
        simp only [if_pos rfl]
        exact h_a_true
      
      -- Other positions unchanged (same as before)
      have h_unchanged : ∀ i ≠ cfg.tape.head_pos, 
        (cfg.tape.write a).nth_absolute i = cfg.tape.nth_absolute i := by
        intro i hi
        simp only [nth_absolute, write]
        rw [Turing.Tape.write_nth]
        split_ifs with h
        · have : i = cfg.tape.head_pos := by linarith
          contradiction
        · rfl
      
      -- Show that true_positions differ only by adding cfg.tape.head_pos
      have h_diff : (cfg.tape.write a).true_positions_absolute = 
                    cfg.tape.true_positions_absolute ∪ {cfg.tape.head_pos} := by
        ext i
        simp only [true_positions_absolute, Finset.mem_filter, Set.Finite.mem_toFinset, 
                   Finset.mem_union, Finset.mem_singleton]
        constructor
        · intro ⟨hi_mem, hi_le, hi_true⟩
          by_cases h : i = cfg.tape.head_pos
          · right
            exact h
          · left
            refine ⟨?_, hi_le, ?_⟩
            · simp only [Set.mem_setOf, has_content_at_absolute]
              rw [← h_unchanged i h]
              simp only [has_content_at_absolute] at hi_mem
              exact hi_mem
            · -- We need to show cfg.tape.nth_absolute i = true
              -- We know (cfg.tape.write a).nth_absolute i = true
              -- and i ≠ cfg.tape.head_pos, so h_unchanged applies
              have : cfg.tape.nth_absolute i = (cfg.tape.write a).nth_absolute i := by
                rw [h_unchanged i h]
              rw [this]
              exact hi_true
        · intro hi
          cases hi with
          | inl hi_in =>
            obtain ⟨hi_mem, hi_le, hi_true⟩ := hi_in
            refine ⟨?_, hi_le, ?_⟩
            · simp only [Set.mem_setOf, has_content_at_absolute]
              rw [h_unchanged i ?_]
              · simp only [has_content_at_absolute] at hi_mem
                exact hi_mem
              · -- Need to show i ≠ cfg.tape.head_pos
                intro h_eq
                rw [h_eq] at hi_true
                rw [h_old_false] at hi_true
                simp at hi_true
            · rw [h_unchanged i ?_]
              · exact hi_true
              · intro h_eq
                rw [h_eq] at hi_true
                rw [h_old_false] at hi_true
                simp at hi_true
          | inr hi_eq =>
            rw [hi_eq]
            refine ⟨?_, cfg.tape.head_nonpos, h_new_true⟩
            simp only [Set.mem_setOf, has_content_at_absolute, h_new_true]
            trivial
      
      -- Calculate the encoding difference
      have h_new_encode : (⟨Turing.Tape.write a cfg.tape.tape, 
                           cfg.tape.head_pos,
                           cfg.tape.head_nonpos⟩ : LeftwardTape Bool).true_positions_absolute = 
                          (cfg.tape.write a).true_positions_absolute := by
        rfl
      
      -- First unfold the encoding
      simp only [encode_config, LeftwardTape.encode]
      -- Now we can use h_diff to rewrite the LHS
      rw [h_diff]
      
      -- Show head_pos is not in the old true_positions (since it has false)
      have h_not_in : cfg.tape.head_pos ∉ cfg.tape.true_positions_absolute := by
        simp only [true_positions_absolute, Finset.mem_filter, Set.Finite.mem_toFinset]
        push_neg
        intro _ _
        -- We need to show cfg.tape.nth_absolute cfg.tape.head_pos ≠ true
        -- We have h_old_false : cfg.tape.nth_absolute cfg.tape.head_pos = false
        rw [h_old_false]
        simp
      
      -- Use the formula: sum(A ∪ {x}) = sum(A) + sum({x}) when x ∉ A
      have h_sum_eq : (∑ i ∈ cfg.tape.true_positions_absolute ∪ {cfg.tape.head_pos}, 2 ^ (-i).natAbs) =
                      (∑ i ∈ cfg.tape.true_positions_absolute, 2 ^ (-i).natAbs) +
                      (∑ i ∈ ({cfg.tape.head_pos} : Finset ℤ), 2 ^ (-i).natAbs) := by
        rw [Finset.sum_union]
        exact Finset.disjoint_singleton_right.mpr h_not_in
      
      rw [h_sum_eq]
      simp only [Finset.sum_singleton]
      -- Now we have: (sum(A) + 2^|x|) - sum(A) = 2^|x|
      -- This is basic arithmetic: (a + b) - a = b
      -- TODO: Fix this arithmetic
      sorry
    · -- Writing false over false: no change
      left
      -- Show encoding doesn't change
      -- Show the encoding difference is 0
      simp only [h_cfg']
      have h_read : cfg.tape.tape.nth 0 = current_val := rfl
      -- h_current says current_val ≠ true, so current_val = false (for Bool)
      -- h_new says a ≠ true, so a = false
      have h_current_false : current_val = false := by
        cases h_current_eq : current_val with
        | false => rfl
        | true => 
          -- In this case branch, current_val = true (from h_current_eq)
          -- But h_current says ¬current_val = true, i.e., ¬true = true
          -- This is a contradiction
          exfalso
          rw [h_current_eq] at h_current
          exact h_current rfl
      have h_a_false : a = false := by
        cases a with
        | false => rfl
        | true => 
          -- If a = true, then h_new says ¬a = true, i.e., ¬true = true
          -- This is False
          exfalso
          exact h_new rfl
      rw [h_current_false] at h_read
      -- h_read : cfg.tape.tape.nth 0 = false
      -- We're writing a = false (from h_a_false)
      -- So the tape doesn't change
      have h_write_eq : cfg.tape.tape.write a = cfg.tape.tape := by
        rw [h_a_false]  -- Now we need to show cfg.tape.tape.write false = cfg.tape.tape
        apply Turing.Tape.ext
        intro i
        by_cases h_pos : i = 0
        · -- At position 0, we're writing false where there's already false
          rw [h_pos, Turing.Tape.write_nth]
          simp
          exact h_read
        · -- At other positions, write doesn't change the value
          rw [Turing.Tape.write_nth]
          simp [h_pos]
      simp only [encode_config, LeftwardTape.write]
      rw [h_write_eq]
      simp

/-- One step of a TM changes the encoding by 0 or ±2^k -/
lemma sequence_diff_is_power_of_two (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ) :
    sequence_difference (sequence M init_cfg) t = 0 ∨
    ∃ k : ℕ, sequence_difference (sequence M init_cfg) t = 2^k ∨
             sequence_difference (sequence M init_cfg) t = -(2^k : ℤ) := by
  unfold sequence_difference sequence
  -- sequence_difference s t = s(t+1) - s(t)
  -- = encode_config (steps M (t+1) init_cfg) - encode_config (steps M t init_cfg)

  -- The key insight: one step either moves (no encoding change) or writes (±2^k change)
  -- We need to analyze the transition at step t

  sorry -- TODO: Complete proof by case analysis
  -- Key steps:
  -- 1. steps M (t + 1) init_cfg = step_or_stay M (steps M t init_cfg)
  -- 2. If step returns none, then encoding doesn't change (difference is 0)
  -- 3. If step returns some cfg', analyze the transition:
  --    - If it's a move, encoding doesn't change (use encoding preservation lemma)
  --    - If it's a write, use encode_diff_at_write lemma

/-- The k value in a sequence change equals the absolute position where the write occurred -/
lemma sequence_k_equals_position (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ)
    (h_change : sequence M init_cfg (t + 1) ≠ sequence M init_cfg t) :
    ∃ k : ℕ, (sequence_difference (sequence M init_cfg) t = 2^k ∨
              sequence_difference (sequence M init_cfg) t = -(2^k : ℤ)) ∧
              k = Int.natAbs (-(steps M t init_cfg).tape.head_pos) := by
  -- Since the sequence changed, the machine must have written at step t
  -- The change is at the head position, which is an absolute position
  -- The encoding formula uses 2^|position| for each true position
  sorry -- TODO: Complete proof
  -- Key steps:
  -- 1. h_change implies a write occurred (not just a move)
  -- 2. The write is at head_pos
  -- 3. Since head_pos ≤ 0, |head_pos| = -head_pos
  -- 4. The encoding change is ±2^(-head_pos)

/-- The k value is bounded by the step number -/
lemma sequence_k_bound (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ)
    (h_init : init_cfg.tape.head_pos = 0) :
    ∀ k : ℕ, (sequence_difference (sequence M init_cfg) t = 2^k ∨
               sequence_difference (sequence M init_cfg) t = -(2^k : ℤ)) →
    k ≤ t := by
  intro k hk
  -- Use sequence_k_equals_position to relate k to head position
  -- Then use head_pos_bound to show |head_pos| ≤ t
  sorry -- TODO: Complete proof
  -- Key steps:
  -- 1. By sequence_k_equals_position, k = |head_pos| at step t
  -- 2. By head_pos_bound with h_init, -t ≤ head_pos ≤ 0
  -- 3. Therefore |head_pos| ≤ t
  -- 4. So k ≤ t

/-- Movement constraint between k values -/
lemma sequence_k_movement_constraint (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (i j : ℕ)
    (h_order : i < j)
    (h_i_change : sequence M init_cfg (i + 1) ≠ sequence M init_cfg i)
    (h_j_change : sequence M init_cfg (j + 1) ≠ sequence M init_cfg j) :
    ∃ k_i k_j : ℕ,
      (sequence_difference (sequence M init_cfg) i = 2^k_i ∨
       sequence_difference (sequence M init_cfg) i = -(2^k_i : ℤ)) ∧
      (sequence_difference (sequence M init_cfg) j = 2^k_j ∨
       sequence_difference (sequence M init_cfg) j = -(2^k_j : ℤ)) ∧
      (k_j : ℤ) - k_i ≤ j - i ∧ k_i - k_j ≤ j - i := by
  -- Get k_i and k_j from sequence_k_equals_position
  -- Show that |k_j - k_i| ≤ j - i using head movement bounds
  sorry -- TODO: Complete proof
  -- Key steps:
  -- 1. Use sequence_k_equals_position for both i and j
  -- 2. k_i = |head_pos at step i|, k_j = |head_pos at step j|
  -- 3. Head can move at most 1 position per step
  -- 4. So |head_pos_j - head_pos_i| ≤ j - i
  -- 5. This implies ||head_pos_j| - |head_pos_i|| ≤ j - i
  -- 6. Therefore |k_j - k_i| ≤ j - i

/-- Main theorem: Every TM-generated sequence is a binary step sequence -/
theorem tm_sequence_is_binary_step_sequence (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ)
    (h_init_empty : init_cfg = init [])
    (h_init_pos : init_cfg.tape.head_pos = 0) :
    is_binary_step_sequence (sequence M init_cfg) := by
  constructor
  · -- Condition 1: s_0 = 0
    simp only [sequence, sequence_zero]
    rw [h_init_empty]
    simp only [init, encode_config]
    exact encode_empty_tape
  constructor
  · -- Condition 2: differences are 0 or ±2^k
    exact sequence_diff_is_power_of_two M init_cfg
  · -- Condition 3: movement constraints
    intro t ht
    simp only [change_indices, Set.mem_setOf] at ht
    constructor
    · -- 3(a): k_t ≤ t
      obtain ⟨k, hk_def, hk_eq⟩ := sequence_k_equals_position M init_cfg t ht
      use k
      refine ⟨hk_def, ?_⟩
      rw [hk_eq]
      -- k = |head_pos| and head_pos ≥ -t, so k ≤ t
      have h_bound := head_pos_bound M init_cfg t
      rw [h_init_pos] at h_bound
      -- h_bound: (steps M t init_cfg).tape.head_pos ≥ -t
      -- So |head_pos| ≤ t
      have h_pos := (steps M t init_cfg).tape.head_nonpos
      -- head_pos ≤ 0 and head_pos ≥ -t, so -t ≤ head_pos ≤ 0
      -- Therefore |head_pos| = -head_pos ≤ t
      have : -(steps M t init_cfg).tape.head_pos ≤ t := by linarith
      -- Since head_pos ≤ 0, we have -head_pos ≥ 0
      have h_nonneg : 0 ≤ -(steps M t init_cfg).tape.head_pos := by linarith
      -- We need to show natAbs(-head_pos) ≤ t
      -- Since -head_pos ≥ 0, natAbs(-head_pos) = -head_pos as a natural number
      -- We have -head_pos ≤ t as integers, and both are non-negative
      -- So we can use omega to conclude
      omega
    · -- 3(b): movement constraint between indices
      intro i hi h_lt
      simp only [change_indices, Set.mem_setOf] at hi
      exact sequence_k_movement_constraint M init_cfg i t h_lt hi ht

-- Growth Bounds for Binary Step Sequences

/-- Main growth bound theorem: Any binary step sequence s satisfies s_t < 2^(t+1) -/
theorem binary_step_sequence_growth_bound (s : ℕ → ℕ) (h : is_binary_step_sequence s) :
    ∀ t : ℕ, s t < 2^(t + 1) := by
  intro t
  -- Proof by induction on t
  induction t with
  | zero =>
    -- Base case: s 0 < 2^1 = 2
    rw [h.1]  -- s 0 = 0
    norm_num
  | succ t ih =>
    -- Inductive step: assume s t < 2^(t+1), prove s (t+1) < 2^(t+2)
    -- s(t+1) = s(t) + difference
    -- The difference is 0 or ±2^k with k ≤ t
    -- So s(t+1) ≤ s(t) + 2^t < 2^(t+1) + 2^t = 2^(t+2)
    sorry -- TODO: Complete the detailed calculation
    -- Key steps:
    -- 1. s(t+1) = s(t) + sequence_difference s t
    -- 2. By h.2.1, the difference is 0 or ±2^k
    -- 3. If in change_indices, use h.2.2 to get k ≤ t
    -- 4. So |difference| ≤ 2^t
    -- 5. Therefore s(t+1) ≤ s(t) + 2^t < 2^(t+1) + 2^t = 2^(t+2)

/-- Corollary: TM-generated sequences have the growth bound -/
theorem tm_sequence_growth_bound (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ)
    (h_init_empty : init_cfg = init [])
    (h_init_pos : init_cfg.tape.head_pos = 0) :
    ∀ t : ℕ, sequence M init_cfg t < 2^(t + 1) := by
  have h_bss := tm_sequence_is_binary_step_sequence M init_cfg h_init_empty h_init_pos
  exact binary_step_sequence_growth_bound _ h_bss

-- Finite Sequence Generation Theorem

/-- States for the universal finite sequence generator -/
inductive SeqGenState (n : ℕ)
  | state : Fin n → SeqGenState n
  | halt : SeqGenState n

instance {n : ℕ} : Inhabited (SeqGenState n) := ⟨SeqGenState.halt⟩

/-- Construct a Turing machine that generates a given finite binary step sequence -/
noncomputable def construct_tm_for_sequence (s : List ℕ)
    (h : is_finite_binary_step_sequence s) : Machine Bool (SeqGenState s.length) :=
  sorry  -- Complex construction

/-- Main theorem: Every finite binary step sequence is TM-generable -/
theorem finite_binary_step_sequence_generable (s : List ℕ)
    (h : is_finite_binary_step_sequence s) :
    ∃ (M : Machine Bool (SeqGenState s.length)) (init_cfg : Cfg Bool (SeqGenState s.length)),
      init_cfg = init [] ∧
      init_cfg.tape.head_pos = 0 ∧
      ∀ i hi, sequence M init_cfg i = s.get ⟨i, hi⟩ := by
  sorry  -- Proof uses construct_tm_for_sequence and shows correctness

end LeftTM0
