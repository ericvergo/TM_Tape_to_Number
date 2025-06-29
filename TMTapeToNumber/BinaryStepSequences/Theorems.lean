import TMTapeToNumber.BinaryStepSequences.Basic
import TMTapeToNumber.LeftwardSequences.Theorems
import Mathlib.Data.Nat.Log

namespace LeftTM0

open LeftTM0.Theorems

variable {Λ : Type*} [Inhabited Λ]

-- Helper lemma for Tape extensionality
lemma Turing.Tape.ext' {Γ : Type*} [Inhabited Γ] (T₁ T₂ : Turing.Tape Γ) 
    (h : ∀ i, T₁.nth i = T₂.nth i) : T₁ = T₂ := by
  cases' T₁ with head₁ left₁ right₁
  cases' T₂ with head₂ left₂ right₂
  simp at h ⊢
  constructor
  · -- heads are equal
    have := h 0
    simp [Turing.Tape.nth] at this
    exact this
  constructor  
  · -- lefts are equal
    apply Turing.ListBlank.ext
    intro n
    have := h (-(n + 1 : ℕ))
    -- When i = -(n+1), T.nth i = T.left.nth n
    -- So this gives us T₁.left.nth n = T₂.left.nth n
    convert this
    · simp [Turing.Tape.nth]
    · simp [Turing.Tape.nth]
  · -- rights are equal
    apply Turing.ListBlank.ext
    intro n
    have := h (n + 1 : ℕ)
    simp [Turing.Tape.nth] at this
    exact this

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
        apply Turing.Tape.ext'
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
      sorry -- TODO: Show encoding difference when removing a true bit
  · -- Current value is false
    by_cases h_new : a = true
    · -- Writing true over false: adds 2^k
      right
      use Int.natAbs (-cfg.tape.head_pos)
      left
      -- The encoding increases by 2^|head_pos|
      sorry -- TODO: Show encoding difference when adding a true bit
    · -- Writing false over false: no change
      left
      -- Show encoding doesn't change
      -- Show the encoding difference is 0
      simp only [h_cfg']
      have h_read : cfg.tape.tape.nth 0 = current_val := rfl
      -- h_current says current_val ≠ true, so current_val = false (for Bool)
      -- h_new says a ≠ true, so a = false
      have h_current_false : current_val = false := by
        cases current_val with
        | false => rfl
        | true => contradiction
      have h_a_false : a = false := by
        cases a with
        | false => rfl
        | true => contradiction
      rw [h_current_false] at h_read
      -- h_read : cfg.tape.tape.nth 0 = false
      -- We're writing a = false (from h_a_false)
      -- So the tape doesn't change
      have h_write_eq : cfg.tape.tape.write a = cfg.tape.tape := by
        rw [h_a_false]  -- Now we need to show cfg.tape.tape.write false = cfg.tape.tape
        apply Turing.Tape.ext'
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