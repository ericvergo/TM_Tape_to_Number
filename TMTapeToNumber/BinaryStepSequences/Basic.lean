import TMTapeToNumber.LeftwardSequences.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Int.Bitwise
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Bitwise

namespace LeftTM0

-- Binary Step Sequences definitions from the paper

/-- Compute the difference between consecutive sequence values -/
def sequence_difference (s : ℕ → ℕ) (t : ℕ) : ℤ :=
  (s (t + 1) : ℤ) - (s t : ℤ)

/-- Extract k value from a difference of the form ±2^k -/
def extract_k_value (d : ℤ) : Option ℕ :=
  if d = 0 then none
  else
    let abs_d := Int.natAbs d
    -- Check if abs_d is a power of 2
    if abs_d > 0 ∧ (abs_d &&& (abs_d - 1) = 0) then
      some (abs_d.log2)
    else none

/-- The set of indices where the sequence changes -/
def change_indices (s : ℕ → ℕ) : Set ℕ :=
  {t : ℕ | s (t + 1) ≠ s t}

/-- A sequence is a binary step sequence if it satisfies the constraints from the paper -/
def is_binary_step_sequence (s : ℕ → ℕ) : Prop :=
  -- Condition 1: s_0 = 0
  s 0 = 0 ∧
  -- Condition 2: For each step t, the difference is 0 or ±2^k
  (∀ t : ℕ, sequence_difference s t = 0 ∨
    ∃ k : ℕ, sequence_difference s t = 2^k ∨ sequence_difference s t = -(2^k : ℤ)) ∧
  -- Condition 3: Movement constraints on k values
  (∀ t ∈ change_indices s,
    -- 3(a): k_t ≤ t (head can reach at most position t after t steps)
    (∃ k : ℕ, (sequence_difference s t = 2^k ∨ sequence_difference s t = -(2^k : ℤ)) ∧ k ≤ t) ∧
    -- 3(b): For any two change indices i < j, |k_j - k_i| ≤ j - i
    (∀ i ∈ change_indices s, i < t →
      ∃ k_i k_t : ℕ,
        (sequence_difference s i = 2^k_i ∨ sequence_difference s i = -(2^k_i : ℤ)) ∧
        (sequence_difference s t = 2^k_t ∨ sequence_difference s t = -(2^k_t : ℤ)) ∧
        (k_t : ℤ) - k_i ≤ t - i ∧ k_i - k_t ≤ t - i))

/-- Finite version of binary step sequence for constructive proofs -/
def is_finite_binary_step_sequence (s : List ℕ) : Prop :=
  -- Convert list to function for easier manipulation
  let sf : ℕ → ℕ := fun i => if h : i < s.length then s.get ⟨i, h⟩ else 0
  -- Condition 1: s_0 = 0
  s.head? = some 0 ∧
  -- Conditions 2 and 3 adapted for finite sequence
  (∀ t < s.length - 1, sequence_difference sf t = 0 ∨
    ∃ k : ℕ, sequence_difference sf t = 2^k ∨ sequence_difference sf t = -(2^k : ℤ)) ∧
  -- Movement constraints
  (∀ t < s.length - 1, sf (t + 1) ≠ sf t →
    (∃ k : ℕ, (sequence_difference sf t = 2^k ∨ sequence_difference sf t = -(2^k : ℤ)) ∧ k ≤ t) ∧
    (∀ i < t, sf (i + 1) ≠ sf i →
      ∃ k_i k_t : ℕ,
        (sequence_difference sf i = 2^k_i ∨ sequence_difference sf i = -(2^k_i : ℤ)) ∧
        (sequence_difference sf t = 2^k_t ∨ sequence_difference sf t = -(2^k_t : ℤ)) ∧
        (k_t : ℤ) - k_i ≤ t - i ∧ k_i - k_t ≤ t - i))

-- Path construction helpers for finite sequence generation

/-- Extract the k value at each change index from a sequence -/
noncomputable def extract_k_sequence (s : List ℕ) : List (Option ℕ) :=
  let sf : ℕ → ℕ := fun i => if h : i < s.length then s.get ⟨i, h⟩ else 0
  List.range (s.length - 1) |>.map fun t =>
    if t + 1 < s.length ∧ sf (t + 1) ≠ sf t then
      extract_k_value (sequence_difference sf t)
    else none

/-- A valid head path for a Turing machine -/
def is_valid_head_path (path : List ℤ) : Prop :=
  path.head? = some 0 ∧
  ∀ i hi hi',
    let curr := path.get ⟨i, hi⟩
    let next := path.get ⟨i + 1, hi'⟩
    (next = curr - 1 ∨ next = curr ∨ next = curr + 1) ∧
    curr ≤ 0 ∧ next ≤ 0

/-- Construct a head path from k values and change indices -/
noncomputable def construct_head_path_segment (start_pos end_pos : ℤ) (steps : ℕ) : List ℤ :=
  -- Move from start_pos to end_pos in exactly 'steps' steps
  if steps = 0 then []
  else if start_pos = end_pos then
    List.replicate steps start_pos
  else
    let distance := end_pos - start_pos
    let abs_dist := Int.natAbs distance
    if abs_dist > steps then
      [] -- Invalid: can't reach end_pos in time
    else
      let move_steps := abs_dist
      let wait_steps := steps - move_steps
      let moves := if distance < 0 then
        List.replicate move_steps (-1 : ℤ)
      else
        List.replicate move_steps (1 : ℤ)
      let waits := List.replicate wait_steps (0 : ℤ)
      -- Apply moves to start_pos
      let path_during_moves := moves.scanl (· + ·) start_pos |>.tail
      let final_pos := if h : path_during_moves = [] then start_pos
                      else path_during_moves.getLast (by simp [h])
      path_during_moves ++ List.replicate wait_steps final_pos

-- Helper lemmas for binary step sequences

-- We'll remove these helper lemmas and try a different approach

/-- Key property: 2^k AND (2^k - 1) = 0 -/
lemma pow_two_land_pred (k : ℕ) : (2^k) &&& (2^k - 1) = 0 := by
  -- The key insight: 2^k in binary is 1 followed by k zeros
  -- 2^k - 1 in binary is k ones
  -- Their AND is 0 because they have no bits in common
  cases k with
  | zero =>
    -- Base case: 2^0 = 1, so 1 &&& 0 = 0
    rfl
  | succ k' =>
    -- We'll prove this by induction and direct computation
    -- First, let's establish that 2^(k'+1) - 1 < 2^(k'+1)
    have h_lt : 2^(k' + 1) - 1 < 2^(k' + 1) := by
      apply Nat.sub_lt
      · exact Nat.pow_pos (Nat.zero_lt_two)
      · exact Nat.one_pos
    -- Now we use a key fact: for powers of 2, the AND with predecessor is 0
    -- This follows from the binary representation:
    -- 2^n = 1000...0 (one followed by n zeros)
    -- 2^n - 1 = 0111...1 (n ones)
    -- Their AND is 0 since no bit positions overlap
    sorry  -- TODO: complete using bit properties or direct calculation

/-- If a difference is ±2^k, then extract_k_value returns k -/
theorem extract_k_value_pow (k : ℕ) :
    extract_k_value (2^k : ℤ) = some k ∧ extract_k_value (-(2^k : ℤ)) = some k := by
  -- The proof shows that extract_k_value correctly identifies k from ±2^k
  constructor
  · -- Case: extract_k_value (2^k) = some k
    unfold extract_k_value
    simp only [Int.natCast_pow]
    -- 2^k ≠ 0
    have h_ne_zero : (2^k : ℤ) ≠ 0 := by
      simp [pow_ne_zero]
    rw [if_neg h_ne_zero]
    -- Int.natAbs (2^k) = 2^k since 2^k is positive
    have h_natAbs : Int.natAbs (2^k : ℤ) = 2^k := by
      simp [Int.natAbs_of_nonneg, pow_nonneg]
    simp only [h_natAbs]
    -- Need to show: 2^k > 0 ∧ (2^k).land (2^k - 1) = 0
    have h_pos : 2^k > 0 := pow_pos (by norm_num) k
    have h_land : (2^k).land (2^k - 1) = 0 := pow_two_land_pred k
    rw [if_pos ⟨h_pos, h_land⟩]
    -- Finally, show that log2(2^k) = k
    -- We have abs_d.log2 = Nat.log 2 (2^k) = k
    rw [Nat.log2_eq_log_two]
    congr
    exact Nat.log_pow (by norm_num : 1 < 2) k
  · -- Case: extract_k_value (-(2^k)) = some k
    unfold extract_k_value
    -- -(2^k) ≠ 0
    have h_ne_zero : -(2^k : ℤ) ≠ 0 := by
      simp [pow_ne_zero]
    rw [if_neg h_ne_zero]
    -- Int.natAbs (-(2^k)) = 2^k
    have h_natAbs : Int.natAbs (-(2^k : ℤ)) = 2^k := by
      simp [Int.natAbs_neg, Int.natAbs_of_nonneg, pow_nonneg]
    simp only [h_natAbs]
    -- The rest is the same as the positive case
    have h_pos : 2^k > 0 := pow_pos (by norm_num) k
    have h_land : (2^k).land (2^k - 1) = 0 := pow_two_land_pred k
    rw [if_pos ⟨h_pos, h_land⟩]
    -- Finally, show that log2(2^k) = k
    -- We have abs_d.log2 = Nat.log 2 (2^k) = k
    rw [Nat.log2_eq_log_two]
    congr
    exact Nat.log_pow (by norm_num : 1 < 2) k

/-- A sequence value at time 0 is 0 for binary step sequences -/
theorem binary_step_sequence_zero (s : ℕ → ℕ) (h : is_binary_step_sequence s) :
    s 0 = 0 := h.1

/-- Helper to check if a natural number is a power of 2 -/
def is_power_of_two (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 2^k

/-- The absolute value of a binary step sequence difference is 0 or a power of 2 -/
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
    cases h_k with
    | inl h_pos =>
      -- sequence_difference s t = 2^k
      use k
      rw [h_pos]
      simp [Int.natAbs_of_nonneg]
    | inr h_neg =>
      -- sequence_difference s t = -(2^k)
      use k
      rw [h_neg]
      simp [Int.natAbs_neg]

end LeftTM0
