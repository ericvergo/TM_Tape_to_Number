import TMTapeToNumber.LeftwardEncoding.Basic
import TMTapeToNumber.LeftwardEncoding.Properties

namespace LeftTM0

open LeftTM0.Theorems

variable {Λ : Type*} [Inhabited Λ]

/-- Generate sequence by running machine and encoding each step -/
noncomputable def sequence (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) : ℕ → ℕ :=
  fun n ↦ encode_config (steps M n init_cfg)

/-- Generate sequence with bounded execution (halt after max_steps) -/
noncomputable def sequence_bounded (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ)
    (max_steps : ℕ) : ℕ → ℕ :=
  fun n ↦
    if n ≤ max_steps then
      encode_config (steps M n init_cfg)
    else
      encode_config (steps_until_halt M max_steps init_cfg)

/-- Get the value at step 0 (initial configuration) -/
noncomputable def sequence_initial (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) : ℕ :=
  sequence M init_cfg 0

/-- Check if sequence reaches a fixed point (machine halts) -/
def sequence_stabilizes (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (n : ℕ) : Prop :=
  ∀ m ≥ n, sequence M init_cfg m = sequence M init_cfg n

/-- Find first step where sequence stabilizes, if any -/
noncomputable def first_stable_step (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (max_search : ℕ) : Option ℕ :=
  let rec search (k : ℕ) : Option ℕ :=
    if k ≥ max_search then none
    else if sequence M init_cfg k = sequence M init_cfg (k + 1) then some k
    else search (k + 1)
  search 0

-- Properties of sequences
theorem sequence_zero (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) :
    sequence M init_cfg 0 = encode_config init_cfg := rfl

theorem sequence_step_relation (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (n : ℕ) :
    sequence M init_cfg (n + 1) = encode_config (step_or_stay M (steps M n init_cfg)) := by
  unfold sequence steps
  simp [Function.iterate_succ_apply']

-- Helper lemma for steps
theorem steps_succ (M : Machine Bool Λ) (n : ℕ) (init_cfg : Cfg Bool Λ) :
    steps M (n + 1) init_cfg = step_or_stay M (steps M n init_cfg) := by
  unfold steps
  simp [Function.iterate_succ_apply']

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
    if abs_d > 0 ∧ (abs_d.land (abs_d - 1) = 0) then
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

/-- If a difference is ±2^k, then extract_k_value returns k -/
theorem extract_k_value_pow (k : ℕ) :
    extract_k_value (2^k : ℤ) = some k ∧ extract_k_value (-(2^k : ℤ)) = some k := by
  sorry

/-- A sequence value at time 0 is 0 for binary step sequences -/
theorem binary_step_sequence_zero (s : ℕ → ℕ) (h : is_binary_step_sequence s) :
    s 0 = 0 := h.1

/-- Helper to check if a natural number is a power of 2 -/
def is_power_of_two (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 2^k

/-- The absolute value of a binary step sequence difference is 0 or a power of 2 -/
theorem binary_step_diff_power_of_two (s : ℕ → ℕ) (h : is_binary_step_sequence s) (t : ℕ) :
    sequence_difference s t = 0 ∨ is_power_of_two (Int.natAbs (sequence_difference s t)) := by
  sorry

end LeftTM0
