import TMTapeToNumber.BinaryStepSequences.Basic
import TMTapeToNumber.LeftwardSequences.Theorems
import Mathlib.Data.Nat.Log

namespace LeftTM0

open LeftTM0.Theorems

variable {Λ : Type*} [Inhabited Λ]

-- Forward Characterization: TM sequences are binary step sequences

/-- The difference in encoding when writing at a position is ±2^k where k is the absolute position -/
lemma encode_diff_at_write (cfg : Cfg Bool Λ) (cfg' : Cfg Bool Λ) 
    (h_step : ∃ a, cfg' = ⟨cfg.q, cfg.tape.write a⟩) :
    encode_config cfg' - encode_config cfg = 0 ∨
    ∃ k : ℕ, (encode_config cfg' : ℤ) - encode_config cfg = 2^k ∨ 
             (encode_config cfg' : ℤ) - encode_config cfg = -(2^k : ℤ) := by
  sorry

/-- One step of a TM changes the encoding by 0 or ±2^k -/
lemma sequence_diff_is_power_of_two (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ) :
    sequence_difference (sequence M init_cfg) t = 0 ∨
    ∃ k : ℕ, sequence_difference (sequence M init_cfg) t = 2^k ∨ 
             sequence_difference (sequence M init_cfg) t = -(2^k : ℤ) := by
  sorry

/-- The k value in a sequence change equals the absolute position where the write occurred -/
lemma sequence_k_equals_position (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ)
    (h_change : sequence M init_cfg (t + 1) ≠ sequence M init_cfg t) :
    ∃ k : ℕ, (sequence_difference (sequence M init_cfg) t = 2^k ∨ 
              sequence_difference (sequence M init_cfg) t = -(2^k : ℤ)) ∧
              k = Int.natAbs (-(steps M t init_cfg).tape.head_pos) := by
  sorry

/-- The k value is bounded by the step number -/
lemma sequence_k_bound (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ)
    (h_init : init_cfg.tape.head_pos = 0) :
    ∀ k : ℕ, (sequence_difference (sequence M init_cfg) t = 2^k ∨ 
               sequence_difference (sequence M init_cfg) t = -(2^k : ℤ)) →
    k ≤ t := by
  sorry

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
  sorry

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
  sorry  -- Proof is complex, leaving as sorry for now

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