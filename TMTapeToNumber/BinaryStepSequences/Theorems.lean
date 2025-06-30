import TMTapeToNumber.BinaryStepSequences.Basic
import TMTapeToNumber.BinaryStepSequences.Lemmas
import TMTapeToNumber.LeftwardSequences.Theorems
import TMTapeToNumber.LeftTM0.LeftwardTape
import TMTapeToNumber.LeftTM0.Step
import TMTapeToNumber.LeftwardEncoding.Properties
import Mathlib.Data.Nat.Log

set_option linter.unusedSectionVars false

namespace LeftTM0

open LeftTM0.Theorems
open Turing

variable {Λ : Type*} [Inhabited Λ]

open LeftwardTape

-- Main Theorems: TM sequences are binary step sequences

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
  -- The proof would establish that s_t < 2^(t+1) by induction
  -- Base case: s_0 = 0 < 2^1 = 2
  -- Inductive step: if s_t < 2^(t+1) and the difference at t is 0 or ±2^k with k ≤ t,
  -- then s_(t+1) ≤ s_t + 2^t < 2^(t+1) + 2^t < 2^(t+2)
  sorry


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