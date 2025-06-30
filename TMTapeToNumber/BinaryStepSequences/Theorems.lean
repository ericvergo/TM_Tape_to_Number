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
  -- The proof establishes that s_t < 2^(t+1) by induction
  induction t with
  | zero =>
    -- Base case: s_0 = 0 < 2^1 = 2
    have h_zero := h.1  -- First component: s 0 = 0
    rw [h_zero]
    norm_num
  | succ t ih =>
    -- Inductive step: if s_t < 2^(t+1), then s_(t+1) < 2^(t+2)
    have h_diff := h.2.1 t  -- Second component, first part: diffs condition
    cases h_diff with
    | inl h_zero =>
      -- Case: difference is 0, so s(t+1) = s(t)
      have : s (t + 1) = s t := by
        unfold sequence_difference at h_zero
        have : (s (t + 1) : ℤ) = s t := by linarith
        exact Nat.cast_injective this
      rw [this]
      -- s t < 2^(t+1) < 2^(t+2)
      calc
        s t < 2^(t + 1) := ih
        _ < 2^(t + 2) := by
          have : 2^(t + 1) < 2^(t + 2) := by
            apply Nat.pow_lt_pow_right
            · norm_num  -- 1 < 2
            · omega     -- t + 1 < t + 2
          exact this
    | inr h_exists =>
      obtain ⟨k, hk⟩ := h_exists
      -- The sequence changed by ±2^k at step t
      -- We need to show s (t + 1) < 2^(t + 2)

      -- From h_bss.2, we know k ≤ t
      have h_k_bound : k ≤ t := by
        -- Extract from the binary step sequence property
        have h_ne : s (t + 1) ≠ s t := by
          -- We know the sequence changed at step t
          intro h_eq
          -- If s (t + 1) = s t, then sequence_difference = 0
          have : sequence_difference s t = 0 := by
            unfold sequence_difference
            simp [h_eq]
          -- But hk says sequence_difference = ±2^k ≠ 0
          cases hk with
          | inl h_pos =>
            -- h_pos : sequence_difference s t = 2^k
            -- this : sequence_difference s t = 0
            rw [this] at h_pos
            -- h_pos : 0 = 2^k
            have : 0 < 2^k := by apply Nat.pow_pos; norm_num
            linarith
          | inr h_neg =>
            -- h_neg : sequence_difference s t = -(2^k)
            -- this : sequence_difference s t = 0
            rw [this] at h_neg
            -- h_neg : 0 = -(2^k)
            have : (0 : ℤ) < 2^k := by simp
            linarith

        have h_I : t ∈ {i | 0 ≤ i ∧ i < t + 1 ∧ s (i + 1) ≠ s i} := by
          simp only [Set.mem_setOf]
          exact And.intro (by omega) (And.intro (by omega) h_ne)

        -- The definition of binary step sequence says:
        -- For all t in change_indices, there exists k with the right properties
        have h_t_change : t ∈ change_indices s := by
          unfold change_indices
          simp [Set.mem_setOf]
          exact h_ne

        -- Apply the first part of property h.2.2
        have h_constraint := h.2.2 t h_t_change
        have ⟨k', h_k'_pow, h_k'_bound⟩ := h_constraint.1

        -- k' must equal k by uniqueness of powers of 2
        have h_k_eq : k' = k := by
          cases h_k'_pow with
          | inl h_pos' =>
            cases hk with
            | inl h_pos =>
              -- Both are positive powers
              have : (2^k' : ℤ) = 2^k := by rw [← h_pos', h_pos]
              have h_eq_nat : 2^k' = 2^k := by
                have h_cast1 : (2^k' : ℤ) = ((2^k' : ℕ) : ℤ) := by norm_cast
                have h_cast2 : (2^k : ℤ) = ((2^k : ℕ) : ℤ) := by norm_cast
                rw [h_cast1, h_cast2] at this
                exact Nat.cast_injective this
              exact Nat.pow_right_injective (by omega : 1 < 2) h_eq_nat
            | inr h_neg =>
              -- One positive, one negative - impossible
              have : (2^k' : ℤ) = -(2^k : ℤ) := by rw [← h_pos', h_neg]
              have : (2^k' : ℤ) + (2^k : ℤ) = 0 := by linarith
              have h_pos1 : (0 : ℤ) < 2^k' := by simp
              have h_pos2 : (0 : ℤ) < 2^k := by simp
              linarith
          | inr h_neg' =>
            cases hk with
            | inl h_pos =>
              -- One negative, one positive - impossible
              have : -(2^k' : ℤ) = (2^k : ℤ) := by rw [← h_neg', h_pos]
              have : (2^k' : ℤ) + (2^k : ℤ) = 0 := by linarith
              have h_pos1 : (0 : ℤ) < 2^k' := by simp
              have h_pos2 : (0 : ℤ) < 2^k := by simp
              linarith
            | inr h_neg =>
              -- Both are negative powers
              have : -(2^k' : ℤ) = -(2^k : ℤ) := by rw [← h_neg', h_neg]
              have : (2^k' : ℤ) = 2^k := by linarith
              have h_eq_nat : 2^k' = 2^k := by
                have h_cast1 : (2^k' : ℤ) = ((2^k' : ℕ) : ℤ) := by norm_cast
                have h_cast2 : (2^k : ℤ) = ((2^k : ℕ) : ℤ) := by norm_cast
                rw [h_cast1, h_cast2] at this
                exact Nat.cast_injective this
              exact Nat.pow_right_injective (by omega : 1 < 2) h_eq_nat

        rw [← h_k_eq]
        exact h_k'_bound

      -- Now consider two cases based on the sign of the change
      cases hk with
      | inl h_increase =>
        -- s (t + 1) = s t + 2^k
        have h_eq : s (t + 1) = s t + 2^k := by
          unfold sequence_difference at h_increase
          have h1 : (s (t + 1) : ℤ) - s t = 2^k := h_increase
          have h2 : (s (t + 1) : ℤ) = (s t : ℤ) + (2^k : ℤ) := by linarith
          -- Key: rewrite 2^k in the integer context to (2^k : ℕ)
          have h3 : (2^k : ℤ) = ((2^k : ℕ) : ℤ) := by norm_cast
          rw [h3] at h2
          -- Now h2 : (s (t + 1) : ℤ) = (s t : ℤ) + ((2^k : ℕ) : ℤ)
          have h4 : (s (t + 1) : ℤ) = ((s t + 2^k : ℕ) : ℤ) := by
            conv_rhs => rw [Nat.cast_add]
            exact h2
          -- Apply injectivity
          simp only [Nat.cast_injective.eq_iff] at h4
          exact h4

        rw [h_eq]
        -- We need: s t + 2^k < 2^(t + 2)
        -- We have: s t < 2^(t + 1) (from ih)
        -- We have: k ≤ t (from h_k_bound)
        -- So: 2^k ≤ 2^t
        have h_pow_bound : 2^k ≤ 2^t := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h_k_bound

        -- Therefore: s t + 2^k < 2^(t + 1) + 2^t
        have : s t + 2^k < 2^(t + 1) + 2^t := by
          -- We know s t < 2^(t + 1) and 2^k ≤ 2^t
          -- So s t + 2^k ≤ s t + 2^t < 2^(t + 1) + 2^t
          calc s t + 2^k ≤ s t + 2^t := Nat.add_le_add_left h_pow_bound _
               _ < 2^(t + 1) + 2^t := Nat.add_lt_add_right ih _

        -- And 2^(t + 1) + 2^t < 2^(t + 2)
        have h_sum_bound : 2^(t + 1) + 2^t < 2^(t + 2) := by
          -- 2^(t + 1) = 2 * 2^t
          -- So 2^(t + 1) + 2^t = 2 * 2^t + 2^t = 3 * 2^t
          -- And 2^(t + 2) = 2^2 * 2^t = 4 * 2^t
          -- So we need to show 3 * 2^t < 4 * 2^t
          have h1 : 2^(t + 1) = 2 * 2^t := by rw [pow_succ, mul_comm]
          have h2 : 2^(t + 2) = 4 * 2^t := by
            -- 2^(t + 2) = 2^(t + 1 + 1) = 2^(t+1) * 2 = 2 * 2^t * 2 = 4 * 2^t
            calc 2^(t + 2) = 2^(t + 1) * 2 := by rw [pow_succ]
            _ = (2 * 2^t) * 2 := by rw [h1]
            _ = 2 * 2^t * 2 := rfl
            _ = 2 * 2 * 2^t := by ring
            _ = 4 * 2^t := by norm_num
          rw [h1, h2]
          -- Now show 2 * 2^t + 2^t < 4 * 2^t
          -- This is 3 * 2^t < 4 * 2^t
          have : 2 * 2^t + 2^t = 3 * 2^t := by ring
          rw [this]
          -- 3 * 2^t < 4 * 2^t because 3 < 4 and 2^t > 0
          apply Nat.mul_lt_mul_of_pos_right
          · norm_num
          · apply Nat.pow_pos; norm_num

        exact Nat.lt_trans this h_sum_bound

      | inr h_decrease =>
        -- s (t + 1) = s t - 2^k
        have h_eq : (s (t + 1) : ℤ) = (s t : ℤ) - (2^k : ℤ) := by
          unfold sequence_difference at h_decrease
          have : (s (t + 1) : ℤ) - s t = -(2^k : ℤ) := h_decrease
          linarith

        -- Since s t < 2^(t + 1) and we're subtracting, we get
        -- s (t + 1) < s t < 2^(t + 1) < 2^(t + 2)

        -- First, we need to show that the subtraction is valid
        -- i.e., that 2^k ≤ s t
        have h_valid_sub : 2^k ≤ s t := by
          -- If 2^k > s t, then s t - 2^k would be negative
          -- But s (t + 1) is a natural number
          by_contra h_not
          push_neg at h_not
          -- So s t < 2^k
          -- Then in integers: s (t + 1) = s t - 2^k < 0
          have h1 : (s t : ℤ) < (2^k : ℤ) := by
            norm_cast
          have h2 : (s (t + 1) : ℤ) < 0 := by
            calc
              (s (t + 1) : ℤ) = (s t : ℤ) - 2^k := h_eq
              _ < (2^k : ℤ) - 2^k := by linarith
              _ = 0 := by ring
          -- But s (t + 1) ≥ 0, contradiction
          have h3 : (0 : ℤ) ≤ s (t + 1) := by simp
          linarith

        -- Now we can compute s (t + 1) in naturals
        have h_sub : s (t + 1) = s t - 2^k := by
          -- From h_eq: (s (t + 1) : ℤ) = (s t : ℤ) - (2^k : ℤ)
          -- And h_valid_sub: 2^k ≤ s t
          -- So we can convert to natural subtraction
          have h_cast : ((s t - 2^k : ℕ) : ℤ) = (s t : ℤ) - (2^k : ℤ) := by
            norm_cast
          have : (s (t + 1) : ℤ) = ((s t - 2^k : ℕ) : ℤ) := by
            rw [h_cast]
            exact h_eq
          exact Nat.cast_injective this

        -- Therefore s (t + 1) < s t
        rw [h_sub]
        have : s t - 2^k < s t := by
          apply Nat.sub_lt
          · -- s t > 0 because if s t = 0, then 2^k ≤ 0, which is impossible
            by_contra h_zero
            push_neg at h_zero
            have : s t = 0 := by omega
            rw [this] at h_valid_sub
            simp at h_valid_sub
          · exact Nat.pow_pos (by norm_num : 0 < 2)

        -- So s (t + 1) < s t < 2^(t + 1) < 2^(t + 2)
        exact Nat.lt_trans this (Nat.lt_trans ih (Nat.pow_lt_pow_right (by norm_num) (by omega)))



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
