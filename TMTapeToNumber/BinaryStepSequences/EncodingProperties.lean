/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean FRO Team
-/
import TMTapeToNumber.BinaryStepSequences.EncodingDifference

/-!
# Properties of Encoding Operations

This file contains lemmas about properties of encoding operations,
including when the encoding difference is zero and relationships
between natural and integer subtraction.
-/

set_option linter.unusedSectionVars false

namespace LeftTM0

namespace BinaryStepSequences

variable {Λ : Type*} [Inhabited Λ]

open Turing LeftTM0 LeftwardTape

/-- The witness k value when writing changes the encoding.
    This is the absolute value of the head position, which determines
    the power of 2 by which the encoding changes. -/
def write_witness (cfg : Cfg Bool Λ) : ℕ :=
  Int.natAbs (-cfg.tape.head_pos)

/-- When encode_diff returns zero, we're writing the same value -/
lemma encode_diff_zero_implies_same (cfg : Cfg Bool Λ) (a : Bool)
    (h_diff : encode_diff cfg ⟨cfg.q, cfg.tape.write a⟩ = 0) :
    cfg.tape.nth 0 = a := by
  -- If the encoding doesn't change after writing, then we must be writing the same value
  -- Cases on what value is currently at position 0
  by_cases h_curr : cfg.tape.nth 0 = true
  · -- Current value is true
    by_cases h_a : a = true
    · -- Writing true over true - same value
      rw [h_curr, h_a]
    · -- Writing false over true
      -- This would decrease the encoding, contradicting h_diff = 0
      exfalso
      have h_decrease : (cfg.tape.write a).encode < cfg.tape.encode := by
        have h_a_false : a = false := by
          cases a
          · rfl
          · contradiction
        rw [h_a_false]
        exact encode_decrease_write_false_over_true cfg h_curr
      -- But h_diff = 0 means the integer difference is 0
      -- Since we decreased, the integer diff should be negative, not 0
      have h_neg : encode_diff cfg ⟨cfg.q, cfg.tape.write a⟩ < 0 := by
        unfold encode_diff
        simp only [encode_config]
        have : (cfg.tape.write a).encode < cfg.tape.encode := h_decrease
        omega
      linarith
  · -- Current value is false
    push_neg at h_curr
    rw [eq_false_of_ne_true h_curr]
    by_cases h_a : a = false
    · -- Writing false over false - same value
      rw [h_a]
    · -- Writing true over false
      -- This would increase the encoding, contradicting h_diff = 0
      exfalso
      have h_increase : cfg.tape.encode < (cfg.tape.write a).encode := by
        have h_a_true : a = true := by
          cases a
          · contradiction
          · rfl
        rw [h_a_true]
        have h_false : cfg.tape.nth 0 = false := eq_false_of_ne_true h_curr
        exact encode_increase_write_true_over_false cfg h_false
      -- But h_diff = 0 means the integer difference is 0
      -- Since we increased, the integer diff should be positive, not 0
      have h_pos : encode_diff cfg ⟨cfg.q, cfg.tape.write a⟩ > 0 := by
        unfold encode_diff
        simp only [encode_config]
        have : cfg.tape.encode < (cfg.tape.write a).encode := h_increase
        omega
      linarith

/-- When natural subtraction equals zero with le, encodings are equal -/
lemma encode_nat_sub_zero_eq (cfg cfg' : Cfg Bool Λ)
    (h_le : encode_config cfg ≤ encode_config cfg')
    (h_diff : encode_config cfg' - encode_config cfg = 0) :
    encode_config cfg' = encode_config cfg := by
  -- From h_diff we get cfg' ≤ cfg
  have h_le' : encode_config cfg' ≤ encode_config cfg := Nat.sub_eq_zero_iff_le.mp h_diff
  -- Combined with h_le: cfg ≤ cfg', we get equality
  exact Nat.le_antisymm h_le' h_le

/-- Natural subtraction zero and integer difference = 0 implies equality -/
lemma nat_sub_zero_and_int_diff_zero (a b : ℕ)
    (_h_nat : a - b = 0)
    (h_int : (a : ℤ) - (b : ℤ) = 0) :
    a = b := by
  -- From the integer equality, we get a = b
  have h_eq : (a : ℤ) = (b : ℤ) := by linarith
  -- Cast injective gives us a = b
  exact Nat.cast_injective h_eq


/-- Natural diff = 0 happens only when new encoding ≤ old encoding -/
lemma encode_nat_diff_zero_cases (cfg : Cfg Bool Λ) (a : Bool)
    (h_diff : encode_config ⟨cfg.q, cfg.tape.write a⟩ - encode_config cfg = 0) :
    encode_config ⟨cfg.q, cfg.tape.write a⟩ ≤ encode_config cfg := by
  exact Nat.sub_eq_zero_iff_le.mp h_diff

/-- Simplified: The difference in encoding when writing is 0 or ±2^|head_pos| -/
lemma encode_diff_at_write_simple (cfg : Cfg Bool Λ) (a : Bool) :
    let new_cfg := ⟨cfg.q, cfg.tape.write a⟩
    let diff := encode_diff cfg new_cfg
    diff = 0 ∨
    (cfg.tape.nth 0 = false ∧ a = true ∧ diff = 2^(Int.natAbs (-cfg.tape.head_pos))) ∨
    (cfg.tape.nth 0 = true ∧ a = false ∧ diff = -(2^(Int.natAbs (-cfg.tape.head_pos)) : ℤ)) := by
  -- This follows from encode_diff_at_write by case analysis
  have h_base := encode_diff_at_write cfg a
  -- h_base tells us diff = 0 ∨ ∃ k, diff = 2^k ∨ diff = -2^k
  cases h_base with
  | inl h_zero =>
    left
    exact h_zero
  | inr h_exists =>
    obtain ⟨k, h_or⟩ := h_exists
    -- We need to show k = Int.natAbs (-cfg.tape.head_pos) and relate to tape values
    by_cases h_same : cfg.tape.nth 0 = a
    · -- If we're writing the same value, diff = 0
      left
      exact encode_same_value_zero_diff cfg a h_same
    · -- Writing different value
      right
      cases ha : a with
      | false =>
        -- Writing false, so current must be true
        right
        have h_true : cfg.tape.nth 0 = true := by
          cases h_cur : cfg.tape.nth 0
          · -- cfg.tape.nth 0 = false and a = false, but h_same says they're different
            exfalso
            rw [h_cur, ha] at h_same
            exact h_same rfl
          · rfl
        refine ⟨h_true, rfl, ?_⟩
        -- Use the fact that when writing false over true, encoding decreases by 2^|head_pos|
        have h_dec := encode_strict_decrease_write_false cfg.tape cfg.tape.head_nonpos h_true
        have h_eq : cfg.tape.encode = (cfg.tape.write false).encode + 2^(Int.natAbs (-cfg.tape.head_pos)) := by
          exact encode_eq_write_false_plus_power cfg.tape cfg.tape.head_nonpos h_true
        -- So the difference is negative
        unfold encode_diff
        simp only [encode_config]
        rw [h_eq]
        simp
      | true =>
        -- Writing true, so current must be false
        left
        have h_false : cfg.tape.nth 0 = false := by
          cases h_cur : cfg.tape.nth 0
          · rfl
          · -- cfg.tape.nth 0 = true and a = true, but h_same says they're different
            exfalso
            rw [h_cur, ha] at h_same
            exact h_same rfl
        refine ⟨h_false, rfl, ?_⟩
        -- Use the fact that when writing true over false, encoding increases by 2^|head_pos|
        have h_inc := encode_strict_increase_write_true cfg.tape cfg.tape.head_nonpos h_false
        have h_eq : (cfg.tape.write true).encode = cfg.tape.encode + 2^(Int.natAbs (-cfg.tape.head_pos)) := by
          exact encode_eq_write_true_minus_power cfg.tape cfg.tape.head_nonpos h_false
        -- So the difference is positive
        unfold encode_diff
        simp only [encode_config]
        rw [h_eq]
        simp

/-- Direct computation of encoding difference when writing at head position -/
lemma encode_write_diff_value (cfg : Cfg Bool Λ) (a : Bool) :
    let new_cfg := ⟨cfg.q, cfg.tape.write a⟩
    let diff := encode_diff cfg new_cfg
    let k := write_witness cfg
    (cfg.tape.nth 0 = a → diff = 0) ∧
    (cfg.tape.nth 0 = false ∧ a = true → diff = 2^k) ∧
    (cfg.tape.nth 0 = true ∧ a = false → diff = -(2^k : ℤ)) := by
  constructor
  · -- If writing same value, diff = 0
    intro h_same
    exact encode_same_value_zero_diff cfg a h_same
  · constructor
    · -- If current is false and writing true, diff = 2^k
      intro ⟨h_false, h_true⟩
      -- The encoding increases by 2^k
      have h_inc := encode_increase_write_true_over_false cfg h_false
      unfold encode_diff
      simp only [encode_config]
      -- We know (cfg.tape.write true).encode = cfg.tape.encode + 2^k
      -- So diff = 2^k
      -- First prove the equation with the explicit value
      have h_eq : (cfg.tape.write true).encode = cfg.tape.encode + 2^(Int.natAbs (-cfg.tape.head_pos)) := by
        -- We use the lemma encode_strict_increase_write_true directly
        have h_inc_lemma := encode_strict_increase_write_true cfg.tape cfg.tape.head_nonpos h_false
        -- The lemma shows (tape.write true).encode > tape.encode
        -- But from its proof, we know the exact equation
        -- Let me extract it from encode_increase_write_true_over_false
        have h_exact : (cfg.tape.write true).encode = cfg.tape.encode + 2^(Int.natAbs (-cfg.tape.head_pos)) := by
          -- This is the key equation from the proof of encode_strict_increase_write_true
          -- at line 391 of EncodingDifference.lean
          -- We'll use the wrapper lemma that provides easier access
          -- Actually, looking at the code, we need to reprove the equation here
          -- The proof follows the same structure as in encode_strict_increase_write_true
          unfold LeftwardTape.encode
          -- Show cfg.tape.head_pos is not in cfg.tape.true_positions_absolute
          have h_not_mem : cfg.tape.head_pos ∉ cfg.tape.true_positions_absolute := by
            unfold LeftwardTape.true_positions_absolute
            simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
                       LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
            intro ⟨_, _, h_true⟩
            simp only [sub_self, LeftwardTape.nth] at h_true
            have : cfg.tape.tape.nth 0 = false := h_false
            rw [this] at h_true
            simp at h_true
          -- After writing true, cfg.tape.head_pos is added
          have h_after : (cfg.tape.write true).true_positions_absolute =
                        cfg.tape.true_positions_absolute ∪ {cfg.tape.head_pos} := by
            ext i
            simp only [Finset.mem_union, Finset.mem_singleton]
            unfold LeftwardTape.true_positions_absolute
            simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
                       LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
            constructor
            · intro ⟨h_ne_def, h_le, h_true_after⟩
              unfold LeftwardTape.write at h_ne_def h_true_after
              simp only [LeftwardTape.nth] at h_ne_def h_true_after
              by_cases h : i = cfg.tape.head_pos
              · right; exact h
              · left
                refine ⟨?_, h_le, ?_⟩
                · rw [Turing.Tape.write_nth] at h_ne_def
                  split_ifs at h_ne_def with h_eq
                  · have : i = cfg.tape.head_pos := by linarith
                    contradiction
                  · exact h_ne_def
                · rw [Turing.Tape.write_nth] at h_true_after
                  split_ifs at h_true_after with h_eq
                  · have : i = cfg.tape.head_pos := by linarith
                    contradiction
                  · exact h_true_after
            · intro h
              cases h with
              | inl h_in_orig =>
                obtain ⟨h_ne_def, h_le, h_true_orig⟩ := h_in_orig
                refine ⟨?_, h_le, ?_⟩
                · unfold LeftwardTape.write
                  simp only [LeftwardTape.nth]
                  rw [Turing.Tape.write_nth]
                  have : i - cfg.tape.head_pos ≠ 0 := by
                    intro h_eq
                    have : i = cfg.tape.head_pos := by linarith
                    rw [this] at h_true_orig
                    simp only [sub_self, LeftwardTape.nth] at h_true_orig
                    have h_false' : cfg.tape.tape.nth 0 = false := h_false
                    rw [h_false'] at h_true_orig
                    simp at h_true_orig
                  simp [this, h_true_orig]
                · unfold LeftwardTape.write
                  simp only [LeftwardTape.nth]
                  rw [Turing.Tape.write_nth]
                  have : i - cfg.tape.head_pos ≠ 0 := by
                    intro h_eq
                    have : i = cfg.tape.head_pos := by linarith
                    rw [this] at h_true_orig
                    simp only [sub_self, LeftwardTape.nth] at h_true_orig
                    have h_false' : cfg.tape.tape.nth 0 = false := h_false
                    rw [h_false'] at h_true_orig
                    simp at h_true_orig
                  simp [this, h_true_orig]
              | inr h_eq =>
                rw [h_eq]
                refine ⟨?_, cfg.tape.head_nonpos, ?_⟩
                · unfold LeftwardTape.write
                  simp only [sub_self, LeftwardTape.nth]
                  rw [Turing.Tape.write_nth]
                  simp
                · unfold LeftwardTape.write
                  simp only [sub_self, LeftwardTape.nth]
                  rw [Turing.Tape.write_nth]
                  simp
          -- Complete the calculation
          rw [h_after]
          have h_disjoint : Disjoint cfg.tape.true_positions_absolute {cfg.tape.head_pos} := by
            rw [Finset.disjoint_singleton_right]
            exact h_not_mem
          rw [Finset.sum_union h_disjoint, Finset.sum_singleton, add_comm]
        exact h_exact
      -- Now we need to show diff = 2^k where k = write_witness cfg
      simp only [write_witness] at *
      rw [h_true, h_eq]
      simp only [sub_eq_add_neg, Int.natCast_add, Int.natCast_pow]
      ring
    · -- If current is true and writing false, diff = -2^k
      intro ⟨h_true, h_false⟩
      -- The encoding decreases by 2^k
      have h_dec := encode_decrease_write_false_over_true cfg h_true
      unfold encode_diff
      simp only [encode_config]
      -- We know cfg.tape.encode = (cfg.tape.write false).encode + 2^k
      -- So diff = -2^k
      -- First prove the equation with the explicit value
      have h_eq : cfg.tape.encode = (cfg.tape.write false).encode + 2^(Int.natAbs (-cfg.tape.head_pos)) := by
        -- We use the lemma encode_strict_decrease_write_false directly
        have h_dec_lemma := encode_strict_decrease_write_false cfg.tape cfg.tape.head_nonpos h_true
        -- The lemma shows (tape.write false).encode < tape.encode
        -- But from its proof, we know the exact equation
        have h_exact : cfg.tape.encode = (cfg.tape.write false).encode + 2^(Int.natAbs (-cfg.tape.head_pos)) := by
          -- This is the key equation from the proof of encode_strict_decrease_write_false
          -- at line 291 of EncodingDifference.lean
          -- We'll reprove it here
          unfold LeftwardTape.encode
          -- Show cfg.tape.head_pos is in cfg.tape.true_positions_absolute
          have h_mem : cfg.tape.head_pos ∈ cfg.tape.true_positions_absolute := by
            unfold LeftwardTape.true_positions_absolute
            simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
                       LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
            refine ⟨?_, cfg.tape.head_nonpos, ?_⟩
            · simp only [sub_self, LeftwardTape.nth]
              have : cfg.tape.tape.nth 0 = true := h_true
              rw [this]
              simp
            · simp only [sub_self, LeftwardTape.nth]
              exact h_true
          -- Split the sum
          have h_split : cfg.tape.true_positions_absolute =
                        (cfg.tape.true_positions_absolute \ {cfg.tape.head_pos}) ∪ {cfg.tape.head_pos} := by
            ext x
            simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
            by_cases h : x = cfg.tape.head_pos
            · simp [h, h_mem]
            · simp [h]
          -- After writing false, cfg.tape.head_pos is removed
          have h_after : (cfg.tape.write false).true_positions_absolute =
                        cfg.tape.true_positions_absolute \ {cfg.tape.head_pos} := by
            ext i
            simp only [Finset.mem_sdiff, Finset.mem_singleton]
            unfold LeftwardTape.true_positions_absolute
            simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
                       LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
            constructor
            · intro ⟨h_ne_def, h_le, h_true_after⟩
              unfold LeftwardTape.write at h_ne_def h_true_after
              simp only [LeftwardTape.nth] at h_ne_def h_true_after
              constructor
              · refine ⟨?_, h_le, ?_⟩
                · by_cases h : i - cfg.tape.head_pos = 0
                  · have : i = cfg.tape.head_pos := by linarith
                    rw [this] at h_true_after
                    simp only [sub_self] at h_true_after
                    rw [Turing.Tape.write_nth] at h_true_after
                    simp at h_true_after
                  · rw [Turing.Tape.write_nth] at h_ne_def
                    simp [h] at h_ne_def
                    have h_true_before : cfg.tape.tape.nth (i - cfg.tape.head_pos) = true := by
                      rw [Turing.Tape.write_nth] at h_true_after
                      simp [h] at h_true_after
                      exact h_true_after
                    rw [h_true_before]
                    simp
                · by_cases h : i - cfg.tape.head_pos = 0
                  · have : i = cfg.tape.head_pos := by linarith
                    rw [this] at h_true_after
                    simp only [sub_self] at h_true_after
                    rw [Turing.Tape.write_nth] at h_true_after
                    simp at h_true_after
                  · rw [Turing.Tape.write_nth] at h_true_after
                    simp [h] at h_true_after
                    exact h_true_after
              · intro h_eq
                rw [h_eq] at h_true_after
                simp only [sub_self] at h_true_after
                rw [Turing.Tape.write_nth] at h_true_after
                simp at h_true_after
            · intro ⟨⟨h_ne_def, h_le, h_true_orig⟩, h_ne⟩
              refine ⟨?_, h_le, ?_⟩
              · unfold LeftwardTape.write
                simp only [LeftwardTape.nth]
                rw [Turing.Tape.write_nth]
                have : i - cfg.tape.head_pos ≠ 0 := fun h => h_ne (by linarith : i = cfg.tape.head_pos)
                simp [this, h_true_orig]
              · unfold LeftwardTape.write
                simp only [LeftwardTape.nth]
                rw [Turing.Tape.write_nth]
                have : i - cfg.tape.head_pos ≠ 0 := fun h => h_ne (by linarith : i = cfg.tape.head_pos)
                simp [this, h_true_orig]
          -- Complete the calculation
          rw [h_split]
          have h_disjoint : Disjoint (cfg.tape.true_positions_absolute \ {cfg.tape.head_pos}) {cfg.tape.head_pos} :=
            Finset.sdiff_disjoint
          rw [Finset.sum_union h_disjoint, ← h_after, Finset.sum_singleton, add_comm]
        exact h_exact
      -- Now we need to show diff = -2^k where k = write_witness cfg
      simp only [write_witness] at *
      rw [h_false, h_eq]
      simp only [sub_eq_add_neg, Int.natCast_add, Int.natCast_pow]
      ring

end BinaryStepSequences

end LeftTM0
