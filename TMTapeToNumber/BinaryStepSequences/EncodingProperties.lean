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

/-- The witness k value when writing changes the encoding -/
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
    (h_diff : encode_config cfg' - encode_config cfg = 0) :
    encode_config cfg' = encode_config cfg := by
  sorry

/-- Natural subtraction zero and integer difference = 0 implies equality -/
lemma nat_sub_zero_and_int_diff_zero (a b : ℕ)
    (_h_nat : a - b = 0)
    (h_int : (a : ℤ) - (b : ℤ) = 0) :
    a = b := by
  -- From the integer equality, we get a = b
  have h_eq : (a : ℤ) = (b : ℤ) := by linarith
  -- Cast injective gives us a = b
  exact Nat.cast_injective h_eq

/-- Writing the same value doesn't change encoding -/
lemma encode_same_value_zero_diff (cfg : Cfg Bool Λ) (a : Bool)
    (h_same : cfg.tape.nth 0 = a) :
    encode_diff cfg ⟨cfg.q, cfg.tape.write a⟩ = 0 := by
  -- Writing the same value doesn't change the encoding
  unfold encode_diff
  simp only [encode_config]
  -- When we write the same value, the encoding stays the same
  have h_eq : (cfg.tape.write a).encode = cfg.tape.encode := by
    sorry -- This requires showing that writing the same value preserves encoding
  rw [h_eq]
  simp

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
  sorry

/-- Direct computation of encoding difference when writing at head position -/
lemma encode_write_diff_value (cfg : Cfg Bool Λ) (a : Bool) :
    let new_cfg := ⟨cfg.q, cfg.tape.write a⟩
    let diff := encode_diff cfg new_cfg
    let k := Int.natAbs (-cfg.tape.head_pos)
    (cfg.tape.nth 0 = a → diff = 0) ∧
    (cfg.tape.nth 0 = false ∧ a = true → diff = 2^k) ∧
    (cfg.tape.nth 0 = true ∧ a = false → diff = -(2^k : ℤ)) := by
  sorry

end BinaryStepSequences

end LeftTM0