import TMTapeToNumber.Encoding
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace TMTapeToNumber.Theorems

open TMTapeToNumber Turing TM0 Function
open BigOperators

/-- Create a tape with a single true at the given position -/
noncomputable def single_true_tape (pos : ℕ) : Tape Bool :=
  let base_tape := Tape.mk₁ [true]
  ((fun t => t.move Dir.left)^[pos] base_tape)

/-- The position bijection is indeed a bijection -/
theorem position_exponent_bijective : Function.Bijective position_to_exponent := by
  constructor
  · -- Injective
    intro z₁ z₂ h
    have := position_exponent_left_inv z₁
    rw [← this, h, position_exponent_left_inv]
  · -- Surjective
    intro n
    use exponent_to_position n
    exact position_exponent_right_inv n

/-- Powers of 2 with different exponents are distinct -/
theorem pow_two_injective : Function.Injective (fun n : ℕ => 2^n) := by
  intro n₁ n₂ h
  sorry

/-- Encoding respects position shifts -/
theorem encode_shift (tape : Tape Bool) (k : ℕ) (d : Dir)
    (h_support : has_finite_support tape) :
    has_finite_support ((fun t => t.move d)^[k] tape) := by
  sorry

/-- Tapes differing at finitely many positions have different encodings -/
theorem encode_tape_strict_injective (tape₁ tape₂ : Tape Bool)
    (h₁ : has_finite_support tape₁) (h₂ : has_finite_support tape₂)
    (h_diff : ∃ i, tape₁.nth i ≠ tape₂.nth i) :
    encode_tape tape₁ ≠ encode_tape tape₂ := by
  -- Key insight: different positions map to different powers of 2
  -- Binary representation uniqueness ensures different sums
  sorry

/-- Bound on encoding based on support size -/
theorem encode_tape_bound (tape : Tape Bool) (n : ℕ)
    (h_support : has_finite_support tape)
    (h_bound : ∀ i ∈ h_support.choose, Int.natAbs i ≤ n) :
    encode_tape tape ≤ 2^(2*n + 2) - 1 := by
  -- The largest exponent from position_to_exponent on [-n, n] is at most 2n+1
  -- So the sum is at most 2^0 + 2^1 + ... + 2^(2n+1) = 2^(2n+2) - 1
  sorry

/-- Encoding preserves tape operations -/
theorem encode_tape_write (tape : Tape Bool) (b : Bool)
    (h_support : has_finite_support tape) :
    let tape' := tape.write b
    has_finite_support tape' ∧
    encode_tape tape' =
      if b = true ∧ tape.head = false then
        encode_tape tape + 2^(position_to_exponent 0)
      else if b = false ∧ tape.head = true then
        encode_tape tape - 2^(position_to_exponent 0)
      else
        encode_tape tape := by
  sorry

/-- Moving the tape head doesn't change the encoding -/
theorem encode_tape_move (tape : Tape Bool) (d : Dir)
    (h_support : has_finite_support tape) :
    has_finite_support (tape.move d) ∧
    encode_tape (tape.move d) = encode_tape tape := by
  -- Moving only changes the head position, not the tape contents
  sorry

/-- Empty tape encodes to 0 -/
theorem encode_empty_tape :
    encode_tape (Tape.mk₁ ([] : List Bool)) = 0 := by
  sorry

/-- Tape with single true at origin encodes to 2^0 = 1 -/
theorem encode_single_true_origin :
    encode_tape (Tape.mk₁ [true]) = 1 := by
  have h_support : has_finite_support (Tape.mk₁ [true]) := by
    use {0}
    intro i hi
    simp at hi
    -- Show that positions other than 0 have default (false) value
    sorry
  apply encode_tape_single_true _ 0 h_support
  · -- Show position 0 has true
    simp [Tape.mk₁, Tape.nth]
    rfl
  · -- Show other positions have false
    intro i hi
    simp at hi
    sorry

end TMTapeToNumber.Theorems
