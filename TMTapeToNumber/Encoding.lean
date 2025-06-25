import Mathlib.Computability.TuringMachine
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Turing TM0
open BigOperators

namespace TMTapeToNumber

/-- Bijection from integers to natural numbers using interleaving strategy:
    0 → 0, -1 → 1, 1 → 2, -2 → 3, 2 → 4, ... -/
def position_to_exponent : ℤ → ℕ
  | (n : ℕ) => 2 * n          -- 0, 1, 2, ... → 0, 2, 4, ...
  | -(n + 1 : ℕ) => 2 * n + 1 -- -1, -2, -3, ... → 1, 3, 5, ...

/-- Inverse of position_to_exponent -/
def exponent_to_position : ℕ → ℤ
  | n => if n % 2 = 0 then (n / 2 : ℕ) else -((n / 2 : ℕ) + 1)

/-- The bijection is a left inverse -/
theorem position_exponent_left_inv (z : ℤ) : 
  exponent_to_position (position_to_exponent z) = z := by
  sorry

/-- The bijection is a right inverse -/
theorem position_exponent_right_inv (n : ℕ) : 
  position_to_exponent (exponent_to_position n) = n := by
  sorry

/-- A tape has finite support if it differs from the default value at only finitely many positions -/
def has_finite_support (tape : Tape Bool) : Prop :=
  ∃ (s : Finset ℤ), ∀ i : ℤ, i ∉ s → tape.nth i = default

/-- Encode a boolean tape as a natural number.
    Position i contributes 2^(position_to_exponent i) when tape.nth i = true -/
noncomputable def encode_tape (tape : Tape Bool) : ℕ :=
  sorry  -- This requires classical logic due to finite support

/-- Encoding respects tape equality on finite support -/
theorem encode_tape_ext {tape₁ tape₂ : Tape Bool} 
    (h₁ : has_finite_support tape₁) (h₂ : has_finite_support tape₂)
    (h_eq : ∀ i, tape₁.nth i = tape₂.nth i) : 
    encode_tape tape₁ = encode_tape tape₂ := by
  sorry

/-- A tape with all false values encodes to 0 -/
theorem encode_tape_all_false (tape : Tape Bool) 
    (h_support : has_finite_support tape)
    (h_false : ∀ i, tape.nth i = false) : 
    encode_tape tape = 0 := by
  sorry

/-- A tape with a single true at position i encodes to 2^(position_to_exponent i) -/
theorem encode_tape_single_true (tape : Tape Bool) (pos : ℤ)
    (h_support : has_finite_support tape)
    (h_true : tape.nth pos = true)
    (h_false : ∀ i ≠ pos, tape.nth i = false) :
    encode_tape tape = 2^(position_to_exponent pos) := by
  sorry

/-- Encoding is injective on tapes with finite support -/
theorem encode_tape_injective : 
    Function.Injective (fun tape : {t : Tape Bool // has_finite_support t} => encode_tape tape.val) := by
  sorry

end TMTapeToNumber