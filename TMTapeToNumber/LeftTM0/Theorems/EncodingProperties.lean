import TMTapeToNumber.LeftTM0.LeftwardEncoding
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace LeftTM0.Theorems

open LeftTM0 LeftwardTape
open BigOperators

variable {Λ : Type*} [Inhabited Λ]

/-- Empty tape encodes to 0 -/
theorem encode_empty_tape :
    (LeftwardTape.mk_initial ([] : List Bool)).encode = 0 := by
  sorry

/-- Tape with single true at position 0 encodes to 1 -/
theorem encode_single_true_at_zero :
    (LeftwardTape.mk_initial [true]).encode = 1 := by
  sorry

/-- Tape with single true at position -k encodes to 2^k -/
theorem encode_single_true_at_neg_k (k : ℕ) :
    let tape := (fun t : LeftwardTape Bool => t.move_left)^[k] (LeftwardTape.mk_initial [])
    let tape' := tape.write true
    tape'.encode = 2^k := by
  sorry

/-- Encoding respects the binary representation -/
theorem encode_binary_representation (tape : LeftwardTape Bool) :
    tape.encode = ∑ i ∈ tape.true_positions_absolute, 2^(Int.natAbs (-i)) := by
  sorry

/-- Moving the head doesn't change the encoding -/
theorem encode_move_invariant (tape : LeftwardTape Bool) :
    tape.move_left.encode = tape.encode ∧
    tape.move_right.encode = tape.encode := by
  sorry

/-- Writing true increases encoding by appropriate power of 2 -/
theorem encode_write_true (tape : LeftwardTape Bool) :
    tape.read = false →
    (tape.write true).encode = tape.encode + 2^(Int.natAbs (-tape.head_pos)) := by
  sorry

/-- Writing false decreases encoding by appropriate power of 2 -/
theorem encode_write_false (tape : LeftwardTape Bool) :
    tape.read = true →
    (tape.write false).encode = tape.encode - 2^(Int.natAbs (-tape.head_pos)) := by
  sorry

/-- Bound on encoding based on leftmost true position -/
theorem encode_bound_by_leftmost (tape : LeftwardTape Bool) (n : ℕ) :
    (∀ i < -(n : ℤ), tape.nth_absolute i = false) →
    tape.encode < 2^(n.succ) := by
  sorry

/-- Encoding is injective -/
theorem encode_injective : Function.Injective (LeftwardTape.encode : LeftwardTape Bool → ℕ) := by
  sorry

/-- Two tapes with same content at all positions have same encoding -/
theorem encode_ext (tape₁ tape₂ : LeftwardTape Bool) :
    (∀ i ≤ 0, tape₁.nth_absolute i = tape₂.nth_absolute i) →
    tape₁.encode = tape₂.encode := by
  sorry

end LeftTM0.Theorems