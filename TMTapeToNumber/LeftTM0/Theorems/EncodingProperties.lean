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
  -- Unfold the definition of encode
  simp only [encode, true_positions_absolute]
  -- Show that the filter produces an empty set
  -- because mk_initial [] creates a tape with only default (false) values
  have h_no_true : ∀ i ≤ 0, (mk_initial ([] : List Bool)).nth_absolute i ≠ true := by
    intro i _
    -- From mk_initial_nth, we know nth_absolute i = default = false for empty list
    rw [mk_initial_nth]
    simp
  -- The filter of positions with true values is empty
  have h_filter_empty : Finset.filter (fun i => i ≤ 0 ∧ (mk_initial ([] : List Bool)).nth_absolute i = true)
                        (finite_support_absolute (mk_initial ([] : List Bool))).toFinset = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.notMem_empty]
    constructor
    · intro ⟨_, hi_le, hi_true⟩
      -- This contradicts h_no_true
      exact h_no_true i hi_le hi_true
    · intro h
      exact False.elim h
  rw [h_filter_empty]
  simp

/-- Tape with single true at position 0 encodes to 1 -/
theorem encode_single_true_at_zero :
    (LeftwardTape.mk_initial [true]).encode = 1 := by
  -- Unfold the definition of encode
  simp only [encode, true_positions_absolute]
  -- The tape has true at position 0 and false elsewhere
  have h_at_zero : (mk_initial [true]).nth_absolute 0 = true := by
    rw [mk_initial_nth]
    simp
  have h_not_at_nonzero : ∀ i < 0, (mk_initial [true]).nth_absolute i = false := by
    intro i hi
    rw [mk_initial_nth]
    simp [hi]
  -- The filter produces exactly the singleton {0}
  have h_filter_singleton : Finset.filter (fun i => i ≤ 0 ∧ (mk_initial [true]).nth_absolute i = true)
                           (finite_support_absolute (mk_initial [true])).toFinset = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro ⟨_, hi_le, hi_true⟩
      -- i ≤ 0 and nth_absolute i = true
      -- By cases on whether i = 0 or i < 0
      by_cases h : i = 0
      · exact h
      · -- i < 0
        have hi_neg : i < 0 := lt_of_le_of_ne hi_le h
        have : (mk_initial [true]).nth_absolute i = false := h_not_at_nonzero i hi_neg
        rw [this] at hi_true
        simp at hi_true
    · intro hi_eq
      rw [hi_eq]
      refine ⟨?_, le_refl 0, h_at_zero⟩
      -- Need to show 0 ∈ (finite_support_absolute (mk_initial [true])).toFinset
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf]
      simp only [has_content_at_absolute, h_at_zero]
      trivial
  rw [h_filter_singleton]
  -- Now compute: ∑ i ∈ {0}, 2^(Int.natAbs (-i))
  simp

/-- Tape with single true at position -k encodes to 2^k -/
theorem encode_single_true_at_neg_k (k : ℕ) :
    let tape := (fun t : LeftwardTape Bool => t.move_left)^[k] (LeftwardTape.mk_initial [])
    let tape' := tape.write true
    tape'.encode = 2^k := by
  sorry

/-- Encoding respects the binary representation -/
theorem encode_binary_representation (tape : LeftwardTape Bool) :
    tape.encode = ∑ i ∈ tape.true_positions_absolute, 2^(Int.natAbs (-i)) := by
  -- This is just the definition of encode
  rfl

/-- Moving the head doesn't change the encoding -/
theorem encode_move_invariant (tape : LeftwardTape Bool) :
    tape.move_left.encode = tape.encode ∧
    tape.move_right.encode = tape.encode := by
  constructor
  · -- move_left case
    exact encode_move_left tape
  · -- move_right case
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