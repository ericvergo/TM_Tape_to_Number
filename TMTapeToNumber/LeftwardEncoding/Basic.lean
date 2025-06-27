import TMTapeToNumber.LeftTM0.Step
import TMTapeToNumber.LeftTM0.LeftwardTape
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.MinMax
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.GeomSum
import Mathlib.Computability.Tape
import Mathlib.Computability.TuringMachine

set_option linter.unusedSectionVars false

namespace LeftTM0

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Encode a configuration's tape as a natural number -/
noncomputable def encode_config (cfg : Cfg Bool Λ) : ℕ :=
  cfg.tape.encode

/-- Encode just the tape content -/
noncomputable def encode_tape (tape : LeftwardTape Bool) : ℕ :=
  tape.encode

/-- Check if a position has true content (relative to head) -/
def has_true_at (cfg : Cfg Bool Λ) (pos : ℤ) : Bool :=
  cfg.tape.nth pos

/-- Check if an absolute tape position has true content -/
def has_true_at_absolute (cfg : Cfg Bool Λ) (pos : ℤ) : Bool :=
  cfg.tape.nth_absolute pos

/-- Get the leftmost absolute position with true content -/
noncomputable def leftmost_true_pos (cfg : Cfg Bool Λ) : Option ℤ :=
  -- Get all absolute positions with true values
  let true_positions := cfg.tape.true_positions_absolute
  match true_positions.toList.minimum with
  | ⊤ => none
  | (x : ℤ) => some x

/-- Get the rightmost absolute position with true content -/
noncomputable def rightmost_true_pos (cfg : Cfg Bool Λ) : Option ℤ :=
  -- Get all absolute positions with true values
  let true_positions := cfg.tape.true_positions_absolute
  match true_positions.toList.maximum with
  | ⊥ => none
  | (x : ℤ) => some x

-- Properties of encoding (now using absolute positions)
theorem encode_config_zero (cfg : Cfg Bool Λ) :
    cfg.tape.nth_absolute 0 = false →
    (∀ i < 0, cfg.tape.nth_absolute i = false) →
    encode_config cfg = 0 := by
  intro h0 h_neg
  -- encode_config cfg = cfg.tape.encode
  simp only [encode_config, encode_tape]
  -- cfg.tape.encode = ∑ i ∈ true_positions_absolute cfg.tape, 2^(Int.natAbs (-i))
  simp only [LeftwardTape.encode]
  -- We need to show that true_positions_absolute is empty
  -- true_positions_absolute filters for positions i ≤ 0 where nth_absolute i = true
  -- But we know nth_absolute 0 = false and for all i < 0, nth_absolute i = false
  -- So there are no positions i ≤ 0 with nth_absolute i = true
  have h_empty : cfg.tape.true_positions_absolute = ∅ := by
    simp only [LeftwardTape.true_positions_absolute]
    ext i
    simp only [Finset.mem_filter, Finset.notMem_empty]
    constructor
    · intro ⟨hi_mem, hi_le, hi_true⟩
      -- We have i ≤ 0 and cfg.tape.nth_absolute i = true
      -- Need to derive a contradiction
      cases' (Int.le_iff_lt_or_eq.mp hi_le) with hi_lt hi_eq
      · -- Case: i < 0
        have : cfg.tape.nth_absolute i = false := h_neg i hi_lt
        rw [this] at hi_true
        simp at hi_true
      · -- Case: i = 0
        rw [hi_eq] at hi_true
        rw [h0] at hi_true
        simp at hi_true
    · intro h_false
      -- h_false is False, so we can prove anything
      exact False.elim h_false
  rw [h_empty]
  simp

theorem encode_config_single_true_at_zero (cfg : Cfg Bool Λ) :
    cfg.tape.nth_absolute 0 = true →
    (∀ i < 0, cfg.tape.nth_absolute i = false) →
    encode_config cfg = 1 := by
  intro h0 h_neg
  -- encode_config cfg = cfg.tape.encode
  simp only [encode_config, encode_tape]
  -- cfg.tape.encode = ∑ i ∈ true_positions_absolute cfg.tape, 2^(Int.natAbs (-i))
  simp only [LeftwardTape.encode]
  -- true_positions_absolute contains exactly position 0
  have h_singleton : cfg.tape.true_positions_absolute = {0} := by
    simp only [LeftwardTape.true_positions_absolute]
    ext i
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro ⟨hi_mem, hi_le, hi_true⟩
      -- We have i ≤ 0 and cfg.tape.nth_absolute i = true
      cases' (Int.le_iff_lt_or_eq.mp hi_le) with hi_lt hi_eq
      · -- Case: i < 0
        have : cfg.tape.nth_absolute i = false := h_neg i hi_lt
        rw [this] at hi_true
        simp at hi_true
      · -- Case: i = 0
        exact hi_eq
    · intro hi_eq
      rw [hi_eq]
      refine ⟨?_, by norm_num, h0⟩
      -- Need to show 0 ∈ {i | has_content_at_absolute cfg.tape i}.toFinset
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf, LeftwardTape.has_content_at_absolute]
      -- nth_absolute 0 = true ≠ default
      rw [h0]
      -- For Bool, default = false, so true ≠ false
      simp only [ne_eq]
      -- true ≠ false
      trivial
  rw [h_singleton]
  -- Now compute: ∑ i ∈ {0}, 2^(Int.natAbs (-i))
  simp only [Finset.sum_singleton]
  -- 2^(Int.natAbs (-0)) = 2^(Int.natAbs 0) = 2^0 = 1
  simp

-- Removed encode_config_bound as encode_bound_by_leftmost in EncodingProperties.lean provides similar functionality

end LeftTM0
