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

/-- A single step changes the encoding by at most 2^k for some k -/
theorem encode_step_diff (M : Machine Bool Λ) (cfg cfg' : Cfg Bool Λ) :
    step M cfg = some cfg' →
    ∃ k : ℕ, |Int.ofNat (encode_config cfg') - Int.ofNat (encode_config cfg)| ≤ 2^k := by
  intro h_step
  -- A step can only: move left/right, write true/false
  -- Each of these changes encoding by at most 2^|current_position|
  use Int.natAbs (-cfg.tape.head_pos)

  -- The proof establishes that any single step changes the encoding by at most 2^|head_pos|
  -- For moves: encoding doesn't change (difference is 0)
  -- For writes: encoding changes by at most 2^|head_pos|

  -- Unfold the step function to get the statement executed
  simp only [step] at h_step
  split_ifs at h_step with h_constraint
  · -- Case: step_preserves_constraint was true
    match h_machine : M cfg.q cfg.tape.read with
    | none =>
      -- Machine halts, contradiction with h_step
      simp [h_machine] at h_step
    | some (q', stmt) =>
      -- h_step says cfg' = ⟨q', apply_stmt stmt cfg.tape⟩
      simp [h_machine] at h_step
      rw [← h_step]
      -- Now we need to analyze what statement was executed
      cases stmt with
      | move dir =>
        cases dir with
        | left =>
          -- Moving left doesn't change encoding
          simp only [step.apply_stmt]
          -- encode_config cfg' = encode (move_left cfg.tape)
          -- encode_config cfg = encode cfg.tape
          simp only [encode_config]
          -- We know that move_left preserves encoding from encode_move_left
          rw [LeftwardTape.encode_move_left]
          -- Now |encode cfg.tape - encode cfg.tape| = 0 ≤ 2^k for any k
          simp
        | right =>
          -- Moving right doesn't change encoding
          simp only [step.apply_stmt, encode_config]
          -- We need to prove that encode move_right = encode original
          -- This follows from the fact that move_right preserves absolute tape content
          have h_encode_eq : LeftwardTape.encode cfg.tape.move_right = LeftwardTape.encode cfg.tape := by
            -- The encoding depends only on absolute positions
            simp only [LeftwardTape.encode]
            -- true_positions_absolute are the same for both tapes
            congr 1
            ext i
            simp only [LeftwardTape.true_positions_absolute, Finset.mem_filter, Set.Finite.mem_toFinset]
            constructor
            · intro ⟨hmem, hle, htrue⟩
              refine ⟨?_, hle, ?_⟩
              · -- Show membership in finite support
                simp only [Set.mem_setOf, LeftwardTape.has_content_at_absolute] at hmem ⊢
                rw [← LeftwardTape.move_right_preserves_nth_absolute cfg.tape i]
                exact hmem
              · -- Show the value is true
                rw [← LeftwardTape.move_right_preserves_nth_absolute cfg.tape i]
                exact htrue
            · intro ⟨hmem, hle, htrue⟩
              refine ⟨?_, hle, ?_⟩
              · -- Show membership in finite support
                simp only [Set.mem_setOf, LeftwardTape.has_content_at_absolute] at hmem ⊢
                rw [LeftwardTape.move_right_preserves_nth_absolute cfg.tape i]
                exact hmem
              · -- Show the value is true
                rw [LeftwardTape.move_right_preserves_nth_absolute cfg.tape i]
                exact htrue
          -- Now use this equality
          rw [h_encode_eq]
          -- |encode cfg.tape - encode cfg.tape| = 0 ≤ 2^k for any k
          simp
      | write a =>
        -- Writing can change the encoding by 2^|head_pos| at most
        simp only [step.apply_stmt, encode_config]

        -- The write operation only changes the tape at position 0 (relative to head)
        -- In absolute terms, this is position cfg.tape.head_pos
        -- The encoding can change by at most 2^|head_pos|

        -- We'll prove this by showing the difference is at most 2^|head_pos|
        sorry

end LeftTM0
