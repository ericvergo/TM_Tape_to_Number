import Mathlib.Computability.Tape
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Set.Finite.Basic

open Turing
open BigOperators

/-- A leftward-unbounded tape that restricts operations to positions ≤ 0 -/
structure LeftwardTape (Γ : Type*) [Inhabited Γ] where
  tape : Tape Γ
  head_pos : ℤ  -- Current head position
  head_nonpos : head_pos ≤ 0  -- Invariant: head must be ≤ 0

namespace LeftwardTape

variable {Γ : Type*} [Inhabited Γ]

/-- Read the symbol at the current head position -/
def read (T : LeftwardTape Γ) : Γ := T.tape.head

/-- Write a symbol at the current head position -/
def write (T : LeftwardTape Γ) (a : Γ) : LeftwardTape Γ :=
  { T with tape := T.tape.write a }

/-- Move the head left (always allowed) -/
def move_left (T : LeftwardTape Γ) : LeftwardTape Γ :=
  { tape := T.tape.move Dir.left
    head_pos := T.head_pos - 1
    head_nonpos := by 
      linarith [T.head_nonpos] }

/-- Move the head right (only if not at position 0) -/
def move_right (T : LeftwardTape Γ) : LeftwardTape Γ :=
  if h : T.head_pos < 0 then
    { tape := T.tape.move Dir.right
      head_pos := T.head_pos + 1  
      head_nonpos := by 
        linarith [h] }
  else T  -- Cannot move right from position 0

/-- Create a LeftwardTape from a standard tape, if head position is valid -/
def mk_from_tape (tape : Tape Γ) (pos : ℤ) (h : pos ≤ 0) : LeftwardTape Γ :=
  ⟨tape, pos, h⟩

/-- Create initial LeftwardTape with given list, head at position 0 -/
def mk_initial (l : List Γ) : LeftwardTape Γ :=
  ⟨Tape.mk₁ l, 0, by 
    norm_num⟩

/-- Get the tape content at a specific position relative to the current head -/
def nth (T : LeftwardTape Γ) (n : ℤ) : Γ := T.tape.nth (n - T.head_pos)

/-- Get the tape content at an absolute tape position -/
def nth_absolute (T : LeftwardTape Γ) (n : ℤ) : Γ := T.tape.nth n

/-- Check if the tape has non-default content at position i (relative to head) -/
def has_content_at (T : LeftwardTape Γ) (i : ℤ) : Prop := 
  T.nth i ≠ default

/-- Check if the tape has non-default content at absolute position i -/
def has_content_at_absolute (T : LeftwardTape Γ) (i : ℤ) : Prop := 
  T.nth_absolute i ≠ default

/-- The set of absolute positions with non-default content is finite -/
theorem finite_support_absolute (T : LeftwardTape Γ) : 
    Set.Finite {i : ℤ | T.has_content_at_absolute i} := by
  sorry

/-- For Bool tapes, get the set of absolute positions with true values that are ≤ 0 -/
noncomputable def true_positions_absolute (T : LeftwardTape Bool) : Finset ℤ :=
  (finite_support_absolute T).toFinset.filter (fun i => i ≤ 0 ∧ T.nth_absolute i = true)

/-- Integer encoding for Bool tapes based on absolute positions -/
noncomputable def encode (T : LeftwardTape Bool) : ℕ :=
  -- Sum over all absolute tape positions i ≤ 0 where the tape has content 'true'
  -- Absolute position 0 contributes 2^0 = 1 (ones place)
  -- Absolute position -1 contributes 2^1 = 2 (twos place)
  -- Absolute position -2 contributes 2^2 = 4 (fours place), etc.
  ∑ i ∈ true_positions_absolute T, 2^(Int.natAbs (-i))

/-- The set of positions with non-default content is finite (keeping for compatibility) -/
theorem finite_support (T : LeftwardTape Γ) : 
    Set.Finite {i : ℤ | T.has_content_at i} := by
  sorry

/-- For Bool tapes, get the set of positions with true values (keeping for compatibility) -/
noncomputable def true_positions (T : LeftwardTape Bool) : Finset ℤ :=
  true_positions_absolute T

/-- Example: tape with single 'true' at absolute position 0 encodes to 1 -/
example : 
  let T := mk_initial [true]
  encode T = 1 := by sorry

/-- Example: encoding is independent of head position -/
example :
  let T1 := mk_initial [true, false, true]  -- Head at position 0
  let T2 := T1.move_left.move_left          -- Head at position -2
  encode T1 = encode T2 := by sorry

end LeftwardTape