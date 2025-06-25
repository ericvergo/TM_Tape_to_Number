import Mathlib.Computability.Tape
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

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

/-- Get the tape content at a specific position -/
def nth (T : LeftwardTape Γ) (n : ℤ) : Γ := T.tape.nth (n - T.head_pos)

/-- Check if the tape has non-default content at position i -/
def has_content_at (T : LeftwardTape Γ) (i : ℤ) : Prop := 
  T.nth i ≠ default

/-- Integer encoding for Bool tapes (reading right to left) -/
noncomputable def encode (T : LeftwardTape Bool) : ℕ :=
  -- We need to sum over all positions i ≤ 0 where the tape has content 'true'
  -- Position i contributes 2^(-i) to the sum
  -- For now, we'll approximate by considering a finite range
  let range := Finset.range 100  -- Consider positions 0, -1, -2, ..., -99
  ∑ k ∈ range, if T.nth (-Int.ofNat k) = true then 2^k else 0

/-- Example: tape with single 'true' at position 0 encodes to 1 -/
example : 
  let T := mk_initial [true]
  encode T = 1 := by sorry

end LeftwardTape