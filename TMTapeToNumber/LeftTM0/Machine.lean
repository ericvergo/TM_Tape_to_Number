import Mathlib.Computability.PostTuringMachine
import TMTapeToNumber.LeftTM0.LeftwardTape

open Turing

namespace LeftTM0

/-- A leftward-unbounded TM0 machine is just a standard TM0 machine -/
def Machine (Γ Λ : Type*) [Inhabited Γ] [Inhabited Λ] := TM0.Machine Γ Λ

/-- Configuration for leftward-unbounded TM -/
structure Cfg (Γ Λ : Type*) [Inhabited Γ] where
  q : Λ  -- Current state
  tape : LeftwardTape Γ  -- Leftward-constrained tape

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

instance : Inhabited (Cfg Γ Λ) := ⟨⟨default, LeftwardTape.mk_initial []⟩⟩

/-- Convert LeftTM0 config to standard TM0 config -/
def cfg_to_tm0 (cfg : Cfg Γ Λ) : TM0.Cfg Γ Λ :=
  ⟨cfg.q, cfg.tape.tape⟩

/-- Convert standard TM0 config to LeftTM0 config if position constraint holds -/
def cfg_from_tm0_unchecked (cfg : TM0.Cfg Γ Λ) (pos : ℤ) (h : pos ≤ 0) : Cfg Γ Λ :=
  ⟨cfg.q, LeftwardTape.mk_from_tape cfg.Tape pos h⟩

/-- Helper to determine current head position from TM0 tape -/
def tape_head_position (_ : Tape Γ) : ℤ := 
  -- This is a simplification - in the real implementation we'd need to track position properly
  0  -- For now, assume we start at position 0

/-- Read the current symbol -/
def read_symbol (cfg : Cfg Γ Λ) : Γ := cfg.tape.read

/-- Check if we can move right (not at position 0) -/
def can_move_right (cfg : Cfg Γ Λ) : Bool := cfg.tape.head_pos < 0

/-- Check if a TM0 step would violate leftward constraint -/
def step_preserves_constraint (M : Machine Γ Λ) (cfg : Cfg Γ Λ) : Bool :=
  match M cfg.q cfg.tape.read with
  | none => true  -- Halting preserves constraint
  | some (_, TM0.Stmt.move Dir.left) => true  -- Moving left is always OK
  | some (_, TM0.Stmt.move Dir.right) => can_move_right cfg  -- Moving right only if not at pos 0
  | some (_, TM0.Stmt.write _) => true  -- Writing preserves constraint

/-- Initial configuration from a list, positioned at the rightmost cell -/
def init (l : List Γ) : Cfg Γ Λ :=
  ⟨default, LeftwardTape.mk_initial l⟩

end LeftTM0