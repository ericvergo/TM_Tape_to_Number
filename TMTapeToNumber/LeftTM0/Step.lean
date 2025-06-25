import TMTapeToNumber.LeftTM0.Machine
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation

open Turing
open Relation

namespace LeftTM0

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Step function that enforces leftward constraints -/
def step (M : Machine Γ Λ) : Cfg Γ Λ → Option (Cfg Γ Λ) :=
  fun cfg ↦ 
    if step_preserves_constraint M cfg then
      match M cfg.q cfg.tape.read with
      | none => none  -- Machine halts
      | some (q', stmt) => some ⟨q', apply_stmt stmt cfg.tape⟩
    else none  -- Halt if constraint would be violated

where
  /-- Apply a TM0 statement to a leftward tape -/
  apply_stmt (stmt : TM0.Stmt Γ) (tape : LeftwardTape Γ) : LeftwardTape Γ :=
    match stmt with
    | TM0.Stmt.move Dir.left => tape.move_left
    | TM0.Stmt.move Dir.right => tape.move_right
    | TM0.Stmt.write a => tape.write a

/-- Take a single step, returning the result or the same config if halted -/
def step_or_stay (M : Machine Γ Λ) (cfg : Cfg Γ Λ) : Cfg Γ Λ :=
  match step M cfg with
  | none => cfg
  | some cfg' => cfg'

/-- Execute multiple steps -/
def steps (M : Machine Γ Λ) (n : ℕ) : Cfg Γ Λ → Cfg Γ Λ :=
  Nat.iterate (step_or_stay M) n

/-- Reachability relation for LeftTM0 -/
def Reaches (M : Machine Γ Λ) : Cfg Γ Λ → Cfg Γ Λ → Prop :=
  ReflTransGen (fun a b ↦ b ∈ step M a)

/-- A configuration is terminal if the machine halts from it -/
def is_terminal (M : Machine Γ Λ) (cfg : Cfg Γ Λ) : Prop :=
  step M cfg = none

/-- Check if a machine reaches a terminal state from given config -/
def terminates (M : Machine Γ Λ) (cfg : Cfg Γ Λ) : Prop :=
  ∃ cfg', Reaches M cfg cfg' ∧ is_terminal M cfg'

/-- Execute until termination or n steps, whichever comes first -/
def steps_until_halt (M : Machine Γ Λ) (max_steps : ℕ) (cfg : Cfg Γ Λ) : Cfg Γ Λ :=
  let rec loop (remaining : ℕ) (current : Cfg Γ Λ) : Cfg Γ Λ :=
    match remaining with
    | 0 => current
    | n + 1 => 
        match step M current with
        | none => current  -- Halted
        | some next => loop n next
  loop max_steps cfg

-- Basic properties
theorem step_preserves_position_constraint (M : Machine Γ Λ) (cfg : Cfg Γ Λ) :
    ∀ cfg', step M cfg = some cfg' → cfg'.tape.head_pos ≤ 0 := by
  sorry

theorem steps_preserves_position_constraint (M : Machine Γ Λ) (cfg : Cfg Γ Λ) (n : ℕ) :
    (steps M n cfg).tape.head_pos ≤ 0 := by
  sorry

end LeftTM0