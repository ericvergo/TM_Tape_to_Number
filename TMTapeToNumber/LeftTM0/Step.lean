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
  intro cfg' h_step
  -- Unfold the step function
  simp only [step] at h_step
  -- Split on whether step_preserves_constraint was true
  split_ifs at h_step with h_constraint
  · -- Case: step_preserves_constraint was true, so step proceeded
    -- Match on what the machine does
    match h_machine : M cfg.q cfg.tape.read with
    | none =>
      -- Machine halts, contradiction with h_step
      simp [h_machine] at h_step
    | some (q', stmt) =>
      -- h_step says cfg' = ⟨q', apply_stmt stmt cfg.tape⟩
      simp [h_machine] at h_step
      -- cfg' = { q := q', tape := step.apply_stmt stmt cfg.tape }
      rw [← h_step]
      -- Now we need to show (apply_stmt stmt cfg.tape).head_pos ≤ 0
      cases stmt with
      | move dir =>
        cases dir with
        | left =>
          -- Moving left always preserves the constraint
          simp only [step.apply_stmt, LeftwardTape.move_left]
          -- move_left decreases head_pos by 1
          have h := cfg.tape.head_nonpos
          linarith
        | right =>
          -- Moving right preserves constraint because step_preserves_constraint was true
          simp only [step.apply_stmt, LeftwardTape.move_right]
          -- move_right only moves if head_pos < 0
          split_ifs with h_can_move
          · -- Can move right: new position is head_pos + 1
            have h := cfg.tape.head_nonpos
            linarith [h_can_move]
          · -- Cannot move right: position unchanged
            exact cfg.tape.head_nonpos
      | write a =>
        -- Writing doesn't change position
        simp only [step.apply_stmt, LeftwardTape.write]
        exact cfg.tape.head_nonpos

theorem steps_preserves_position_constraint (M : Machine Γ Λ) (cfg : Cfg Γ Λ) (n : ℕ) :
    (steps M n cfg).tape.head_pos ≤ 0 := by
  -- Prove by induction on n
  induction n generalizing cfg with
  | zero =>
    -- Base case: steps M 0 cfg = cfg
    simp only [steps, Function.iterate_zero_apply]
    exact cfg.tape.head_nonpos
  | succ m ih =>
    -- Inductive case: steps M (m+1) cfg = step_or_stay M (steps M m cfg)
    simp only [steps, Function.iterate_succ_apply']
    -- Apply inductive hypothesis to (steps M m cfg)
    let cfg_m := steps M m cfg
    have h_m : cfg_m.tape.head_pos ≤ 0 := ih cfg
    -- Now need to show: (step_or_stay M cfg_m).tape.head_pos ≤ 0
    unfold step_or_stay
    -- Case split on whether step returns none or some
    match h_step : step M cfg_m with
    | none =>
      -- step_or_stay returns cfg_m unchanged
      exact h_m
    | some cfg' =>
      -- step_or_stay returns cfg'
      -- Use step_preserves_position_constraint
      exact step_preserves_position_constraint M cfg_m cfg' h_step

end LeftTM0
