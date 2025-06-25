import TMTapeToNumber.Encoding
import Mathlib.Computability.TuringMachine

open Turing TM0 Function

namespace TMTapeToNumber

variable {Λ : Type*} [Inhabited Λ]

/-- Take a single step, returning the result or the same config if halted -/
def step_or_stay (M : Machine Bool Λ) (cfg : Cfg Bool Λ) : Cfg Bool Λ :=
  match step M cfg with
  | none => cfg
  | some cfg' => cfg'

/-- Generate a sequence of natural numbers from a Turing machine by encoding
    the tape at each step of execution -/
noncomputable def sequence (M : Machine Bool Λ) (init : Cfg Bool Λ) : ℕ → ℕ :=
  fun n => encode_tape ((step_or_stay M)^[n] init).Tape

/-- The sequence at step 0 is the encoding of the initial tape -/
theorem sequence_zero (M : Machine Bool Λ) (init : Cfg Bool Λ) :
    sequence M init 0 = encode_tape init.Tape := by
  simp [sequence, Function.iterate_zero]

/-- The sequence at step n+1 is determined by stepping the machine -/
theorem sequence_succ (M : Machine Bool Λ) (init : Cfg Bool Λ) (n : ℕ) :
    sequence M init (n + 1) = encode_tape ((step_or_stay M)^[n + 1] init).Tape := by
  simp [sequence]

/-- If the machine halts at step n, the sequence is constant thereafter -/
theorem sequence_const_after_halt (M : Machine Bool Λ) (init : Cfg Bool Λ) (n : ℕ)
    (h_halt : ((step_or_stay M)^[n] init).q = default) :
    ∀ m ≥ n, sequence M init m = sequence M init n := by
  sorry

/-- Create an initial configuration from a list of booleans -/
def init_from_list (l : List Bool) : Cfg Bool Λ :=
  ⟨default, Tape.mk₁ l⟩

/-- Helper to create a configuration with the tape head at a specific position -/
def init_at_pos (l : List Bool) (pos : ℕ) : Cfg Bool Λ :=
  ⟨default, ((fun t => t.move Dir.left)^[pos] (Tape.mk₁ l))⟩

/-- If all configurations in the execution have finite support,
    then all values in the sequence are well-defined -/
theorem sequence_finite_support (M : Machine Bool Λ) (init : Cfg Bool Λ)
    (_ : ∀ n, has_finite_support ((step_or_stay M)^[n] init).Tape) :
    ∀ n, ∃ m, sequence M init n = m := by
  intro n
  use sequence M init n

end TMTapeToNumber
