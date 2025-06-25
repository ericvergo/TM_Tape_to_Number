import TMTapeToNumber.LeftTM0.Sequences

open Turing

namespace LeftTM0.Examples

/-- States for the powers of 2 machine -/
inductive PowersState where
  | q0  -- Scan right looking for rightmost 1  
  | q1  -- Move back left writing 1s

instance : Inhabited PowersState := ⟨PowersState.q0⟩

/-- The powers of 2 machine -/
def powers_machine : Machine Bool PowersState :=
  fun state symbol ↦
    match state, symbol with
    | PowersState.q0, true  => some (PowersState.q1, TM0.Stmt.write false)
    | PowersState.q0, false => some (PowersState.q0, TM0.Stmt.move Dir.left)
    | PowersState.q1, true  => some (PowersState.q1, TM0.Stmt.move Dir.left)  
    | PowersState.q1, false => some (PowersState.q0, TM0.Stmt.write true)

/-- Initial configuration: single 1 at position 0 -/
def powers_initial : Cfg Bool PowersState :=
  ⟨PowersState.q0, LeftwardTape.mk_initial [true]⟩

/-- The powers of 2 sequence -/
noncomputable def powers_sequence : ℕ → ℕ :=
  sequence powers_machine powers_initial

-- Trace the first few steps manually for verification
/-- Configuration after 0 steps (initial) -/
def powers_step_0 : Cfg Bool PowersState := powers_initial

/-- Expected configuration after 1 step -/
def powers_step_1_expected : Cfg Bool PowersState :=
  -- From q0 reading true: write false, move right, go to q1
  -- But we can't move right from position 0, so we should halt
  powers_initial  -- This needs refinement based on actual semantics

-- Basic correctness properties
theorem powers_sequence_zero : powers_sequence 0 = 1 := by
  unfold powers_sequence sequence
  simp [steps, Function.iterate_zero_apply]
  -- Should follow from encode_config of initial configuration
  sorry

theorem powers_initial_encodes_to_one : 
    encode_config powers_initial = 1 := by
  unfold powers_initial encode_config
  -- Should follow from LeftwardTape.mk_initial [true] encoding to 1
  sorry

-- Expected behavior: generates powers of 2
theorem powers_sequence_generates_powers : 
    ∀ n, ∃ k, powers_sequence n = 2^k := by sorry

-- More specific: should generate 1, 2, 4, 8, 16, ...
theorem powers_sequence_explicit_values :
    powers_sequence 0 = 1 ∧
    powers_sequence 1 = 2 ∧  
    powers_sequence 2 = 4 ∧
    powers_sequence 3 = 8 := by sorry

-- The machine should not halt immediately  
theorem powers_machine_productive :
    ∃ n > 0, ¬is_terminal powers_machine (steps powers_machine n powers_initial) := by sorry

/-- Helper to trace execution for debugging -/
def trace_powers_execution (n : ℕ) : Cfg Bool PowersState :=
  steps powers_machine n powers_initial

/-- Get the encoding at each step for analysis -/
noncomputable def powers_encoding_at_step (n : ℕ) : ℕ :=
  encode_config (trace_powers_execution n)

-- Verify the machine follows the expected transition pattern
theorem powers_machine_transitions :
    powers_machine PowersState.q0 true = some (PowersState.q1, TM0.Stmt.write false) ∧
    powers_machine PowersState.q0 false = some (PowersState.q0, TM0.Stmt.move Dir.left) ∧
    powers_machine PowersState.q1 true = some (PowersState.q1, TM0.Stmt.move Dir.left) ∧
    powers_machine PowersState.q1 false = some (PowersState.q0, TM0.Stmt.write true) := by
  simp [powers_machine]

end LeftTM0.Examples