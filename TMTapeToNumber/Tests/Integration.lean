import TMTapeToNumber

/-!
# Integration Tests

This file contains integration tests that verify the main components
of the TM Tape to Number formalization work correctly together.
-/

namespace TMTapeToNumber.Tests

open Turing LeftTM0 LeftwardTape LeftTM0.Theorems

/-- Test that basic encoding works -/
example : (mk_initial ([] : List Bool)).encode = 0 := encode_empty_tape

/-- Test encoding of a simple tape -/
example : 
  let tape := LeftwardTape.mk_initial [true, false, true]
  tape.encode = 5 := by
  -- Position 0: true → 2^0 = 1
  -- Position -1: false → 0
  -- Position -2: true → 2^2 = 4
  -- Total: 1 + 0 + 4 = 5
  sorry

/-- Test that sequence starts at 0 for empty initial tape -/
example {Λ : Type*} [Inhabited Λ] (M : Machine Bool Λ) :
  let init_cfg : Cfg Bool Λ := init []
  LeftTM0.sequence M init_cfg 0 = 0 := by
  simp [LeftTM0.sequence, sequence_zero, init, encode_config]
  exact encode_empty_tape

/-- Test that a simple write operation changes encoding correctly -/
example :
  let tape := LeftwardTape.mk_initial []
  let tape' := tape.write true
  tape'.encode = 1 := by
  -- Writing true at position 0 on empty tape gives 2^0 = 1
  sorry

/-- Verify binary step sequence conditions are type-correct -/
example : is_binary_step_sequence (fun n => n) ↔ 
  (0 = 0) ∧ 
  (∀ t, sequence_difference (fun n => n) t = 0 ∨ 
        ∃ k, sequence_difference (fun n => n) t = 2^k ∨ 
             sequence_difference (fun n => n) t = -(2^k : ℤ)) ∧
  (∀ t ∈ change_indices (fun n => n), True) := by -- simplified for type checking
  sorry

/-- Test that the TM infrastructure compiles and type-checks -/
example {Λ : Type*} [Inhabited Λ] (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) :
  let seq := sequence M init_cfg
  let cfg_at_5 := steps M 5 init_cfg
  seq 5 = encode_config cfg_at_5 := by
  simp [LeftTM0.sequence]

/-- Verify that sequence differences are integers (can be negative) -/
example {Λ : Type*} [Inhabited Λ] (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ) :
  ∃ (d : ℤ), BinaryStepSequences.sequence_diff M init_cfg t = d := by
  use BinaryStepSequences.sequence_diff M init_cfg t

/-- Test the main theorem statement compiles -/
example {Λ : Type*} [Inhabited Λ] (M : Machine Bool Λ) :
  (init [] : Cfg Bool Λ).tape.head_pos = 0 → 
  is_binary_step_sequence (LeftTM0.sequence M (init [])) := by
  intro h
  exact tm_sequence_is_binary_step_sequence M (init []) rfl h

/-- Test that growth bound applies -/
example (s : ℕ → ℕ) (h : is_binary_step_sequence s) :
  ∀ t, s t < 2^(t + 1) := by
  exact binary_step_sequence_growth_bound s h

/-- Verify the finite sequence generation theorem statement -/
example (s : List ℕ) (h : is_finite_binary_step_sequence s) :
  ∃ (M : Machine Bool (SeqGenState s.length)) (init_cfg : Cfg Bool (SeqGenState s.length)),
    init_cfg = init [] ∧ 
    init_cfg.tape.head_pos = 0 ∧
    ∀ i hi, sequence M init_cfg i = s.get ⟨i, hi⟩ := by
  exact finite_binary_step_sequence_generable s h

end TMTapeToNumber.Tests