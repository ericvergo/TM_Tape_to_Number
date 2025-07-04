/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean FRO Team
-/
import TMTapeToNumber.BinaryStepSequences.Basic

/-!
# Encoding Difference Lemmas

This file contains the core lemmas about how the encoding changes when writing to the tape.
The main theorem is `encode_diff_at_write`, which shows that writing changes the encoding
by 0 or ±2^k where k is the absolute position.
-/

set_option linter.unusedSectionVars false

namespace LeftTM0

namespace BinaryStepSequences

variable {Λ : Type*} [Inhabited Λ]

open Turing LeftTM0 LeftwardTape

/-- Integer difference between two configuration encodings -/
noncomputable def encode_diff (cfg cfg' : Cfg Bool Λ) : ℤ :=
  (encode_config cfg' : ℤ) - (encode_config cfg : ℤ)

/-- The difference in encoding when writing at a position is ±2^k where k is the absolute position -/
lemma encode_diff_at_write (cfg : Cfg Bool Λ) (a : Bool) :
    let cfg' := ⟨cfg.q, cfg.tape.write a⟩
    let diff := encode_diff cfg cfg'
    diff = 0 ∨ ∃ k : ℕ, diff = 2^k ∨ diff = -(2^k : ℤ) := by
  sorry

/-- Writing false over true strictly decreases the encoding -/
lemma encode_strict_decrease_write_false (tape : LeftwardTape Bool)
    (h_pos : tape.head_pos ≤ 0)
    (h_true : tape.nth 0 = true) :
    (tape.write false).encode < tape.encode := by
  sorry

/-- Writing true over false strictly increases the encoding -/
lemma encode_strict_increase_write_true (tape : LeftwardTape Bool)
    (h_pos : tape.head_pos ≤ 0)
    (h_false : tape.nth 0 = false) :
    tape.encode < (tape.write true).encode := by
  sorry

/-- Writing false over true decreases the encoding -/
lemma encode_decrease_write_false_over_true (cfg : Cfg Bool Λ)
    (h_true : cfg.tape.nth 0 = true) :
    (cfg.tape.write false).encode < cfg.tape.encode := by
  exact encode_strict_decrease_write_false cfg.tape cfg.tape.head_nonpos h_true

/-- Writing true over false increases the encoding -/
lemma encode_increase_write_true_over_false (cfg : Cfg Bool Λ)
    (h_false : cfg.tape.nth 0 = false) :
    cfg.tape.encode < (cfg.tape.write true).encode := by
  exact encode_strict_increase_write_true cfg.tape cfg.tape.head_nonpos h_false

end BinaryStepSequences

end LeftTM0