import TMTapeToNumber.LeftTM0.LeftwardSequences
import TMTapeToNumber.LeftTM0.Theorems.EncodingProperties
import Mathlib.Computability.TuringMachine

namespace LeftTM0.Theorems

open LeftTM0 

variable {Λ : Type*} [Inhabited Λ]

/-- If a machine never writes true, the sequence is constantly 0 -/
theorem sequence_const_zero (M : Machine Bool Λ) (init : Cfg Bool Λ)
    (h_init : ∀ i ≤ 0, init.tape.nth_absolute i = false)
    (h_never_writes : ∀ q a, M q a = none ∨
      ∃ q' stmt, M q a = some (q', stmt) ∧
        (∀ b, stmt ≠ Turing.TM0.Stmt.write b ∨ b = false)) :
    ∀ n, sequence M init n = 0 := by
  sorry

/-- Sequence values are determined by tape content -/
theorem sequence_tape_content (M : Machine Bool Λ)
    (cfg₁ cfg₂ : Cfg Bool Λ)
    (h_same_state : cfg₁.q = cfg₂.q)
    (h_same_tape : ∀ i ≤ 0, cfg₁.tape.nth_absolute i = cfg₂.tape.nth_absolute i) :
    sequence M cfg₁ = sequence M cfg₂ := by
  sorry

/-- If the machine halts, the sequence eventually becomes constant -/
theorem sequence_eventually_const (M : Machine Bool Λ) (init : Cfg Bool Λ) :
    (∃ n, is_terminal M (steps M n init)) →
    ∃ n₀, ∀ m ≥ n₀, sequence M init m = sequence M init n₀ := by
  sorry

/-- Sequences preserve position constraint -/
theorem sequence_respects_constraint (M : Machine Bool Λ) (init : Cfg Bool Λ) :
    ∀ n, (steps M n init).tape.head_pos ≤ 0 := by
  sorry

/-- Single step can change encoding by at most adding/removing a power of 2 -/
theorem sequence_step_diff (M : Machine Bool Λ) (init : Cfg Bool Λ) (n : ℕ) :
    ∃ k : ℕ, |Int.ofNat (sequence M init (n+1)) - Int.ofNat (sequence M init n)| ≤ 2^k := by
  sorry

/-- Monotonicity for machines that only add true values -/
theorem sequence_monotone_for_additive_machines (M : Machine Bool Λ) (init : Cfg Bool Λ)
    (h_additive : ∀ cfg, match step M cfg with
      | none => true
      | some cfg' => 
        ∀ i ≤ 0, cfg.tape.nth_absolute i = true → cfg'.tape.nth_absolute i = true) :
    ∀ n m, n ≤ m → sequence M init n ≤ sequence M init m := by
  sorry

/-- Bound on sequence growth -/
theorem sequence_growth_bound (M : Machine Bool Λ) (init : Cfg Bool Λ)
    (h_bounded_movement : ∃ k, ∀ n, (steps M n init).tape.head_pos ≥ -k) :
    ∃ c, ∀ n, sequence M init n ≤ c * 2^n := by
  sorry

/-- Sequences from deterministic evolution -/
theorem sequence_deterministic (M : Machine Bool Λ) (init : Cfg Bool Λ) :
    ∀ n, sequence M init (n + 1) = encode_config (step_or_stay M (steps M n init)) := by
  sorry

/-- Sequence stability after halt -/
theorem sequence_stable_after_halt (M : Machine Bool Λ) (init : Cfg Bool Λ) (n : ℕ) :
    is_terminal M (steps M n init) →
    ∀ m ≥ n, sequence M init m = sequence M init n := by
  sorry

/-- Sequence values are bounded by tape support -/
theorem sequence_bounded_by_support (M : Machine Bool Λ) (init : Cfg Bool Λ) :
    (∀ n i, i < -((n : ℕ) : ℤ) → (steps M n init).tape.nth_absolute i = false) →
    ∀ n, sequence M init n < 2^(n + 1) := by
  sorry

end LeftTM0.Theorems