import TMTapeToNumber.Sequences
import TMTapeToNumber.Theorems.EncodingProperties

namespace TMTapeToNumber.Theorems

open TMTapeToNumber Turing TM0

variable {Λ : Type*} [Inhabited Λ]

/-- If a machine never writes true, the sequence is constantly 0 -/
theorem sequence_const_zero (M : Machine Bool Λ) (init : Cfg Bool Λ)
    (h_init : ∀ i, init.Tape.nth i = false)
    (h_never_writes : ∀ q a, M q a = none ∨
      ∃ q' stmt, M q a = some (q', stmt) ∧
        (∀ b, stmt ≠ Stmt.write b ∨ b = false)) :
    ∀ n, sequence M init n = 0 := by
  intro n
  -- By induction, the tape remains all false
  sorry

/-- Sequence values are determined by tape content, not head position -/
theorem sequence_independent_of_head (M : Machine Bool Λ)
    (cfg₁ cfg₂ : Cfg Bool Λ)
    (h_same_state : cfg₁.q = cfg₂.q)
    (h_same_tape : ∀ i, cfg₁.Tape.nth i = cfg₂.Tape.nth i) :
    sequence M cfg₁ = sequence M cfg₂ := by
  ext n
  simp [sequence]
  -- The configurations evolve identically since they have same state and tape content
  sorry

/-- If the machine halts, the sequence eventually becomes constant -/
theorem sequence_eventually_const (M : Machine Bool Λ) (init : Cfg Bool Λ) :
    (∃ n, ((step_or_stay M)^[n] init).q = default) →
    ∃ n₀, ∀ m ≥ n₀, sequence M init m = sequence M init n₀ := by
  intro ⟨n, h_halt⟩
  use n
  exact sequence_const_after_halt M init n h_halt

/-- Sequences from machines with finite support remain bounded -/
theorem sequence_bounded_support (M : Machine Bool Λ) (init : Cfg Bool Λ)
    (h_init : has_finite_support init.Tape)
    (h_preserves : ∀ cfg, has_finite_support cfg.Tape →
      match step M cfg with
      | none => true
      | some cfg' => has_finite_support cfg'.Tape) :
    ∀ n, has_finite_support ((step_or_stay M)^[n] init).Tape := by
  intro n
  induction n with
  | zero => simp; exact h_init
  | succ n ih =>
    simp [Function.iterate_succ]
    sorry

/-- Deterministic evolution of sequences -/
theorem sequence_deterministic (M : Machine Bool Λ) (init : Cfg Bool Λ) :
    ∀ n, sequence M init (n + 1) =
      encode_tape ((step_or_stay M)^[n + 1] init).Tape := by
  intro n
  rfl

/-- Sequence growth is bounded by machine behavior -/
theorem sequence_growth_bound (M : Machine Bool Λ) (init : Cfg Bool Λ)
    (h_support : ∀ n, has_finite_support ((step_or_stay M)^[n] init).Tape)
    (h_bound : ∃ k, ∀ n cfg, cfg = (step_or_stay M)^[n] init →
      ∀ i, cfg.Tape.nth i ≠ default → Int.natAbs i ≤ k) :
    ∃ c, ∀ n, sequence M init n ≤ c * 2^n := by
  -- The encoding can grow at most exponentially due to position bounds
  sorry

/-- Sequences preserve certain algebraic properties -/
theorem sequence_preserves_parity (M : Machine Bool Λ) (init : Cfg Bool Λ)
    (h_parity : ∀ q a, M q a = none ∨
      ∃ q' stmt, M q a = some (q', stmt) ∧
        match stmt with
        | Stmt.write b => b = init.Tape.head
        | _ => true) :
    ∀ n, sequence M init n % 2 = encode_tape init.Tape % 2 := by
  -- If the machine preserves tape parity, so does the sequence
  sorry

/-- Monotonicity for certain machine types -/
theorem sequence_monotone_for_additive_machines (M : Machine Bool Λ) (init : Cfg Bool Λ)
    (h_additive : ∀ cfg, match step M cfg with
      | none => true
      | some cfg' => cfg' = cfg ∨
        ∃ pos, cfg'.Tape.nth pos = true ∧ cfg.Tape.nth pos = false ∧
          ∀ i ≠ pos, cfg'.Tape.nth i = cfg.Tape.nth i) :
    ∀ n m, n ≤ m → sequence M init n ≤ sequence M init m := by
  -- Machines that only add true bits produce monotone sequences
  sorry

end TMTapeToNumber.Theorems
