import TMTapeToNumber.LeftTM0.Encoding

namespace LeftTM0

variable {Λ : Type*} [Inhabited Λ]

/-- Generate sequence by running machine and encoding each step -/
noncomputable def sequence (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) : ℕ → ℕ :=
  fun n ↦ encode_config (steps M n init_cfg)

/-- Generate sequence with bounded execution (halt after max_steps) -/
noncomputable def sequence_bounded (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) 
    (max_steps : ℕ) : ℕ → ℕ :=
  fun n ↦ 
    if n ≤ max_steps then
      encode_config (steps M n init_cfg)
    else
      encode_config (steps_until_halt M max_steps init_cfg)

/-- Get the value at step 0 (initial configuration) -/
noncomputable def sequence_initial (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) : ℕ :=
  sequence M init_cfg 0

/-- Check if sequence reaches a fixed point (machine halts) -/
def sequence_stabilizes (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (n : ℕ) : Prop :=
  ∀ m ≥ n, sequence M init_cfg m = sequence M init_cfg n

/-- Find first step where sequence stabilizes, if any -/
noncomputable def first_stable_step (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (max_search : ℕ) : Option ℕ :=
  let rec search (k : ℕ) : Option ℕ :=
    if k ≥ max_search then none
    else if sequence M init_cfg k = sequence M init_cfg (k + 1) then some k
    else search (k + 1)
  search 0

-- Properties of sequences
theorem sequence_zero (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) :
    sequence M init_cfg 0 = encode_config init_cfg := rfl

theorem sequence_step_relation (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (n : ℕ) :
    sequence M init_cfg (n + 1) = encode_config (step_or_stay M (steps M n init_cfg)) := by
  unfold sequence steps
  simp [Function.iterate_succ_apply']

theorem sequence_monotone_steps (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (n m : ℕ) :
    steps M n init_cfg = steps M m init_cfg → 
    ∀ k ≥ max n m, sequence M init_cfg k = sequence M init_cfg (max n m) := by sorry

theorem sequence_bounded_growth (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ) :
    sequence M init_cfg t ≤ 2^(t + Int.natAbs (leftmost_true_pos init_cfg)) := by sorry

theorem sequence_step_difference_bound (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ) :
    ∃ k : ℕ, |Int.ofNat (sequence M init_cfg (t+1)) - Int.ofNat (sequence M init_cfg t)| ≤ 2^k := by
  sorry

/-- A sequence is eventually constant if the machine halts -/
theorem sequence_eventually_constant_if_halts (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) :
    (∃ n, is_terminal M (steps M n init_cfg)) →
    ∃ N val, ∀ n ≥ N, sequence M init_cfg n = val := by sorry

end LeftTM0