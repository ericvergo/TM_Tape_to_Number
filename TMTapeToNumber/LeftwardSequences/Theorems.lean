import TMTapeToNumber.LeftwardSequences.Basic

namespace LeftTM0

open LeftTM0.Theorems

variable {Λ : Type*} [Inhabited Λ]


theorem sequence_bounded_growth (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ) :
    match leftmost_true_pos init_cfg with
    | none => sequence M init_cfg t < 2^(t+1)
    | some pos => sequence M init_cfg t < 2^(t + Int.natAbs pos + 1) := by
  -- The key insight: after t steps, the leftmost true position can be at most
  -- t positions to the left of the initial leftmost position

  match h_leftmost : leftmost_true_pos init_cfg with
  | none =>
    -- No initial true positions, so all positions > 0 are false initially
    -- After t steps, leftmost true can be at most at position -t
    unfold sequence
    -- Apply encode_bound_by_leftmost with n = t
    have h_bound : sequence M init_cfg t < 2^t.succ := by
      apply encode_bound_by_leftmost
      intro i hi
      -- Need to show: (steps M t init_cfg).tape.nth_absolute i = false for all i < -t
      -- This is the key insight about tape evolution that needs to be proven
      -- The argument is:
      -- 1. leftmost_true_pos init_cfg = none means all positions initially have false
      -- 2. The head starts at position ≤ 0 (from LeftwardTape constraint)
      -- 3. In t steps, head can move at most t positions left, so final position ≥ -t
      -- 4. Machine can only write to current head position
      -- 5. Therefore positions < -t are never written and remain false

      -- The key insight: positions < -t are unreachable in t steps
      -- This is because:
      -- 1. Head starts at position ≤ 0
      -- 2. Head can move at most 1 position left per step
      -- 3. So after t steps, head position ≥ -t
      -- 4. Positions < -t cannot be written to
      -- 5. Since leftmost_true_pos = none, all positions were initially false
      -- 6. Therefore positions < -t remain false
      sorry
    -- h_bound gives exactly what we need: sequence M init_cfg t < 2^(t+1)
    exact h_bound

  | some pos =>
    -- Initial leftmost true is at position pos (which is ≤ 0)
    -- After t steps, leftmost true can be at most at position pos - t
    unfold sequence
    -- Apply encode_bound_by_leftmost with n = t + |pos|
    have h_bound : sequence M init_cfg t < 2^(t + Int.natAbs pos).succ := by
      apply encode_bound_by_leftmost
      intro i hi
      -- Need to show: (steps M t init_cfg).tape.nth_absolute i = false
      -- for all i < -(t + |pos|)
      -- The argument is:
      -- 1. pos is the leftmost true position initially, so all positions < pos are false
      -- 2. The head starts at position ≤ 0 and can move at most t positions left in t steps
      -- 3. So the leftmost reachable position is at most pos - t = -(|pos| + t) (since pos ≤ 0)
      -- 4. Positions < -(t + |pos|) are never reached and remain false

      -- The key insight: positions < -(t + |pos|) remain false
      -- This is because:
      -- 1. pos ≤ 0 is the leftmost true position initially
      -- 2. All positions < pos are initially false
      -- 3. Head can move at most t positions left in t steps
      -- 4. Since |pos| = -pos (as pos ≤ 0), we have -(t + |pos|) = pos - t
      -- 5. Positions < pos - t are never reached and remain false
      sorry
    -- h_bound: sequence M init_cfg t < 2^((t + |pos|) + 1)
    -- This is exactly what we need!
    simp only [Nat.succ_eq_add_one] at h_bound
    exact h_bound

theorem sequence_step_difference_bound (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ) :
    ∃ k : ℕ, |Int.ofNat (sequence M init_cfg (t+1)) - Int.ofNat (sequence M init_cfg t)| ≤ 2^k := by
  -- The difference between consecutive sequence values comes from a single TM step
  unfold sequence
  -- sequence M init_cfg (t+1) = encode_config (steps M (t+1) init_cfg)
  -- sequence M init_cfg t = encode_config (steps M t init_cfg)

  -- steps M (t+1) init_cfg = step_or_stay M (steps M t init_cfg)
  rw [steps_succ]

  -- Now we need to bound |encode_config (step_or_stay M cfg_t) - encode_config cfg_t|
  -- where cfg_t = steps M t init_cfg
  let cfg_t := steps M t init_cfg

  -- Case analysis on whether the machine halts at cfg_t
  by_cases h_halt : is_terminal M cfg_t
  · -- Machine has halted, so step_or_stay returns cfg_t unchanged
    unfold is_terminal at h_halt
    simp only [step_or_stay, h_halt, cfg_t]
    -- The goal becomes |encode_config cfg_t - encode_config cfg_t| ≤ 1
    use 0
    simp

  · -- Machine hasn't halted, so step produces a new configuration
    unfold is_terminal at h_halt
    push_neg at h_halt
    -- h_halt : step M cfg_t ≠ none, so ∃ cfg', step M cfg_t = some cfg'
    -- Since the machine doesn't halt, step produces some configuration
    cases h_step_eq : step M cfg_t with
    | none => exact absurd h_step_eq h_halt
    | some cfg' =>
      -- Now we have step M cfg_t = some cfg'
      have h_eq : step_or_stay M cfg_t = cfg' := by
        simp only [step_or_stay, h_step_eq]

      -- Substitute cfg_t and use h_eq
      simp only [cfg_t, h_eq]

      -- Now apply encode_step_diff
      have h_diff := encode_step_diff M cfg_t cfg' h_step_eq
      obtain ⟨k, hk⟩ := h_diff
      use k

/-- A sequence is eventually constant if the machine halts -/
theorem sequence_eventually_constant_if_halts (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) :
    (∃ n, is_terminal M (steps M n init_cfg)) →
    ∃ N val, ∀ n ≥ N, sequence M init_cfg n = val := by
  intro ⟨n, h_terminal⟩
  -- If the machine halts at step n, then the configuration is fixed from that point
  use n, sequence M init_cfg n
  intro m h_m

  -- We need to show: sequence M init_cfg m = sequence M init_cfg n
  unfold sequence
  congr 1

  -- Show: steps M m init_cfg = steps M n init_cfg
  -- Since the machine halted at step n, all future steps give the same config
  have h_fixed : ∀ k ≥ n, steps M k init_cfg = steps M n init_cfg := by
    intro k h_k
    -- Prove by induction on k - n
    have h_diff : ∃ d, k = n + d := by
      use k - n
      omega
    obtain ⟨d, hd⟩ := h_diff
    rw [hd]
    clear hd h_k
    -- Prove by induction on d
    induction d with
    | zero =>
      simp
    | succ d' ih =>
      rw [Nat.add_succ]
      simp only [steps]
      rw [Function.iterate_succ_apply']
      -- By IH, steps M (n + d') init_cfg = steps M n init_cfg
      have h_eq : (step_or_stay M)^[n + d'] init_cfg = (step_or_stay M)^[n] init_cfg := ih
      rw [h_eq]
      -- Since steps M n init_cfg is terminal, step_or_stay leaves it unchanged
      -- We need to show: step_or_stay M ((step_or_stay M)^[n] init_cfg) = (step_or_stay M)^[n] init_cfg
      have h_terminal' : is_terminal M ((step_or_stay M)^[n] init_cfg) := by
        exact h_terminal
      -- By definition of is_terminal and step_or_stay
      simp only [is_terminal] at h_terminal'
      simp only [step_or_stay, h_terminal']

  exact h_fixed m h_m

end LeftTM0
