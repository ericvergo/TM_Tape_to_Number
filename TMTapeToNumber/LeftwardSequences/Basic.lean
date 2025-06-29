import TMTapeToNumber.LeftwardEncoding.Basic
import TMTapeToNumber.LeftwardEncoding.Properties

namespace LeftTM0

open LeftTM0.Theorems

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

-- Helper lemma for steps
theorem steps_succ (M : Machine Bool Λ) (n : ℕ) (init_cfg : Cfg Bool Λ) :
    steps M (n + 1) init_cfg = step_or_stay M (steps M n init_cfg) := by
  unfold steps
  simp [Function.iterate_succ_apply']


end LeftTM0
