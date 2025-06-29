import TMTapeToNumber.LeftwardSequences.Basic
import Mathlib.Data.Nat.Log

namespace LeftTM0

open LeftTM0.Theorems

variable {Λ : Type*} [Inhabited Λ]

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


/-- The head position after k steps is bounded by initial position minus k -/
lemma head_pos_bound (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (k : ℕ) :
    (steps M k init_cfg).tape.head_pos ≥ init_cfg.tape.head_pos - k := by
  induction k with
  | zero =>
    simp only [steps, Function.iterate_zero]
    simp
  | succ k' ih =>
    simp only [steps, Function.iterate_succ_apply']
    -- After one more step from (steps M k' init_cfg)
    have h_one_step : (step_or_stay M (steps M k' init_cfg)).tape.head_pos ≥
                     (steps M k' init_cfg).tape.head_pos - 1 := by
      -- A single step can move left by at most 1
      simp only [step_or_stay]
      split
      · -- step returns none, config unchanged
        simp
      · -- step returns some cfg'
        rename_i cfg' h_step_some
        -- Analyze what step does
        simp only [step] at h_step_some
        split_ifs at h_step_some with h_constraint
        · -- step_preserves_constraint was true
          match h_machine : M (steps M k' init_cfg).q (steps M k' init_cfg).tape.read with
          | none => simp [h_machine] at h_step_some
          | some (q', stmt) =>
            simp [h_machine] at h_step_some
            rw [← h_step_some]
            cases stmt with
            | move dir =>
              cases dir with
              | left =>
                -- Moving left decreases head_pos by 1
                simp only [step.apply_stmt, LeftwardTape.move_left]
                linarith
              | right =>
                -- Moving right increases head_pos by 1 (or stays same)
                simp only [step.apply_stmt, LeftwardTape.move_right]
                split_ifs
                · -- Can move right
                  linarith
                · -- Cannot move right, position unchanged
                  linarith
            | write a =>
              -- Writing doesn't change head position
              simp only [step.apply_stmt, LeftwardTape.write]
              linarith
    calc (step_or_stay M (steps M k' init_cfg)).tape.head_pos
      ≥ (steps M k' init_cfg).tape.head_pos - 1 := h_one_step
      _ ≥ init_cfg.tape.head_pos - k' - 1 := by linarith [ih]
      _ = init_cfg.tape.head_pos - (k' + 1) := by ring

/-- Writing to a tape preserves nth at non-zero positions -/
lemma tape_write_preserves_nth {Γ : Type*} [Inhabited Γ] (tape : Turing.Tape Γ) (a : Γ) (n : ℤ) (h : n ≠ 0) :
    (tape.write a).nth n = tape.nth n := by
  -- By definition, tape.write only changes the head (position 0)
  cases n with
  | ofNat k =>
    cases k with
    | zero => contradiction
    | succ k' => rfl
  | negSucc k => rfl

/-- When there are no initial true positions, the sequence is bounded by 2^(t+1) -/
theorem sequence_bounded_growth_none (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ)
    (h_none : leftmost_true_pos init_cfg = none)
    (h_init_head : init_cfg.tape.head_pos = 0) :
    sequence M init_cfg t < 2^(t+1) := by
  -- No initial true positions, so all positions ≤ 0 are false initially
  -- After t steps, leftmost true can be at most at position -t
  unfold sequence
  -- Apply encode_bound_by_leftmost with n = t
  have h_bound : sequence M init_cfg t < 2^t.succ := by
    apply encode_bound_by_leftmost
    intro i hi
    -- When leftmost_true_pos is none, there are no true positions initially
    -- First, establish that all positions ≤ 0 are false initially
    have h_init_all_false : ∀ j ≤ 0, init_cfg.tape.nth_absolute j = false := by
      intro j hj
      by_contra h_not_false
      -- If j were true, then leftmost_true_pos would find it
      push_neg at h_not_false
      have h_j_true : init_cfg.tape.nth_absolute j = true := by
        cases h : init_cfg.tape.nth_absolute j with
        | true => rfl
        | false => exact absurd h h_not_false
      -- j would be in true_positions_absolute
      have h_j_in : j ∈ init_cfg.tape.true_positions_absolute := by
        simp only [LeftwardTape.true_positions_absolute, Finset.mem_filter]
        refine ⟨?_, hj, h_j_true⟩
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf, LeftwardTape.has_content_at_absolute]
        rw [h_j_true]
        simp
      -- This means true_positions_absolute is non-empty
      have h_nonempty : init_cfg.tape.true_positions_absolute ≠ ∅ := by
        intro h_empty
        rw [h_empty] at h_j_in
        simp at h_j_in
      -- So minimum exists, contradicting leftmost_true_pos = none
      have : ∃ x, leftmost_true_pos init_cfg = some x := by
        simp only [leftmost_true_pos]
        -- Since true_positions_absolute is non-empty, its minimum exists
        have h_list_nonempty : init_cfg.tape.true_positions_absolute.toList ≠ [] := by
          intro h_empty
          have : init_cfg.tape.true_positions_absolute = ∅ := by
            ext x
            simp only [Finset.notMem_empty, iff_false]
            intro hx
            have : x ∈ init_cfg.tape.true_positions_absolute.toList := by
              exact Finset.mem_toList.mpr hx
            rw [h_empty] at this
            simp at this
          exact h_nonempty this
        -- For a non-empty list of integers, minimum is some value
        cases h_min : init_cfg.tape.true_positions_absolute.toList.minimum with
        | top =>
          -- If minimum is ⊤, list must be empty
          -- But we know the list is non-empty, contradiction
          exfalso
          -- When List.minimum returns ⊤, the list is empty
          have h_empty : init_cfg.tape.true_positions_absolute.toList = [] := by
            exact List.minimum_eq_top.mp h_min
          exact absurd h_empty h_list_nonempty
        | coe x =>
          -- minimum is ↑x, so match returns some x
          use x
      obtain ⟨x, hx⟩ := this
      rw [hx] at h_none
      cases h_none

    -- Now we know all positions ≤ 0 are initially false
    -- Since i < -t and t ≥ 0, we have i ≤ 0
    have hi_le : i ≤ 0 := by linarith
    have h_init_i_false : init_cfg.tape.nth_absolute i = false := h_init_all_false i hi_le

    -- The key claim: position i remains unchanged after t steps
    -- This is because the head cannot reach position i in t steps
    have h_unchanged : (steps M t init_cfg).tape.nth_absolute i = init_cfg.tape.nth_absolute i := by
      -- We'll prove this by induction on t
      clear h_init_all_false hi_le h_init_i_false
      induction t with
      | zero =>
        -- Base case: after 0 steps, nothing changes
        simp only [steps, Function.iterate_zero]
        -- Goal: (id init_cfg).tape.nth_absolute i = init_cfg.tape.nth_absolute i
        rfl
      | succ t' ih =>
        -- Inductive case: if unchanged after t' steps, still unchanged after t'+1 steps
        simp only [steps, Function.iterate_succ_apply']
        -- By IH: (steps M t' init_cfg).tape.nth_absolute i = init_cfg.tape.nth_absolute i
        have ih' : (steps M t' init_cfg).tape.nth_absolute i = init_cfg.tape.nth_absolute i := by
          apply ih
          -- i < -(t'+1) implies i < -t'
          -- We have: i < -↑(t' + 1) = -(↑t' + 1)
          -- We need: i < -↑t'
          have : -(↑(t' + 1) : ℤ) = -(↑t' + 1 : ℤ) := by simp
          rw [this] at hi
          linarith
        -- Now show: (step_or_stay M (steps M t' init_cfg)).tape.nth_absolute i = init_cfg.tape.nth_absolute i
        rw [← ih']
        -- It suffices to show: (step_or_stay M (steps M t' init_cfg)).tape.nth_absolute i = (steps M t' init_cfg).tape.nth_absolute i

        -- step_or_stay either returns the same config or takes a step
        simp only [step_or_stay]
        split
        · -- step returns none, config unchanged
          rfl
        · -- step returns some cfg'
          rename_i cfg' h_step
          -- We need to show cfg'.tape.nth_absolute i = (steps M t' init_cfg).tape.nth_absolute i

          -- Key insight: a step only modifies the position where the head is
          -- We need to show i ≠ (steps M t' init_cfg).tape.head_pos
          have h_not_at_head : i ≠ (steps M t' init_cfg).tape.head_pos := by
            -- We know: i < -(t'+1) = -(t' + 1)
            -- We'll show: (steps M t' init_cfg).tape.head_pos ≥ -t'
            -- Therefore: i < -(t' + 1) < -t' ≤ head_pos, so i ≠ head_pos
            have h_head_bound : (steps M t' init_cfg).tape.head_pos ≥ -(↑t' : ℤ) := by
              -- Use our head position bound lemma
              have h := head_pos_bound M init_cfg t'
              -- We have: (steps M t' init_cfg).tape.head_pos ≥ init_cfg.tape.head_pos - t'
              -- Since init_cfg.tape.head_pos = 0, we get:
              -- (steps M t' init_cfg).tape.head_pos ≥ 0 - t' = -t'
              rw [h_init_head] at h
              -- h : (steps M t' init_cfg).tape.head_pos ≥ 0 - ↑t'
              -- We need to show: (steps M t' init_cfg).tape.head_pos ≥ -↑t'
              convert h using 1
              simp
            -- Now: i < -(t'+1) and head_pos ≥ -t'
            -- We need to show i ≠ head_pos
            intro h_eq
            -- If i = head_pos, then head_pos < -(t'+1) and head_pos ≥ -t'
            -- But -(t'+1) = -(t' + 1) < -t', contradiction
            have h1 : i < -(↑(t' + 1) : ℤ) := hi
            have h2 : -(↑(t' + 1) : ℤ) = -(↑t' + 1 : ℤ) := by simp
            rw [h2] at h1
            have h3 : -(↑t' + 1 : ℤ) < -(↑t' : ℤ) := by linarith
            rw [h_eq] at h1
            linarith

          -- Now use that step preserves positions away from head
          have h_step_preserves : cfg'.tape.nth_absolute i = (steps M t' init_cfg).tape.nth_absolute i := by
            -- Analyze what step does
            -- Note: steps M t' init_cfg = (step_or_stay M)^[t'] init_cfg by definition
            have h_eq_cfg : steps M t' init_cfg = (step_or_stay M)^[t'] init_cfg := by
              simp only [steps]
            rw [← h_eq_cfg] at h_step

            simp only [step] at h_step
            split_ifs at h_step with h_constraint
            · -- step_preserves_constraint was true
              match h_machine : M (steps M t' init_cfg).q (steps M t' init_cfg).tape.read with
              | none =>
                rw [h_machine] at h_step
                simp at h_step
              | some (q', stmt) =>
                rw [h_machine] at h_step
                simp at h_step
                rw [← h_step]
                -- cfg' = ⟨q', apply_stmt stmt (steps M t' init_cfg).tape⟩
                cases stmt with
                | move dir =>
                  cases dir with
                  | left =>
                    -- Moving left preserves absolute positions
                    simp only [step.apply_stmt]
                    exact LeftwardTape.move_left_preserves_nth_absolute _ i
                  | right =>
                    -- Moving right preserves absolute positions
                    simp only [step.apply_stmt]
                    exact LeftwardTape.move_right_preserves_nth_absolute _ i
                | write a =>
                  -- Writing only affects the current head position
                  simp only [step.apply_stmt, LeftwardTape.write, LeftwardTape.nth_absolute]
                  -- write changes tape.nth 0 to a, which is tape.nth_absolute head_pos
                  -- For i ≠ head_pos, nth_absolute i is unchanged
                  -- We need to show: tape.write a.nth (i - head_pos) = tape.nth (i - head_pos)
                  -- where tape = (steps M t' init_cfg).tape.tape
                  have h_not_zero : i - (steps M t' init_cfg).tape.head_pos ≠ 0 := by
                    intro h_eq
                    have : i = (steps M t' init_cfg).tape.head_pos := by linarith
                    exact h_not_at_head this
                  -- Use our lemma about tape.write preserving nth at non-zero positions
                  exact tape_write_preserves_nth _ _ _ h_not_zero

          exact h_step_preserves

    rw [h_unchanged, h_init_i_false]
  exact h_bound

-- Forward Characterization: TM sequences are binary step sequences

/-- The difference in encoding when writing at a position is ±2^k where k is the absolute position -/
lemma encode_diff_at_write (cfg : Cfg Bool Λ) (cfg' : Cfg Bool Λ) 
    (h_step : ∃ a, cfg' = ⟨cfg.q, cfg.tape.write a⟩) :
    encode_config cfg' - encode_config cfg = 0 ∨
    ∃ k : ℕ, (encode_config cfg' : ℤ) - encode_config cfg = 2^k ∨ 
             (encode_config cfg' : ℤ) - encode_config cfg = -(2^k : ℤ) := by
  sorry

/-- One step of a TM changes the encoding by 0 or ±2^k -/
lemma sequence_diff_is_power_of_two (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ) :
    sequence_difference (sequence M init_cfg) t = 0 ∨
    ∃ k : ℕ, sequence_difference (sequence M init_cfg) t = 2^k ∨ 
             sequence_difference (sequence M init_cfg) t = -(2^k : ℤ) := by
  sorry

/-- The k value in a sequence change equals the absolute position where the write occurred -/
lemma sequence_k_equals_position (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ)
    (h_change : sequence M init_cfg (t + 1) ≠ sequence M init_cfg t) :
    ∃ k : ℕ, (sequence_difference (sequence M init_cfg) t = 2^k ∨ 
              sequence_difference (sequence M init_cfg) t = -(2^k : ℤ)) ∧
              k = Int.natAbs (-(steps M t init_cfg).tape.head_pos) := by
  sorry

/-- The k value is bounded by the step number -/
lemma sequence_k_bound (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ)
    (h_init : init_cfg.tape.head_pos = 0) :
    ∀ k : ℕ, (sequence_difference (sequence M init_cfg) t = 2^k ∨ 
               sequence_difference (sequence M init_cfg) t = -(2^k : ℤ)) →
    k ≤ t := by
  sorry

/-- Movement constraint between k values -/
lemma sequence_k_movement_constraint (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (i j : ℕ)
    (h_order : i < j)
    (h_i_change : sequence M init_cfg (i + 1) ≠ sequence M init_cfg i)
    (h_j_change : sequence M init_cfg (j + 1) ≠ sequence M init_cfg j) :
    ∃ k_i k_j : ℕ,
      (sequence_difference (sequence M init_cfg) i = 2^k_i ∨ 
       sequence_difference (sequence M init_cfg) i = -(2^k_i : ℤ)) ∧
      (sequence_difference (sequence M init_cfg) j = 2^k_j ∨ 
       sequence_difference (sequence M init_cfg) j = -(2^k_j : ℤ)) ∧
      (k_j : ℤ) - k_i ≤ j - i ∧ k_i - k_j ≤ j - i := by
  sorry

/-- Main theorem: Every TM-generated sequence is a binary step sequence -/
theorem tm_sequence_is_binary_step_sequence (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ)
    (h_init_empty : init_cfg = init [])
    (h_init_pos : init_cfg.tape.head_pos = 0) :
    is_binary_step_sequence (sequence M init_cfg) := by
  constructor
  · -- Condition 1: s_0 = 0
    simp only [sequence, sequence_zero]
    rw [h_init_empty]
    simp only [init, encode_config]
    exact encode_empty_tape
  constructor
  · -- Condition 2: differences are 0 or ±2^k
    exact sequence_diff_is_power_of_two M init_cfg
  · -- Condition 3: movement constraints
    intro t ht
    simp only [change_indices, Set.mem_setOf] at ht
    constructor
    · -- 3(a): k_t ≤ t
      obtain ⟨k, hk_def, hk_eq⟩ := sequence_k_equals_position M init_cfg t ht
      use k
      refine ⟨hk_def, ?_⟩
      rw [hk_eq]
      -- k = |head_pos| and head_pos ≥ -t, so k ≤ t
      have h_bound := head_pos_bound M init_cfg t
      rw [h_init_pos] at h_bound
      -- h_bound: (steps M t init_cfg).tape.head_pos ≥ -t
      -- So |head_pos| ≤ t
      have h_pos := (steps M t init_cfg).tape.head_nonpos
      -- head_pos ≤ 0 and head_pos ≥ -t, so -t ≤ head_pos ≤ 0
      -- Therefore |head_pos| = -head_pos ≤ t
      have : -(steps M t init_cfg).tape.head_pos ≤ t := by linarith
      -- Since head_pos ≤ 0, we have -head_pos ≥ 0
      have h_nonneg : 0 ≤ -(steps M t init_cfg).tape.head_pos := by linarith
      -- We need to show natAbs(-head_pos) ≤ t
      -- Since -head_pos ≥ 0, natAbs(-head_pos) = -head_pos as a natural number
      -- We have -head_pos ≤ t as integers, and both are non-negative
      -- So we can use omega to conclude
      omega
    · -- 3(b): movement constraint between indices
      intro i hi h_lt
      simp only [change_indices, Set.mem_setOf] at hi
      exact sequence_k_movement_constraint M init_cfg i t h_lt hi ht

-- Growth Bounds for Binary Step Sequences

/-- Main growth bound theorem: Any binary step sequence s satisfies s_t < 2^(t+1) -/
theorem binary_step_sequence_growth_bound (s : ℕ → ℕ) (h : is_binary_step_sequence s) :
    ∀ t : ℕ, s t < 2^(t + 1) := by
  sorry  -- Proof is complex, leaving as sorry for now

/-- Corollary: TM-generated sequences have the growth bound -/
theorem tm_sequence_growth_bound (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ)
    (h_init_empty : init_cfg = init [])
    (h_init_pos : init_cfg.tape.head_pos = 0) :
    ∀ t : ℕ, sequence M init_cfg t < 2^(t + 1) := by
  have h_bss := tm_sequence_is_binary_step_sequence M init_cfg h_init_empty h_init_pos
  exact binary_step_sequence_growth_bound _ h_bss

-- Finite Sequence Generation Theorem

/-- States for the universal finite sequence generator -/
inductive SeqGenState (n : ℕ)
  | state : Fin n → SeqGenState n
  | halt : SeqGenState n

instance {n : ℕ} : Inhabited (SeqGenState n) := ⟨SeqGenState.halt⟩

/-- Construct a Turing machine that generates a given finite binary step sequence -/
noncomputable def construct_tm_for_sequence (s : List ℕ) 
    (h : is_finite_binary_step_sequence s) : Machine Bool (SeqGenState s.length) :=
  sorry  -- Complex construction

/-- Main theorem: Every finite binary step sequence is TM-generable -/
theorem finite_binary_step_sequence_generable (s : List ℕ) 
    (h : is_finite_binary_step_sequence s) :
    ∃ (M : Machine Bool (SeqGenState s.length)) (init_cfg : Cfg Bool (SeqGenState s.length)),
      init_cfg = init [] ∧
      init_cfg.tape.head_pos = 0 ∧
      ∀ i hi, sequence M init_cfg i = s.get ⟨i, hi⟩ := by
  sorry  -- Proof uses construct_tm_for_sequence and shows correctness

end LeftTM0
