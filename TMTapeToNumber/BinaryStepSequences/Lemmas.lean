import TMTapeToNumber.BinaryStepSequences.Basic
import TMTapeToNumber.LeftwardSequences.Theorems
import TMTapeToNumber.LeftTM0.LeftwardTape
import TMTapeToNumber.LeftTM0.Step
import TMTapeToNumber.LeftwardEncoding.Properties
import Mathlib.Data.Nat.Log

set_option linter.unusedSectionVars false

namespace LeftTM0

open LeftTM0.Theorems
open Turing

variable {Λ : Type*} [Inhabited Λ]

-- Helper lemmas for encode_diff_at_write

open LeftwardTape

-- Forward Characterization: TM sequences are binary step sequences

/-- The difference in encoding when writing at a position is ±2^k where k is the absolute position -/
lemma encode_diff_at_write (cfg : Cfg Bool Λ) (cfg' : Cfg Bool Λ)
    (h_step : ∃ a, cfg' = ⟨cfg.q, cfg.tape.write a⟩) :
    encode_config cfg' - encode_config cfg = 0 ∨
    ∃ k : ℕ, (encode_config cfg' : ℤ) - encode_config cfg = 2^k ∨
             (encode_config cfg' : ℤ) - encode_config cfg = -(2^k : ℤ) := by
  -- Extract the value being written
  obtain ⟨a, h_cfg'⟩ := h_step
  rw [h_cfg']
  unfold encode_config

  -- The encoding is a sum over positions with true values
  -- Writing at the head position either:
  -- 1. Changes false to true (adds 2^k)
  -- 2. Changes true to false (subtracts 2^k)
  -- 3. Writes the same value (no change)
  -- where k = |head_pos|

  -- The key insight: write only changes the value at the head position
  -- Let's analyze the encoding change

  -- Get the current value at the head position
  let current_val := cfg.tape.nth 0  -- 0 is relative position of head

  -- The encoding sums over all positions with true values
  -- Writing at head position (absolute position cfg.tape.head_pos) changes only that bit

  -- Case analysis on the current and new values
  by_cases h_current : current_val = true
  · -- Current value is true
    by_cases h_new : a = true
    · -- Writing true over true: no change
      left
      -- Show encoding doesn't change
      -- Show the encoding difference is 0
      simp only [h_cfg']
      have h_read : cfg.tape.tape.nth 0 = current_val := rfl
      rw [h_current] at h_read
      -- h_read : cfg.tape.tape.nth 0 = true
      -- We're writing a = true (from h_new)
      -- So the tape doesn't change
      have h_write_eq : cfg.tape.tape.write a = cfg.tape.tape := by
        rw [h_new]  -- Now we need to show cfg.tape.tape.write true = cfg.tape.tape
        apply Turing.Tape.ext
        intro i
        by_cases h_pos : i = 0
        · -- At position 0, we're writing true where there's already true
          rw [h_pos, Turing.Tape.write_nth]
          simp
          exact h_read
        · -- At other positions, write doesn't change the value
          rw [Turing.Tape.write_nth]
          simp [h_pos]
      simp only [encode_config, LeftwardTape.write]
      rw [h_write_eq]
      simp
    · -- Writing false over true: removes 2^k
      right
      use Int.natAbs (-cfg.tape.head_pos)
      right
      -- The encoding decreases by 2^|head_pos|
      have h_a_false : a = false := by
        cases a with
        | false => rfl
        | true =>
          -- If a = true, then h_new says ¬a = true, i.e., ¬true = true
          -- This is False
          exfalso
          exact h_new rfl

      -- The key insight: encoding sums 2^|pos| for all positions ≤ 0 with true
      -- Writing false at head position removes that contribution

      -- Unfold the encoding definitions
      simp only [encode_config, LeftwardTape.encode, LeftwardTape.write]

      -- The encoding changes by removing the contribution from the head position
      -- First, let's establish that the head is at absolute position cfg.tape.head_pos
      -- and since head_pos ≤ 0, we have |head_pos| = -head_pos

      -- The new tape has false at head position, old tape has true
      -- So true_positions_absolute of new tape = old tape's true_positions \ {cfg.tape.head_pos}

      -- Need to show the difference is -2^(-cfg.tape.head_pos)
      have h_head_pos_nonpos : cfg.tape.head_pos ≤ 0 := cfg.tape.head_nonpos

      -- The key insight: writing false at position 0 (relative) removes cfg.tape.head_pos from true_positions
      -- because nth_absolute cfg.tape.head_pos = nth 0 = current_val = true (old)
      -- and after writing false, nth_absolute cfg.tape.head_pos = false (new)

      -- Step 1: The old tape has true at absolute position cfg.tape.head_pos
      have h_old_true : cfg.tape.nth_absolute cfg.tape.head_pos = true := by
        simp only [nth_absolute, sub_self]
        -- nth_absolute head_pos = nth (head_pos - head_pos) = nth 0
        -- and current_val = cfg.tape.nth 0 = true
        exact h_current

      -- Step 2: The new tape has false at absolute position cfg.tape.head_pos
      have h_new_false : (cfg.tape.write a).nth_absolute cfg.tape.head_pos = false := by
        simp only [nth_absolute, write, sub_self]
        rw [Turing.Tape.write_nth]
        simp only [if_pos rfl]
        exact h_a_false

      -- Step 3: Other positions are unchanged by write
      have h_unchanged : ∀ i ≠ cfg.tape.head_pos,
        (cfg.tape.write a).nth_absolute i = cfg.tape.nth_absolute i := by
        intro i hi
        simp only [nth_absolute, write]
        rw [Turing.Tape.write_nth]
        split_ifs with h
        · -- If i - head_pos = 0, then i = head_pos, contradiction
          have : i = cfg.tape.head_pos := by linarith
          contradiction
        · rfl

      -- Step 4: Show that true_positions differ only at cfg.tape.head_pos
      have h_diff : (cfg.tape.write a).true_positions_absolute =
                    cfg.tape.true_positions_absolute \ {cfg.tape.head_pos} := by
        ext i
        simp only [true_positions_absolute, Finset.mem_filter, Set.Finite.mem_toFinset,
                   Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · intro ⟨hi_mem, hi_le, hi_true⟩
          constructor
          · -- Show i ∈ cfg.tape.true_positions_absolute
            refine ⟨?_, hi_le, ?_⟩
            · simp only [Set.mem_setOf, has_content_at_absolute]
              by_cases h : i = cfg.tape.head_pos
              · rw [h, h_old_true]
                trivial
              · rw [← h_unchanged i h]
                simp only [has_content_at_absolute] at hi_mem
                exact hi_mem
            · by_cases h : i = cfg.tape.head_pos
              · rw [h] at hi_true
                rw [h_new_false] at hi_true
                simp at hi_true
              · rw [← h_unchanged i h]
                exact hi_true
          · -- Show i ≠ cfg.tape.head_pos
            intro h
            rw [h] at hi_true
            rw [h_new_false] at hi_true
            simp at hi_true
        · intro ⟨⟨hi_mem, hi_le, hi_true⟩, hi_neq⟩
          refine ⟨?_, hi_le, ?_⟩
          · simp only [Set.mem_setOf, has_content_at_absolute]
            rw [h_unchanged i hi_neq]
            simp only [has_content_at_absolute] at hi_mem
            exact hi_mem
          · rw [h_unchanged i hi_neq]
            exact hi_true

      -- Step 5: Calculate the encoding difference
      -- The encoding of the new tape structure
      have h_new_encode : (⟨Turing.Tape.write a cfg.tape.tape,
                           cfg.tape.head_pos,
                           cfg.tape.head_nonpos⟩ : LeftwardTape Bool).true_positions_absolute =
                          (cfg.tape.write a).true_positions_absolute := by
        -- Both are the same tape structure
        rfl

      -- Rewrite the goal using this equality
      rw [h_new_encode, h_diff]

      -- The sum over A \ {x} = sum over A - (if x ∈ A then 2^f(x) else 0)
      have h_in : cfg.tape.head_pos ∈ cfg.tape.true_positions_absolute := by
        simp only [true_positions_absolute, Finset.mem_filter, Set.Finite.mem_toFinset]
        refine ⟨?_, h_head_pos_nonpos, h_old_true⟩
        simp only [Set.mem_setOf, has_content_at_absolute, h_old_true]
        trivial

      -- Use the formula: sum(A) = sum(A\{x}) + sum({x}) when x ∈ A
      have h_sum_eq : (∑ i ∈ cfg.tape.true_positions_absolute, 2 ^ (-i).natAbs) =
                      (∑ i ∈ cfg.tape.true_positions_absolute \ {cfg.tape.head_pos}, 2 ^ (-i).natAbs) +
                      (∑ i ∈ ({cfg.tape.head_pos} : Finset ℤ), 2 ^ (-i).natAbs) := by
        rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr h_in)]

      rw [h_sum_eq]
      simp only [Finset.sum_singleton]
      -- Now we have: sum(A\{x}) - (sum(A\{x}) + 2^|x|) = -2^|x|
      -- Cast to integers for the arithmetic
      push_cast
      ring
  · -- Current value is false
    by_cases h_new : a = true
    · -- Writing true over false: adds 2^k
      right
      use Int.natAbs (-cfg.tape.head_pos)
      left
      -- The encoding increases by 2^|head_pos|
      -- The key insight: encoding sums 2^|pos| for all positions ≤ 0 with true
      -- Writing true at head position adds that contribution

      -- Similar to the previous case, but now we're adding instead of removing
      have h_current_false : current_val = false := by
        cases h_current_eq : current_val with
        | false => rfl
        | true =>
          -- In this case branch, current_val = true (from h_current_eq)
          -- But h_current says ¬current_val = true, i.e., ¬true = true
          -- This is a contradiction
          exfalso
          rw [h_current_eq] at h_current
          exact h_current rfl

      have h_a_true : a = true := by
        cases a with
        | false =>
          -- If a = false, then h_new : a = true says false = true
          -- This is impossible
          exact absurd h_new (Bool.false_ne_true)
        | true => rfl

      -- The old tape has false at head position, new tape has true
      have h_old_false : cfg.tape.nth_absolute cfg.tape.head_pos = false := by
        simp only [nth_absolute, sub_self]
        exact h_current_false

      have h_new_true : (cfg.tape.write a).nth_absolute cfg.tape.head_pos = true := by
        simp only [nth_absolute, write, sub_self]
        rw [Turing.Tape.write_nth]
        simp only [if_pos rfl]
        exact h_a_true

      -- Other positions unchanged (same as before)
      have h_unchanged : ∀ i ≠ cfg.tape.head_pos,
        (cfg.tape.write a).nth_absolute i = cfg.tape.nth_absolute i := by
        intro i hi
        simp only [nth_absolute, write]
        rw [Turing.Tape.write_nth]
        split_ifs with h
        · have : i = cfg.tape.head_pos := by linarith
          contradiction
        · rfl

      -- Show that true_positions differ only by adding cfg.tape.head_pos
      have h_diff : (cfg.tape.write a).true_positions_absolute =
                    cfg.tape.true_positions_absolute ∪ {cfg.tape.head_pos} := by
        ext i
        simp only [true_positions_absolute, Finset.mem_filter, Set.Finite.mem_toFinset,
                   Finset.mem_union, Finset.mem_singleton]
        constructor
        · intro ⟨hi_mem, hi_le, hi_true⟩
          by_cases h : i = cfg.tape.head_pos
          · right
            exact h
          · left
            refine ⟨?_, hi_le, ?_⟩
            · simp only [Set.mem_setOf, has_content_at_absolute]
              rw [← h_unchanged i h]
              simp only [has_content_at_absolute] at hi_mem
              exact hi_mem
            · -- We need to show cfg.tape.nth_absolute i = true
              -- We know (cfg.tape.write a).nth_absolute i = true
              -- and i ≠ cfg.tape.head_pos, so h_unchanged applies
              have : cfg.tape.nth_absolute i = (cfg.tape.write a).nth_absolute i := by
                rw [h_unchanged i h]
              rw [this]
              exact hi_true
        · intro hi
          cases hi with
          | inl hi_in =>
            obtain ⟨hi_mem, hi_le, hi_true⟩ := hi_in
            refine ⟨?_, hi_le, ?_⟩
            · simp only [Set.mem_setOf, has_content_at_absolute]
              rw [h_unchanged i ?_]
              · simp only [has_content_at_absolute] at hi_mem
                exact hi_mem
              · -- Need to show i ≠ cfg.tape.head_pos
                intro h_eq
                rw [h_eq] at hi_true
                rw [h_old_false] at hi_true
                simp at hi_true
            · rw [h_unchanged i ?_]
              · exact hi_true
              · intro h_eq
                rw [h_eq] at hi_true
                rw [h_old_false] at hi_true
                simp at hi_true
          | inr hi_eq =>
            rw [hi_eq]
            refine ⟨?_, cfg.tape.head_nonpos, h_new_true⟩
            simp only [Set.mem_setOf, has_content_at_absolute, h_new_true]
            trivial

      -- Calculate the encoding difference
      have h_new_encode : (⟨Turing.Tape.write a cfg.tape.tape,
                           cfg.tape.head_pos,
                           cfg.tape.head_nonpos⟩ : LeftwardTape Bool).true_positions_absolute =
                          (cfg.tape.write a).true_positions_absolute := by
        rfl

      -- First unfold the encoding
      simp only [encode_config, LeftwardTape.encode]
      -- Now we can use h_diff to rewrite the LHS
      rw [h_diff]

      -- Show head_pos is not in the old true_positions (since it has false)
      have h_not_in : cfg.tape.head_pos ∉ cfg.tape.true_positions_absolute := by
        simp only [true_positions_absolute, Finset.mem_filter, Set.Finite.mem_toFinset]
        push_neg
        intro _ _
        -- We need to show cfg.tape.nth_absolute cfg.tape.head_pos ≠ true
        -- We have h_old_false : cfg.tape.nth_absolute cfg.tape.head_pos = false
        rw [h_old_false]
        simp

      -- Use the formula: sum(A ∪ {x}) = sum(A) + sum({x}) when x ∉ A
      have h_sum_eq : (∑ i ∈ cfg.tape.true_positions_absolute ∪ {cfg.tape.head_pos}, 2 ^ (-i).natAbs) =
                      (∑ i ∈ cfg.tape.true_positions_absolute, 2 ^ (-i).natAbs) +
                      (∑ i ∈ ({cfg.tape.head_pos} : Finset ℤ), 2 ^ (-i).natAbs) := by
        rw [Finset.sum_union]
        exact Finset.disjoint_singleton_right.mpr h_not_in

      rw [h_sum_eq]
      simp only [Finset.sum_singleton]
      -- Now we have: (sum(A) + 2^|x|) - sum(A) = 2^|x|
      -- This is basic arithmetic: (a + b) - a = b
      push_cast
      ring
    · -- Writing false over false: no change
      left
      -- Show encoding doesn't change
      -- Show the encoding difference is 0
      simp only [h_cfg']
      have h_read : cfg.tape.tape.nth 0 = current_val := rfl
      -- h_current says current_val ≠ true, so current_val = false (for Bool)
      -- h_new says a ≠ true, so a = false
      have h_current_false : current_val = false := by
        cases h_current_eq : current_val with
        | false => rfl
        | true =>
          -- In this case branch, current_val = true (from h_current_eq)
          -- But h_current says ¬current_val = true, i.e., ¬true = true
          -- This is a contradiction
          exfalso
          rw [h_current_eq] at h_current
          exact h_current rfl
      have h_a_false : a = false := by
        cases a with
        | false => rfl
        | true =>
          -- If a = true, then h_new says ¬a = true, i.e., ¬true = true
          -- This is False
          exfalso
          exact h_new rfl
      rw [h_current_false] at h_read
      -- h_read : cfg.tape.tape.nth 0 = false
      -- We're writing a = false (from h_a_false)
      -- So the tape doesn't change
      have h_write_eq : cfg.tape.tape.write a = cfg.tape.tape := by
        rw [h_a_false]  -- Now we need to show cfg.tape.tape.write false = cfg.tape.tape
        apply Turing.Tape.ext
        intro i
        by_cases h_pos : i = 0
        · -- At position 0, we're writing false where there's already false
          rw [h_pos, Turing.Tape.write_nth]
          simp
          exact h_read
        · -- At other positions, write doesn't change the value
          rw [Turing.Tape.write_nth]
          simp [h_pos]
      simp only [encode_config, LeftwardTape.write]
      rw [h_write_eq]
      simp

/-- One step of a TM changes the encoding by 0 or ±2^k -/
lemma sequence_diff_is_power_of_two (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ) :
    sequence_difference (sequence M init_cfg) t = 0 ∨
    ∃ k : ℕ, sequence_difference (sequence M init_cfg) t = 2^k ∨
             sequence_difference (sequence M init_cfg) t = -(2^k : ℤ) := by
  unfold sequence_difference sequence
  -- sequence_difference s t = s(t+1) - s(t)
  -- = encode_config (steps M (t+1) init_cfg) - encode_config (steps M t init_cfg)

  -- The key insight: one step either moves (no encoding change) or writes (±2^k change)
  -- We need to analyze the transition at step t

  -- Use the fact that steps (t + 1) = step_or_stay M (steps t)
  have h_step : steps M (t + 1) init_cfg = step_or_stay M (steps M t init_cfg) := by
    simp only [steps]
    rw [Function.iterate_succ_apply']

  rw [h_step]

  -- Case analysis on what step does
  let cfg_t := steps M t init_cfg
  unfold step_or_stay

  match h_step_result : step M cfg_t with
  | none =>
    -- Machine halted, config stays the same
    left
    simp [h_step_result]
  | some cfg' =>
    -- Machine took a step
    -- Now analyze what kind of step it was
    unfold step at h_step_result
    split_ifs at h_step_result with h_constraint
    · -- Step preserves constraint
      match h_machine : M cfg_t.q cfg_t.tape.read with
      | none =>
        -- Machine halts, contradiction
        simp [h_machine] at h_step_result
      | some (q', stmt) =>
        -- h_step_result says cfg' = ⟨q', apply_stmt stmt cfg_t.tape⟩
        simp [h_machine] at h_step_result
        -- h_step_result : { q := q', tape := step.apply_stmt stmt cfg_t.tape } = cfg'
        have h_cfg' : cfg' = ⟨q', step.apply_stmt stmt cfg_t.tape⟩ := by
          rw [← h_step_result]

        -- First simplify the goal to work with cfg'
        simp [h_step_result]
        rw [h_cfg']

        -- Case analysis on the statement
        cases stmt with
        | move dir =>
          -- Moving doesn't change encoding
          left
          simp only [step.apply_stmt, encode_config]
          cases dir with
          | left =>
            rw [encode_move_left]
            ring
          | right =>
            have h_move_right := encode_move_invariant cfg_t.tape
            rw [h_move_right.2]
            ring
        | write a =>
          -- Writing can change encoding by ±2^k
          simp only [step.apply_stmt, encode_config]
          -- cfg_t = steps M t init_cfg by definition
          have : cfg_t = steps M t init_cfg := by rfl
          rw [this]
          -- Apply encode_diff_at_write
          have h_exists : ∃ b, ({ q := (steps M t init_cfg).q, tape := (steps M t init_cfg).tape.write a } : Cfg Bool Λ) =
                              { q := (steps M t init_cfg).q, tape := (steps M t init_cfg).tape.write b } := by
            use a
          have h_result := encode_diff_at_write (steps M t init_cfg)
                                              ({ q := (steps M t init_cfg).q, tape := (steps M t init_cfg).tape.write a } : Cfg Bool Λ)
                                              h_exists
          -- Convert from encode_config to just tape.encode
          simp only [encode_config] at h_result
          -- Cast the natural numbers to integers
          cases h_result with
          | inl h_zero =>
            left
            -- The "left" case from encode_diff_at_write occurs when writing doesn't change encoding
            -- h_zero from encode_diff_at_write tells us the integer difference is 0
            -- Since we're subtracting natural numbers cast to integers, this means they're equal
            -- h_zero : encode(write a) - encode = 0 (as naturals)
            -- We need: ↑encode(write a) - ↑encode = 0 (as integers)
            -- When natural subtraction is 0, we have encode(write a) ≤ encode
            have h_le : ((steps M t init_cfg).tape.write a).encode ≤ (steps M t init_cfg).tape.encode := by
              exact Nat.sub_eq_zero_iff_le.mp h_zero
            -- From encode_diff_at_write being in the left case, the encodings don't change
            -- So they must be equal (not just ≤)
            -- Looking at the proof of encode_diff_at_write, the left case occurs when
            -- writing doesn't change the encoding, which happens when:
            -- 1. Writing true over true, or
            -- 2. Writing false over false
            -- In both cases, the encoding stays exactly the same
            have h_eq : ((steps M t init_cfg).tape.write a).encode = (steps M t init_cfg).tape.encode := by
              -- The natural subtraction equals 0 could mean either:
              -- a) The encodings are equal, or
              -- b) encode(write a) < encode
              -- But if (b) were true, then the integer difference would be negative
              -- and encode_diff_at_write would have returned the ∃ k, ... = -2^k case
              -- Since we're in the left case (natural diff = 0), it must be (a)
              by_contra h_ne
              have h_lt : ((steps M t init_cfg).tape.write a).encode < (steps M t init_cfg).tape.encode := by
                exact Nat.lt_of_le_of_ne h_le h_ne
              -- This means writing decreased the encoding
              -- If the encoding strictly decreased, then by the structure of encode_diff_at_write,
              -- we would have: ∃ k, (encode_config cfg') - (encode_config cfg) = -2^k
              -- But we have h_result which is the disjunction from encode_diff_at_write
              -- We're in the left case (h_zero), not the right case
              -- So the encoding cannot have decreased
              
              -- Let's think about what h_result actually says
              -- h_result came from applying encode_diff_at_write
              -- We matched on it and we're in the `inl h_zero` case
              -- This means encode_diff_at_write returned `left (cfg'.encode - cfg.encode = 0)`
              -- If the encoding had decreased, encode_diff_at_write would have returned
              -- `right (∃ k, ... = -2^k)` instead
              
              -- So we have a contradiction: h_lt says encoding decreased,
              -- but being in the left case means it didn't change
              -- This contradiction shows our assumption h_ne is false
              have h_decreased : (((steps M t init_cfg).tape.write a).encode : ℤ) < 
                                 ((steps M t init_cfg).tape.encode : ℤ) := by
                -- h_lt : encode(write a) < encode as naturals
                -- We need: ↑encode(write a) < ↑encode as integers
                have : ↑((steps M t init_cfg).tape.write a).encode < (↑(steps M t init_cfg).tape.encode : ℤ) := by
                  exact Nat.cast_lt.mpr h_lt
                exact this
              
              -- If write decreased the encoding, the integer difference is negative
              have h_neg_diff : (((steps M t init_cfg).tape.write a).encode : ℤ) - 
                               ((steps M t init_cfg).tape.encode : ℤ) < 0 := by
                linarith
              
              -- But h_result (via encode_diff_at_write) tells us the difference is 0 or ±2^k
              -- Since we're in the left case, the difference should be 0 (as naturals)
              -- The integer difference being negative means we should be in the ∃k, diff = -2^k case
              -- This contradicts being in the left case
              
              -- The contradiction comes from the fact that encode_diff_at_write's proof
              -- explicitly handles the case where writing false over true gives -2^k
              -- and returns that in the right branch, not the left branch
              -- We have h_zero : encode(write a) - encode = 0 (natural subtraction)
              -- But h_lt : encode(write a) < encode
              -- For natural subtraction, if a < b then a - b = 0, which is consistent
              -- So we need a different approach to get the contradiction
              
              -- The real contradiction is that encode_diff_at_write would have returned
              -- the right branch (∃ k, diff = -2^k) if the encoding decreased
              -- But we're in the left branch, which means the encoding didn't change
              -- This is fundamentally about the structure of the proof of encode_diff_at_write
              
              -- Actually, let's use the fact that we can re-apply encode_diff_at_write
              -- and it must give us the same result we already have
              have h_reapply := encode_diff_at_write (steps M t init_cfg) 
                                   ⟨(steps M t init_cfg).q, (steps M t init_cfg).tape.write a⟩ h_exists
              -- h_reapply tells us the difference is 0 or ±2^k
              -- We know we're in the case where natural diff = 0
              -- If encoding decreased, we'd have integer diff < 0, so it would be -2^k
              -- But that would put us in the right branch of h_reapply, not the left
              cases h_reapply with
              | inl h_zero' =>
                -- This case: natural diff = 0
                -- Both h_zero and h_zero' say the natural difference is 0
                -- From h_zero': encode(write a) - encode = 0 (natural)
                -- From h_zero: encode(write a) - encode = 0 (natural)
                -- These are the same, so we have consistency
                -- But we still haven't proven that the encodings are equal
                -- 
                -- The key is to look at what encode_diff_at_write actually proves
                -- When it returns left, it's showing that the encoding doesn't change
                -- This happens only when writing the same value (true over true, or false over false)
                -- In those cases, the encoding is exactly preserved
                --
                -- Actually, looking at encode_diff_at_write's proof structure:
                -- It does case analysis on current value and new value
                -- Returns left only when they're the same
                -- In those cases it proves the tapes are equal, hence encodings are equal
                --
                -- So if h_zero' holds, the encodings must be equal
                -- But our h_ne says they're not equal - contradiction!
                -- 
                -- To make this formal, we need to understand that natural subtraction = 0
                -- combined with the fact that encode_diff_at_write exhaustively covers all cases
                -- means the encodings must be equal
                -- 
                -- Since both h_zero and h_zero' say nat diff = 0, and we know from h_neg_diff
                -- that if encodings were different, we'd have int diff < 0 (so -2^k case),
                -- the fact we're in the left case means encodings are equal
                exfalso
                -- We have h_ne : encode(write a) ≠ encode
                -- We have h_lt : encode(write a) < encode  
                -- We have h_zero : encode(write a) - encode = 0 (natural)
                -- We have h_zero' : encode(write a) - encode = 0 (natural)
                -- From encode_diff_at_write's structure, being in left case means no change
                -- But h_lt says there was a decrease
                -- This is the contradiction
                
                -- Actually, the cleaner way: h_zero' implies the encodings are equal
                -- because that's what the left case of encode_diff_at_write means
                have h_eq' : ((steps M t init_cfg).tape.write a).encode = (steps M t init_cfg).tape.encode := by
                  -- When encode_diff_at_write returns left with nat diff = 0,
                  -- it means the encodings are exactly equal
                  -- This is because the proof checks if writing changes the value
                  -- and returns left only when it doesn't
                  -- 
                  -- We have h_zero' : encode(write a) - encode = 0 (natural)
                  -- Combined with h_le : encode(write a) ≤ encode
                  -- If they were not equal, we'd have encode(write a) < encode
                  -- Then the integer difference would be negative
                  -- But encode_diff_at_write would return right with -2^k, not left
                  -- Since it returned left (h_zero'), they must be equal
                  --
                  -- More directly: natural subtraction = 0 means ≤
                  -- We have two cases: = or <
                  -- If <, then encode_diff_at_write returns right (by its construction)
                  -- Since it returned left, we must have =
                  by_contra h_ne'
                  have h_lt' : ((steps M t init_cfg).tape.write a).encode < (steps M t init_cfg).tape.encode := by
                    exact Nat.lt_of_le_of_ne h_le h_ne'
                  -- If strictly less, the integer difference is negative
                  have h_neg' : (((steps M t init_cfg).tape.write a).encode : ℤ) - 
                               ((steps M t init_cfg).tape.encode : ℤ) < 0 := by
                    have : (((steps M t init_cfg).tape.write a).encode : ℤ) < 
                           ((steps M t init_cfg).tape.encode : ℤ) := by
                      exact Nat.cast_lt.mpr h_lt'
                    linarith
                  -- But then encode_diff_at_write would give us ∃ k, diff = -2^k
                  -- not the left case we're in (h_reapply = inl h_zero')
                  -- This is a contradiction because encode_diff_at_write is deterministic
                  -- and must return the same result for the same inputs
                  -- 
                  -- The contradiction is that h_reapply = inl h_zero' says we're in left case
                  -- but h_neg' implies we should be in right case with -2^k
                  -- Since encode_diff_at_write exhaustively covers all cases and is deterministic,
                  -- this is impossible
                  --
                  -- Actually, we can be more direct: h_zero' says nat diff = 0
                  -- Combined with the fact that if int diff < 0, encode_diff_at_write
                  -- would return right, not left, we conclude they're equal
                  -- h_zero' says nat diff = 0, but h_lt' says first < second
                  -- So nat diff should be 0 (which it is), but that's not a contradiction
                  -- The real contradiction is deeper: we're in left case but should be in right
                  -- Let me think about this differently...
                  -- If h_lt' holds, then encode(write a) < encode
                  -- So the integer difference is negative
                  -- But we're in the left case of h_reapply, which means nat diff = 0
                  -- This is consistent (nat subtraction truncates to 0)
                  -- The contradiction is that encode_diff_at_write should return right, not left
                  -- when the integer difference is negative
                  -- So the issue is we can't be in both left (from original) and have negative diff
                  sorry -- Need to formalize the determinism of encode_diff_at_write
                exact h_ne h_eq'
              | inr h_exists_k =>
                -- This case: ∃ k, integer diff = ±2^k  
                obtain ⟨k, hk⟩ := h_exists_k
                cases hk with
                | inl h_pos =>
                  -- Case: integer diff = 2^k > 0
                  -- But we have h_zero : nat diff = 0
                  -- If int diff > 0, then encode(write a) > encode
                  -- So nat diff = encode(write a) - encode > 0
                  -- This contradicts h_zero
                  have h_pos_diff : 0 < encode_config ⟨(steps M t init_cfg).q, (steps M t init_cfg).tape.write a⟩ - 
                                       encode_config (steps M t init_cfg) := by
                    -- From h_pos: ↑encode(write a) - ↑encode = 2^k
                    -- Since 2^k > 0, we have ↑encode(write a) > ↑encode
                    -- Therefore encode(write a) > encode (as naturals)
                    -- So encode(write a) - encode > 0 (natural subtraction)
                    have h_cast_pos : (2 : ℤ)^k > 0 := by
                      exact pow_pos (by norm_num : (2 : ℤ) > 0) k
                    have h_gt : encode_config ⟨(steps M t init_cfg).q, (steps M t init_cfg).tape.write a⟩ > 
                               encode_config (steps M t init_cfg) := by
                      -- From h_pos: ↑(encode_config(write a)) - ↑encode_config = 2^k > 0
                      -- So ↑(encode_config(write a)) > ↑encode_config
                      -- Therefore encode_config(write a) > encode_config as naturals
                      have : (encode_config ⟨(steps M t init_cfg).q, (steps M t init_cfg).tape.write a⟩ : ℤ) > 
                             (encode_config (steps M t init_cfg) : ℤ) := by
                        linarith [h_pos, h_cast_pos]
                      exact Nat.cast_lt.mp this
                    exact Nat.sub_pos_of_lt h_gt
                  -- But h_zero says nat diff = 0 for tape.encode
                  -- We need to connect encode_config to tape.encode
                  -- encode_config cfg = cfg.tape.encode by definition
                  have h_zero_config : encode_config ⟨(steps M t init_cfg).q, (steps M t init_cfg).tape.write a⟩ - 
                                      encode_config (steps M t init_cfg) = 0 := by
                    simp only [encode_config]
                    exact h_zero
                  linarith [h_zero_config, h_pos_diff]
                | inr h_neg =>
                  -- Case: integer diff = -2^k < 0
                  -- We have h_zero : nat diff = 0
                  -- We have h_neg : int diff = -2^k
                  -- This is consistent when encode(write a) < encode
                  -- But this contradicts being in the original left case
                  --
                  -- The issue is that we started with h_result being in the left case
                  -- If the encoding decreased (int diff = -2^k), then h_result
                  -- should have been in the right case originally
                  -- This is our contradiction
                  exfalso
                  -- We need to show this is impossible given our original h_result
                  -- The original h_result was obtained from encode_diff_at_write
                  -- and we matched on it to get into the `inl h_zero` case
                  -- But if int diff = -2^k, encode_diff_at_write would return right
                  -- not left, so we wouldn't be in this branch of the original match
                  --
                  -- The key insight: encode_diff_at_write is a function that returns
                  -- a unique result for given inputs. We have:
                  -- 1. h_result (via matching) says encode_diff_at_write returned left
                  -- 2. h_reapply with h_neg says it should return right
                  -- This is a contradiction
                  --
                  -- More specifically: we know the original application of encode_diff_at_write
                  -- gave us the left case (that's how we got h_zero)
                  -- But h_neg says the integer difference is -2^k
                  -- If the integer difference is -2^k, then encode_diff_at_write
                  -- MUST return the right case, not the left case
                  -- This contradicts our original h_result being in the left case
                  --
                  -- The formal argument: encode_diff_at_write returns a disjunction
                  -- The left means nat diff = 0 AND encodings are equal
                  -- The right means int diff = ±2^k AND encodings differ
                  -- We can't be in both cases simultaneously
                  --
                  -- We have h_neg : int diff = -2^k < 0
                  -- This means encode(write a) < encode
                  -- So encode_diff_at_write must return right, not left
                  -- But we originally got left (h_zero), contradiction
                  have h_neg_nonzero : (-2^k : ℤ) ≠ 0 := by
                    simp only [neg_ne_zero]
                    exact pow_ne_zero k (by norm_num : (2 : ℤ) ≠ 0)
                  -- From h_neg, the integer difference is -2^k ≠ 0
                  -- So the natural difference being 0 means encode(write a) < encode
                  -- In this case, encode_diff_at_write returns right, not left
                  -- But we started in the left case (h_zero), contradiction
                  have h_int_diff_neg : (((steps M t init_cfg).tape.write a).encode : ℤ) - 
                                       ((steps M t init_cfg).tape.encode : ℤ) = -2^k := by
                    -- h_neg is about encode_config, we need it for tape.encode
                    simp only [encode_config] at h_neg
                    exact h_neg
                  have h_not_zero_int : (((steps M t init_cfg).tape.write a).encode : ℤ) - 
                                       ((steps M t init_cfg).tape.encode : ℤ) ≠ 0 := by
                    rw [h_int_diff_neg]
                    exact h_neg_nonzero
                  -- If int diff ≠ 0 but nat diff = 0, then encode(write a) < encode
                  -- This means encode_diff_at_write should return right with -2^k
                  -- But our original h_result was left, contradiction
                  have h_not_eq : ((steps M t init_cfg).tape.write a).encode ≠ (steps M t init_cfg).tape.encode := by
                    intro h_eq_contra
                    have : (((steps M t init_cfg).tape.write a).encode : ℤ) = 
                           ((steps M t init_cfg).tape.encode : ℤ) := by simp [h_eq_contra]
                    have : (((steps M t init_cfg).tape.write a).encode : ℤ) - 
                           ((steps M t init_cfg).tape.encode : ℤ) = 0 := by simp [this]
                    exact h_not_zero_int this
                  -- Combined with h_zero (nat diff = 0), we have encode(write a) < encode
                  have h_lt_result : ((steps M t init_cfg).tape.write a).encode < (steps M t init_cfg).tape.encode := by
                    exact Nat.lt_of_le_of_ne h_le h_not_eq
                  -- But if encode(write a) < encode, then h_zero (nat diff = 0) and
                  -- h_result being left is impossible - encode_diff_at_write would return right
                  -- h_lt_result : encode(write a) < encode
                  -- h_zero : encode(write a) - encode = 0
                  -- These are consistent for natural subtraction
                  -- The contradiction is that we should be in the right case, not left
                  -- Let's use a different approach
                  have h_zero_tape : ((steps M t init_cfg).tape.write a).encode ≤ (steps M t init_cfg).tape.encode := by
                    exact Nat.sub_eq_zero_iff_le.mp h_zero
                  -- Combined with h_lt_result, we get equality contradiction
                  -- h_zero_tape : first ≤ second
                  -- h_lt_result : first < second
                  -- These are consistent, not contradictory
                  -- The issue is we need h_ne to be false, but that requires first = second
                  have h_not_lt : ¬((steps M t init_cfg).tape.write a).encode < (steps M t init_cfg).tape.encode := by
                    -- We can't have both first < second and be in the left case of encode_diff_at_write
                    sorry
                  -- Wait, that's backwards. Let me think...
                  -- h_lt_result says first < second, h_zero_tape says first ≤ second
                  -- That's consistent, not a contradiction
                  -- The real issue is being in left case when we should be in right
                  sorry
            simp only [h_eq, sub_self]
          | inr h_pow =>
            right
            exact h_pow


/-- The k value in a sequence change equals the absolute position where the write occurred -/
lemma sequence_k_equals_position (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ)
    (h_change : sequence M init_cfg (t + 1) ≠ sequence M init_cfg t) :
    ∃ k : ℕ, (sequence_difference (sequence M init_cfg) t = 2^k ∨
              sequence_difference (sequence M init_cfg) t = -(2^k : ℤ)) ∧
              k = Int.natAbs (-(steps M t init_cfg).tape.head_pos) := by
  -- First, use sequence_diff_is_power_of_two to get that the difference is 0 or ±2^k
  have h_diff := sequence_diff_is_power_of_two M init_cfg t

  -- h_change means the difference is not 0
  unfold sequence_difference at ⊢
  unfold sequence at h_change
  have h_not_zero : encode_config (steps M (t + 1) init_cfg) ≠ encode_config (steps M t init_cfg) := by
    intro h_eq
    apply h_change
    exact h_eq

  -- So the difference must be ±2^k for some k
  cases h_diff with
  | inl h_zero =>
    -- If difference is 0, then sequences are equal, contradicting h_change
    exfalso
    unfold sequence_difference at h_zero
    have h_eq : encode_config (steps M (t + 1) init_cfg) = encode_config (steps M t init_cfg) := by
      -- h_zero says the Int difference is 0
      have : (encode_config (steps M (t + 1) init_cfg) : ℤ) = (encode_config (steps M t init_cfg) : ℤ) := by
        simp only [sequence_difference, sequence] at h_zero
        linarith
      exact Nat.cast_injective this
    exact h_not_zero h_eq
  | inr h_exists =>
    obtain ⟨k, h_pow⟩ := h_exists
    use k
    constructor
    · exact h_pow
    · -- Now we need to show k = |-(steps M t init_cfg).tape.head_pos|
      -- Since a write occurred at the head position, and encode_diff_at_write tells us
      -- the change is ±2^k where k is the absolute position
      sorry  -- TODO: Connect to encode_diff_at_write and extract position

/-- The k value is bounded by the step number -/
lemma sequence_k_bound (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ)
    (h_init : init_cfg.tape.head_pos = 0) :
    ∀ k : ℕ, (sequence_difference (sequence M init_cfg) t = 2^k ∨
               sequence_difference (sequence M init_cfg) t = -(2^k : ℤ)) →
    k ≤ t := by
  intro k hk
  -- The key insight: if the difference is ±2^k, then by encode_diff_at_write,
  -- k is the absolute value of the head position where the write occurred
  -- Since head starts at 0 and can move at most 1 position per step,
  -- after t steps the head is at position ≥ -t
  -- Therefore |head_pos| ≤ t, so k ≤ t

  -- We need to connect the power k to the position
  -- From the structure of encode_diff_at_write, when writing changes the encoding by ±2^k,
  -- k = |head_pos| where the write occurred

  -- Get the head position bound
  have h_bound := head_pos_bound M init_cfg t
  rw [h_init] at h_bound
  -- h_bound : (steps M t init_cfg).tape.head_pos ≥ 0 - t
  simp at h_bound
  -- h_bound : (steps M t init_cfg).tape.head_pos ≥ -↑t

  -- The head position is always ≤ 0 for LeftwardTape
  have h_nonpos := (steps M t init_cfg).tape.head_nonpos
  -- So we have: -t ≤ head_pos ≤ 0

  -- If the sequence changes at time t, it's because of a write at the head position
  -- The change is ±2^k where k = |head_pos|
  -- Since -t ≤ head_pos ≤ 0, we have |head_pos| ≤ t

  -- We need to show k ≤ t
  -- By the nature of encode_diff_at_write, k represents |head_pos| at step t
  -- Since -t ≤ head_pos ≤ 0, we have |head_pos| = -head_pos ≤ t

  -- From h_bound and h_nonpos: -t ≤ head_pos ≤ 0 where head_pos = (steps M t init_cfg).tape.head_pos
  -- Therefore: 0 ≤ -head_pos ≤ t

  have h_pos_neg : 0 ≤ -(steps M t init_cfg).tape.head_pos := by linarith
  have h_pos_bound : -(steps M t init_cfg).tape.head_pos ≤ t := by linarith

  -- The key fact: when sequence_difference = ±2^k, the k equals Int.natAbs(-head_pos)
  -- where head_pos is the position where the write occurred.
  -- This is established in encode_diff_at_write where it uses `use Int.natAbs (-cfg.tape.head_pos)`

  -- At time t, if the sequence changes by ±2^k, it's due to a write at the current head position
  -- Therefore k = Int.natAbs(-(steps M t init_cfg).tape.head_pos)

  -- Since we've shown Int.natAbs(-(steps M t init_cfg).tape.head_pos) ≤ t,
  -- and k equals this value, we have k ≤ t

  -- The formal proof would require extracting the witness from the existential in hk
  -- and showing it equals Int.natAbs(-(steps M t init_cfg).tape.head_pos)
  -- For now, we assert this connection
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
  -- Since the sequences change at times i and j, by sequence_diff_is_power_of_two,
  -- the differences must be 0 or ±2^k for some k
  have h_diff_i := sequence_diff_is_power_of_two M init_cfg i
  have h_diff_j := sequence_diff_is_power_of_two M init_cfg j

  -- The changes are non-zero because the sequences differ
  have h_nonzero_i : sequence_difference (sequence M init_cfg) i ≠ 0 := by
    intro h_zero
    unfold sequence_difference at h_zero
    have h_eq : sequence M init_cfg (i + 1) = sequence M init_cfg i := by
      have : (sequence M init_cfg (i + 1) : ℤ) = sequence M init_cfg i := by
        linarith
      exact Nat.cast_injective this
    exact h_i_change h_eq

  have h_nonzero_j : sequence_difference (sequence M init_cfg) j ≠ 0 := by
    intro h_zero
    unfold sequence_difference at h_zero
    have h_eq : sequence M init_cfg (j + 1) = sequence M init_cfg j := by
      have : (sequence M init_cfg (j + 1) : ℤ) = sequence M init_cfg j := by
        linarith
      exact Nat.cast_injective this
    exact h_j_change h_eq

  -- So the differences must be ±2^k for some k
  cases h_diff_i with
  | inl h_zero_i =>
    exfalso
    unfold sequence_difference at h_zero_i
    exact h_nonzero_i h_zero_i
  | inr h_exists_i =>
    obtain ⟨k_i, h_ki⟩ := h_exists_i
    cases h_diff_j with
    | inl h_zero_j =>
      exfalso
      unfold sequence_difference at h_zero_j
      exact h_nonzero_j h_zero_j
    | inr h_exists_j =>
      obtain ⟨k_j, h_kj⟩ := h_exists_j
      use k_i, k_j
      constructor
      · exact h_ki
      constructor
      · exact h_kj
      · -- Now prove the movement constraint: |k_j - k_i| ≤ j - i
        -- k_i = Int.natAbs(-(head_pos at step i))
        -- k_j = Int.natAbs(-(head_pos at step j))
        -- The head can move at most 1 position per step
        -- So |head_pos_j - head_pos_i| ≤ j - i
        -- This implies ||head_pos_j| - |head_pos_i|| ≤ j - i
        -- Therefore |k_j - k_i| ≤ j - i

        -- From the conceptual understanding:
        -- k values represent absolute head positions where writes occur
        -- Head moves at most 1 step per time unit
        -- So the difference in k values is bounded by time difference
        sorry
  -- 6. Therefore |k_j - k_i| ≤ j - i

end LeftTM0