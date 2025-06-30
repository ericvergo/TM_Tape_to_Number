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

/-- Writing false over true strictly decreases the encoding -/
lemma encode_strict_decrease_write_false (tape : LeftwardTape Bool) (a : Bool)
    (h_current : tape.nth 0 = true) (h_new : a = false) :
    (tape.write a).encode < tape.encode := by
  -- The encoding is the sum of 2^|i| for all absolute positions i ≤ 0 with true
  -- Writing false at head position removes 2^|head_pos| from this sum

  -- First, establish that head_pos ≤ 0
  have h_head_nonpos : tape.head_pos ≤ 0 := tape.head_nonpos

  -- The key insight: write only changes the value at head position
  -- After writing false, that position no longer contributes to the sum

  -- The old tape has true at absolute position head_pos
  have h_old_true : tape.nth_absolute tape.head_pos = true := by
    simp only [nth_absolute, sub_self]
    exact h_current

  -- After writing false, the new tape has false at head_pos
  have h_new_false : (tape.write a).nth_absolute tape.head_pos = false := by
    simp only [nth_absolute, write]
    rw [Turing.Tape.write_nth]
    simp only [if_pos (sub_self tape.head_pos)]
    exact h_new

  -- Other positions are unchanged
  have h_unchanged : ∀ i ≠ tape.head_pos,
    (tape.write a).nth_absolute i = tape.nth_absolute i := by
    intro i hi
    simp only [nth_absolute, write]
    rw [Turing.Tape.write_nth]
    split_ifs with h
    · have : i = tape.head_pos := by linarith
      contradiction
    · rfl

  -- The true_positions of new tape = old tape's true_positions \ {head_pos}
  have h_diff : (tape.write a).true_positions_absolute =
                tape.true_positions_absolute \ {tape.head_pos} := by
    ext i
    simp only [true_positions_absolute, Finset.mem_filter, Set.Finite.mem_toFinset,
               Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · intro ⟨hi_mem, hi_le, hi_true⟩
      constructor
      · refine ⟨?_, hi_le, ?_⟩
        · simp only [Set.mem_setOf, has_content_at_absolute]
          by_cases h : i = tape.head_pos
          · rw [h, h_old_true]
            trivial
          · rw [← h_unchanged i h]
            simp only [has_content_at_absolute] at hi_mem
            exact hi_mem
        · by_cases h : i = tape.head_pos
          · rw [h] at hi_true
            rw [h_new_false] at hi_true
            simp at hi_true
          · rw [← h_unchanged i h]
            exact hi_true
      · intro h
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

  -- head_pos is in the old true_positions
  have h_in : tape.head_pos ∈ tape.true_positions_absolute := by
    simp only [true_positions_absolute, Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨?_, h_head_nonpos, h_old_true⟩
    simp only [Set.mem_setOf, has_content_at_absolute, h_old_true]
    trivial

  -- The sum decreases by exactly 2^|head_pos|
  have h_sum_decrease : tape.encode = (tape.write a).encode + 2^(-tape.head_pos).natAbs := by
    simp only [encode]
    rw [h_diff]
    -- Sum over A = Sum over (A \ {x}) + 2^f(x) when x ∈ A
    have : (∑ i ∈ tape.true_positions_absolute, 2 ^ (-i).natAbs) =
           (∑ i ∈ tape.true_positions_absolute \ {tape.head_pos}, 2 ^ (-i).natAbs) +
           2 ^ (-tape.head_pos).natAbs := by
      rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr h_in)]
      congr
    exact this

  -- Since 2^|head_pos| > 0, we have strict inequality
  have h_pow_pos : 0 < 2^(-tape.head_pos).natAbs := by
    apply pow_pos
    norm_num

  linarith

/-- Writing true over false strictly increases the encoding -/
lemma encode_strict_increase_write_true (tape : LeftwardTape Bool) (a : Bool)
    (h_current : tape.nth 0 = false) (h_new : a = true) :
    tape.encode < (tape.write a).encode := by
  -- The encoding is the sum of 2^|i| for all absolute positions i ≤ 0 with true
  -- Writing true at head position adds 2^|head_pos| to this sum

  -- First, establish that head_pos ≤ 0
  have h_head_nonpos : tape.head_pos ≤ 0 := tape.head_nonpos

  -- The key insight: write only changes the value at head position
  -- After writing true, that position now contributes to the sum

  -- The old tape has false at absolute position head_pos
  have h_old_false : tape.nth_absolute tape.head_pos = false := by
    simp only [nth_absolute, sub_self]
    exact h_current

  -- After writing true, the new tape has true at head_pos
  have h_new_true : (tape.write a).nth_absolute tape.head_pos = true := by
    simp only [nth_absolute, write]
    rw [Turing.Tape.write_nth]
    simp only [if_pos (sub_self tape.head_pos)]
    exact h_new

  -- Other positions are unchanged
  have h_unchanged : ∀ i ≠ tape.head_pos,
    (tape.write a).nth_absolute i = tape.nth_absolute i := by
    intro i hi
    simp only [nth_absolute, write]
    rw [Turing.Tape.write_nth]
    split_ifs with h
    · have : i = tape.head_pos := by linarith
      contradiction
    · rfl

  -- The true_positions of new tape = old tape's true_positions ∪ {head_pos}
  have h_diff : (tape.write a).true_positions_absolute =
                tape.true_positions_absolute ∪ {tape.head_pos} := by
    ext i
    simp only [true_positions_absolute, Finset.mem_filter, Set.Finite.mem_toFinset,
               Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro ⟨hi_mem, hi_le, hi_true⟩
      by_cases h : i = tape.head_pos
      · right; exact h
      · left
        refine ⟨?_, hi_le, ?_⟩
        · simp only [Set.mem_setOf, has_content_at_absolute]
          rw [← h_unchanged i h]
          simp only [has_content_at_absolute] at hi_mem
          exact hi_mem
        · rw [← h_unchanged i h]
          exact hi_true
    · intro h
      cases h with
      | inl h_in =>
        obtain ⟨hi_mem, hi_le, hi_true⟩ := h_in
        refine ⟨?_, hi_le, ?_⟩
        · simp only [Set.mem_setOf, has_content_at_absolute]
          by_cases h : i = tape.head_pos
          · rw [h, h_new_true]
            trivial
          · rw [h_unchanged i h]
            simp only [has_content_at_absolute] at hi_mem
            exact hi_mem
        · by_cases h : i = tape.head_pos
          · rw [h, h_new_true]
          · rw [h_unchanged i h]
            exact hi_true
      | inr h_eq =>
        rw [h_eq]
        refine ⟨?_, h_head_nonpos, h_new_true⟩
        simp only [Set.mem_setOf, has_content_at_absolute, h_new_true]
        trivial

  -- head_pos is NOT in the old true_positions (since it has false)
  have h_not_in : tape.head_pos ∉ tape.true_positions_absolute := by
    simp only [true_positions_absolute, Finset.mem_filter, Set.Finite.mem_toFinset]
    intro ⟨_, _, hi_true⟩
    rw [h_old_false] at hi_true
    simp at hi_true

  -- The sum increases by exactly 2^|head_pos|
  have h_sum_increase : (tape.write a).encode = tape.encode + 2^(-tape.head_pos).natAbs := by
    simp only [encode]
    rw [h_diff]
    -- Sum over A ∪ {x} = Sum over A + 2^f(x) when x ∉ A
    have : (∑ i ∈ tape.true_positions_absolute ∪ {tape.head_pos}, 2 ^ (-i).natAbs) =
           (∑ i ∈ tape.true_positions_absolute, 2 ^ (-i).natAbs) +
           2 ^ (-tape.head_pos).natAbs := by
      rw [Finset.sum_union (Finset.disjoint_singleton_right.mpr h_not_in)]
      congr
    exact this

  -- Since 2^|head_pos| > 0, we have strict inequality
  have h_pow_pos : 0 < 2^(-tape.head_pos).natAbs := by
    apply pow_pos
    norm_num

  linarith

/-- Helper: When encode_diff_at_write returns left (nat diff = 0), encodings are equal -/
lemma encode_diff_at_write_eq_of_zero (cfg : Cfg Bool Λ) (cfg' : Cfg Bool Λ)
    (h_step : ∃ a, cfg' = ⟨cfg.q, cfg.tape.write a⟩)
    (h_zero : encode_config cfg' - encode_config cfg = 0) :
    encode_config cfg' = encode_config cfg := by
  -- When natural subtraction is 0, we have cfg' ≤ cfg
  have h_le : encode_config cfg' ≤ encode_config cfg := by
    rw [← tsub_eq_zero_iff_le]
    exact h_zero

  -- We'll show they must be equal by examining what encode_diff_at_write tells us
  obtain ⟨a, h_cfg'⟩ := h_step
  rw [h_cfg'] at h_zero ⊢

  -- From the proof of encode_diff_at_write, we know it returns left (nat diff = 0)
  -- only when writing doesn't change the tape value:
  -- 1. Writing true where there's already true (lines 54-78)
  -- 2. Writing false where there's already false (lines 345-389)
  -- In both cases, the tape doesn't change: tape.write a = tape

  -- Get the current value at head position
  let current_val := cfg.tape.nth 0

  -- Case analysis on current value and what we're writing
  by_cases h_current : current_val = true
  · -- Current value is true
    by_cases h_new : a = true
    · -- Writing true over true: tape doesn't change
      have h_write_eq : cfg.tape.tape.write a = cfg.tape.tape := by
        rw [h_new]
        apply Turing.Tape.ext
        intro i
        by_cases h_pos : i = 0
        · rw [h_pos, Turing.Tape.write_nth]
          simp
          exact h_current
        · rw [Turing.Tape.write_nth]
          simp [h_pos]
      simp only [encode_config, LeftwardTape.write]
      rw [h_write_eq]
    · -- Writing false over true: encoding must decrease
      -- But h_le says new ≤ old, and we know new ≠ old in this case
      -- So new < old, which means nat subtraction = 0
      -- But encode_diff_at_write would return right with -2^k in this case
      exfalso
      have h_diff := encode_diff_at_write cfg ⟨cfg.q, cfg.tape.write a⟩ ⟨a, rfl⟩
      simp only [encode_config] at h_zero
      cases h_diff with
      | inl h_zero' =>
        have h_a_false : a = false := by
          cases a with
          | false => rfl
          | true => exfalso; exact h_new rfl

        -- From encode_diff_at_write's proof structure:
        -- When writing false (h_a_false) over true (h_current),
        -- the encoding strictly decreases
        have h_strict_decrease : (cfg.tape.write a).encode < cfg.tape.encode := by
          -- Writing false at a position with true removes 2^|pos| from the sum
          -- Since we're writing at head position (0 relative), we remove 2^|head_pos|
          -- The encoding is the sum of 2^|i| for all absolute positions i ≤ 0 with true
          -- After writing false at head, we remove head_pos from the set of true positions
          -- So new_encode = old_encode - 2^|head_pos| < old_encode

          -- Use properties from the encode_diff_at_write proof
          have h_head_nonpos : cfg.tape.head_pos ≤ 0 := cfg.tape.head_nonpos

          -- The old tape has true at head position
          have h_old_true : cfg.tape.nth 0 = true := h_current

          -- After writing false, the new tape has false at head position
          have h_new_false : (cfg.tape.write a).nth 0 = false := by
            simp only [LeftwardTape.write, LeftwardTape.nth]
            rw [Turing.Tape.write_nth]
            simp only [if_pos rfl]
            exact h_a_false

          -- The encoding strictly decreases when we change a true to false
          apply encode_strict_decrease_write_false
          · exact h_old_true
          · exact h_a_false

        -- But h_zero' says the nat difference is 0
        -- This means new_encode ≤ old_encode (since nat subtraction gives 0 when a ≤ b)
        have h_le : (cfg.tape.write a).encode ≤ cfg.tape.encode := by
          have : (cfg.tape.write a).encode - cfg.tape.encode = 0 := by
            simp only [encode_config] at h_zero'
            exact h_zero'
          exact Nat.sub_eq_zero_iff_le.mp this

        -- This is our contradiction
        -- We have h_strict_decrease : (cfg.tape.write a).encode < cfg.tape.encode
        -- This means the difference is positive: cfg.tape.encode - (cfg.tape.write a).encode > 0
        -- But h_zero' says the difference is 0
        -- These cannot both be true
        have h_pos_diff : cfg.tape.encode - (cfg.tape.write a).encode > 0 := by
          exact Nat.sub_pos_of_lt h_strict_decrease

        exact absurd h_strict_decrease (not_lt.mpr (le_of_eq (Eq.symm (by

          sorry
        ))))
      | inr h_exists =>

        obtain ⟨k, h_pow⟩ := h_exists
        cases h_pow with
        | inl h_pos =>
          -- Positive difference contradicts h_zero
          simp only [encode_config] at h_pos
          have : encode_config ⟨cfg.q, cfg.tape.write a⟩ > encode_config cfg := by
            have h_pos_pow : (0 : ℤ) < 2^k := by
              apply pow_pos
              norm_num
            have h_gt_int : (encode_config ⟨cfg.q, cfg.tape.write a⟩ : ℤ) > encode_config cfg := by
              have h_eq : (encode_config ⟨cfg.q, cfg.tape.write a⟩ : ℤ) - encode_config cfg = 2^k := h_pos
              linarith
            have h_gt_nat : encode_config ⟨cfg.q, cfg.tape.write a⟩ > encode_config cfg := by
              simp only [encode_config] at h_gt_int ⊢
              exact Nat.cast_lt.mp h_gt_int
            linarith
          -- h_zero says nat diff = 0 but we showed encode > encode, so diff > 0
          have h_pos_diff : encode_config ⟨cfg.q, cfg.tape.write a⟩ - encode_config cfg > 0 := by
            exact Nat.sub_pos_of_lt this
          have h_eq_zero : encode_config ⟨cfg.q, cfg.tape.write a⟩ - encode_config cfg = 0 := h_zero
          linarith
        | inr h_neg =>

          -- Let's prove they're not equal
          have h_neq : encode_config ⟨cfg.q, cfg.tape.write a⟩ ≠ encode_config cfg := by
            intro h_eq
            -- If they were equal, then their integer difference would be 0
            have h_diff_zero : (encode_config ⟨cfg.q, cfg.tape.write a⟩ : ℤ) - encode_config cfg = 0 := by
              simp [h_eq]
            -- But h_neg says the difference is -2^k
            rw [h_neg] at h_diff_zero
            -- So -2^k = 0, which means 2^k = 0
            have : (2^k : ℤ) = 0 := by linarith
            -- But 2^k > 0 for any k
            have h_pos : (0 : ℤ) < 2^k := by
              apply pow_pos
              norm_num
            linarith
          admit
  · -- Current value is false
    by_cases h_new : a = false
    · -- Writing false over false: tape doesn't change
      have h_write_eq : cfg.tape.tape.write a = cfg.tape.tape := by
        rw [h_new]
        apply Turing.Tape.ext
        intro i
        by_cases h_pos : i = 0
        · rw [h_pos, Turing.Tape.write_nth]
          simp
          -- We need to show cfg.tape.tape.head = false
          -- We know current_val = cfg.tape.nth 0 and ¬(current_val = true)
          -- So current_val = false
          have : current_val = false := by
            cases h_eq : current_val
            · rfl
            · rw [h_eq] at h_current
              simp at h_current
          -- Now show cfg.tape.tape.head = false
          -- Since cfg.tape.nth 0 = cfg.tape.tape.head
          simp only [nth, LeftwardTape.read] at this
          exact this
        · rw [Turing.Tape.write_nth]
          simp [h_pos]
      simp only [encode_config, LeftwardTape.write]
      rw [h_write_eq]
    · -- Writing true over false: encoding must increase
      -- This means new > old, so nat diff ≠ 0
      -- But we have h_zero saying nat diff = 0
      -- This is impossible
      exfalso
      have h_strict_increase : cfg.tape.encode < (cfg.tape.write a).encode := by
        -- Writing true over false adds 2^|head_pos| to the sum
        -- We need to establish what values we have
        have h_current_false : current_val = false := by
          cases h_eq : current_val
          · rfl
          · rw [h_eq] at h_current
            simp at h_current
        have h_a_true : a = true := by
          cases a with
          | false =>
            -- If a = false, then h_new says ¬a = false, i.e., ¬false = false
            -- This is True = False, which is False
            exfalso
            exact h_new rfl
          | true => rfl

        -- Now apply our lemma
        apply encode_strict_increase_write_true
        · exact h_current_false
        · exact h_a_true
      -- h_zero says (new - old) in naturals = 0
      -- This means new ≤ old
      simp only [encode_config] at h_zero
      have : (cfg.tape.write a).encode ≤ cfg.tape.encode := by
        rw [← tsub_eq_zero_iff_le]; exact h_zero
      linarith

/-- When a write changes the encoding, the k value equals the absolute head position -/
lemma encode_diff_k_eq_head_pos (cfg : Cfg Bool Λ) (a : Bool)
    (h_change : encode_config ⟨cfg.q, cfg.tape.write a⟩ ≠ encode_config cfg) :
    let k := Int.natAbs (-cfg.tape.head_pos)
    (encode_config ⟨cfg.q, cfg.tape.write a⟩ : ℤ) - encode_config cfg = 2^k ∨
    (encode_config ⟨cfg.q, cfg.tape.write a⟩ : ℤ) - encode_config cfg = -(2^k : ℤ) := by
  -- Apply encode_diff_at_write
  have h_diff := encode_diff_at_write cfg ⟨cfg.q, cfg.tape.write a⟩ ⟨a, rfl⟩

  cases h_diff with
  | inl h_zero =>
    -- If nat diff is 0, then they're equal
    have h_eq := encode_diff_at_write_eq_of_zero cfg ⟨cfg.q, cfg.tape.write a⟩ ⟨a, rfl⟩ h_zero
    exact absurd h_eq h_change
  | inr h_exists =>
    -- From the proof structure of encode_diff_at_write:
    -- When writing changes the encoding, it uses Int.natAbs (-cfg.tape.head_pos)
    -- This is seen at lines 81 and 212 of the original proof
    obtain ⟨k', h_pow⟩ := h_exists

    -- We need to show k' = Int.natAbs (-cfg.tape.head_pos)
    -- This is true by the construction in encode_diff_at_write
    -- but we can't extract it directly from the existential

    -- Instead, let's prove it directly by analyzing the cases
    let current_val := cfg.tape.nth 0

    by_cases h_current : current_val = true
    · -- Current value is true
      by_cases h_new : a = true
      · -- Writing true over true: no change
        exfalso
        have h_no_change : encode_config ⟨cfg.q, cfg.tape.write a⟩ = encode_config cfg := by
          have h_write_eq : cfg.tape.tape.write a = cfg.tape.tape := by
            rw [h_new]
            apply Turing.Tape.ext
            intro i
            by_cases h_pos : i = 0
            · rw [h_pos, Turing.Tape.write_nth]
              simp
              exact h_current
            · rw [Turing.Tape.write_nth]
              simp [h_pos]
          simp only [encode_config, LeftwardTape.write]
          rw [h_write_eq]
        exact h_change h_no_change
      · -- Writing false over true: decreases by 2^k
        right


        cases h_pow with
        | inl h_pos =>
          -- Positive difference contradicts the fact that writing false over true decreases
          exfalso
          have h_a_false : a = false := by
            cases a with
            | false => rfl
            | true => exfalso; exact h_new rfl
          have h_decrease : (cfg.tape.write a).encode < cfg.tape.encode := by
            apply encode_strict_decrease_write_false cfg.tape a h_current h_a_false
          -- h_pos says new > old, but h_decrease says new < old
          simp only [encode_config] at h_pos
          have h_increase : encode_config ⟨cfg.q, cfg.tape.write a⟩ > encode_config cfg := by
            have h_pos_pow : (0 : ℤ) < 2^k' := by
              apply pow_pos; norm_num
            have h_eq : (encode_config ⟨cfg.q, cfg.tape.write a⟩ : ℤ) - encode_config cfg = 2^k' := h_pos
            linarith
          simp only [encode_config] at h_decrease h_increase
          linarith
        | inr h_neg =>


          -- We need to use the fact that different powers of 2 are distinct
          have h_unique : ∀ k₁ k₂ : ℕ, -(2^k₁ : ℤ) = -(2^k₂ : ℤ) → k₁ = k₂ := by
            intro k₁ k₂ h_eq
            have : (2^k₁ : ℤ) = 2^k₂ := by linarith
            have h_pos : ∀ n : ℕ, (0 : ℤ) < 2^n := by intro n; simp
            have h_eq_nat : (2^k₁ : ℕ) = 2^k₂ := by
              have h_cast1 : (2^k₁ : ℤ) = ((2^k₁ : ℕ) : ℤ) := by norm_cast
              have h_cast2 : (2^k₂ : ℤ) = ((2^k₂ : ℕ) : ℤ) := by norm_cast
              rw [h_cast1, h_cast2] at this
              exact Nat.cast_injective this
            have h_lt : 1 < 2 := by omega
            exact Nat.pow_right_injective h_lt h_eq_nat


          have h_a_false : a = false := by
            cases a with
            | false => rfl
            | true => exfalso; exact h_new rfl


          sorry
    · -- Current value is false
      by_cases h_new : a = false
      · -- Writing false over false: no change
        exfalso
        have h_no_change : encode_config ⟨cfg.q, cfg.tape.write a⟩ = encode_config cfg := by
          have h_write_eq : cfg.tape.tape.write a = cfg.tape.tape := by
            rw [h_new]
            apply Turing.Tape.ext
            intro i
            by_cases h_pos : i = 0
            · rw [h_pos, Turing.Tape.write_nth]
              simp
              -- We need to show cfg.tape.tape.head = false
              -- We have h_current : ¬(current_val = true) where current_val = cfg.tape.nth 0
              have : current_val = false := by
                cases h_eq : current_val
                · rfl
                · rw [h_eq] at h_current
                  simp at h_current
              simp only [nth, LeftwardTape.read] at this
              exact this
            · rw [Turing.Tape.write_nth]
              simp [h_pos]
          simp only [encode_config, LeftwardTape.write]
          rw [h_write_eq]
        exact h_change h_no_change
      · -- Writing true over false: increases by 2^k
        left

        cases h_pow with
        | inl h_pos =>

          have h_unique : ∀ k₁ k₂ : ℕ, (2^k₁ : ℤ) = (2^k₂ : ℤ) → k₁ = k₂ := by
            intro k₁ k₂ h_eq
            have h_pos : ∀ n : ℕ, (0 : ℤ) < 2^n := by intro n; simp
            have h_eq_nat : (2^k₁ : ℕ) = 2^k₂ := by
              have h_cast1 : (2^k₁ : ℤ) = ((2^k₁ : ℕ) : ℤ) := by norm_cast
              have h_cast2 : (2^k₂ : ℤ) = ((2^k₂ : ℕ) : ℤ) := by norm_cast
              rw [h_cast1, h_cast2] at h_eq
              exact Nat.cast_injective h_eq
            have h_lt : 1 < 2 := by omega
            exact Nat.pow_right_injective h_lt h_eq_nat

          -- Establish the values we're working with
          have h_current_false : current_val = false := by
            cases h_eq : current_val
            · rfl
            · rw [h_eq] at h_current
              simp at h_current
          have h_a_true : a = true := by
            cases a with
            | false => exfalso; exact h_new rfl
            | true => rfl


          sorry
        | inr h_neg =>
          -- Negative difference contradicts the fact that writing true over false increases
          exfalso
          have h_current_false : current_val = false := by
            cases h_eq : current_val
            · rfl
            · rw [h_eq] at h_current
              simp at h_current
          have h_a_true : a = true := by
            cases a with
            | false => exfalso; exact h_new rfl
            | true => rfl
          have h_increase : cfg.tape.encode < (cfg.tape.write a).encode := by
            apply encode_strict_increase_write_true cfg.tape a h_current_false h_a_true
          -- h_neg says new < old, but h_increase says new > old
          simp only [encode_config] at h_neg
          have h_decrease : encode_config ⟨cfg.q, cfg.tape.write a⟩ < encode_config cfg := by
            have h_neg_pow : -(2^k' : ℤ) < 0 := by
              simp
            have h_eq : (encode_config ⟨cfg.q, cfg.tape.write a⟩ : ℤ) - encode_config cfg = -(2^k' : ℤ) := h_neg
            linarith
          simp only [encode_config] at h_increase h_decrease
          linarith

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
          -- h_result has the correct form but the left case uses natural subtraction
          -- We need to convert it to use integer subtraction
          cases h_result with
          | inl h_zero =>
            -- Natural difference is 0, so encodings must be ≤
            -- But from the structure of encode_diff_at_write, they're actually equal
            left
            have h_le : ((steps M t init_cfg).tape.write a).encode ≤ (steps M t init_cfg).tape.encode := by
              rw [← tsub_eq_zero_iff_le]
              exact h_zero
            -- When natural subtraction is 0, either equal or first < second
            -- But if first < second, encode_diff_at_write would return right with -2^k
            -- Since we're in left case, they must be equal
            have h_eq : ((steps M t init_cfg).tape.write a).encode = (steps M t init_cfg).tape.encode := by
              by_contra h_ne
              have h_lt : ((steps M t init_cfg).tape.write a).encode < (steps M t init_cfg).tape.encode := by
                exact Nat.lt_of_le_of_ne h_le h_ne

              -- Use our helper lemma to get equality
              have h_eq' := encode_diff_at_write_eq_of_zero (steps M t init_cfg)
                            ⟨(steps M t init_cfg).q, (steps M t init_cfg).tape.write a⟩
                            ⟨a, rfl⟩ h_zero
              simp only [encode_config] at h_eq'
              -- But we assumed h_ne, contradiction
              exact absurd h_eq' h_ne
            simp [h_eq]
          | inr h_exists =>
            right
            exact h_exists



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

      -- a write operation at the current head position
      unfold sequence_difference sequence at h_pow


      -- First, let's show uniqueness of k for powers of 2
      have h_unique : ∀ k₁ k₂ : ℕ, (2^k₁ : ℤ) = 2^k₂ → k₁ = k₂ := by
        intro k₁ k₂ h_eq
        have h_pos : ∀ n : ℕ, (0 : ℤ) < 2^n := by intro n; simp
        have h_eq_nat : (2^k₁ : ℕ) = 2^k₂ := by
          -- Convert from integers to naturals
          have h_cast1 : (2^k₁ : ℤ) = ((2^k₁ : ℕ) : ℤ) := by norm_cast
          have h_cast2 : (2^k₂ : ℤ) = ((2^k₂ : ℕ) : ℤ) := by norm_cast
          rw [h_cast1, h_cast2] at h_eq
          exact Nat.cast_injective h_eq
        have h_lt : 1 < 2 := by omega
        exact Nat.pow_right_injective h_lt h_eq_nat

      -- Similarly for negative powers
      have h_unique_neg : ∀ k₁ k₂ : ℕ, -(2^k₁ : ℤ) = -(2^k₂ : ℤ) → k₁ = k₂ := by
        intro k₁ k₂ h_eq
        have : (2^k₁ : ℤ) = 2^k₂ := by linarith
        exact h_unique k₁ k₂ this

      sorry  -- This requires a more careful analysis of the proof term

/-- The k value is bounded by the step number -/
lemma sequence_k_bound (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ)
    (h_init : init_cfg.tape.head_pos = 0) :
    ∀ k : ℕ, (sequence_difference (sequence M init_cfg) t = 2^k ∨
               sequence_difference (sequence M init_cfg) t = -(2^k : ℤ)) →
    k ≤ t := by
  intro k hk


  -- Get the head position bound
  have h_bound := head_pos_bound M init_cfg t
  rw [h_init] at h_bound
  -- h_bound : (steps M t init_cfg).tape.head_pos ≥ 0 - t
  simp at h_bound
  -- h_bound : (steps M t init_cfg).tape.head_pos ≥ -↑t

  -- The head position is always ≤ 0 for LeftwardTape
  have h_nonpos := (steps M t init_cfg).tape.head_nonpos

  have h_pos_neg : 0 ≤ -(steps M t init_cfg).tape.head_pos := by linarith
  have h_pos_bound : -(steps M t init_cfg).tape.head_pos ≤ t := by linarith

  -- The key fact: when sequence_difference = ±2^k, the k equals Int.natAbs(-head_pos)

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
        sorry
  -- 6. Therefore |k_j - k_i| ≤ j - i

end LeftTM0
