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

/-- Writing the same value doesn't change encoding -/
lemma encode_same_value_zero_diff (cfg : Cfg Bool Λ) (a : Bool)
    (h_same : cfg.tape.nth 0 = a) :
    encode_diff cfg ⟨cfg.q, cfg.tape.write a⟩ = 0 := by
  -- Writing the same value doesn't change the encoding
  unfold encode_diff
  simp only [encode_config]
  -- When we write the same value, the encoding stays the same
  have h_eq : (cfg.tape.write a).encode = cfg.tape.encode := by
    -- First, let's understand what write does to the underlying tape
    -- cfg.tape.write a = { cfg.tape with tape := cfg.tape.tape.write a }
    -- And from h_same: cfg.tape.nth 0 = a means cfg.tape.tape.nth 0 = a
    -- Since tape.nth 0 = tape.head, we have cfg.tape.tape.head = a

    -- The key insight: write a when tape.head = a preserves the tape
    have h_tape_head : cfg.tape.tape.head = a := by
      have : cfg.tape.tape.nth 0 = a := h_same
      rwa [Turing.Tape.nth_zero] at this

    -- Use Turing.Tape.write_self: T.write T.head = T
    have h_write_self : cfg.tape.tape.write a = cfg.tape.tape := by
      rw [← h_tape_head]
      exact Turing.Tape.write_self cfg.tape.tape

    -- Now the encodings are equal because the tapes are equal
    unfold LeftwardTape.write
    simp [h_write_self]
  rw [h_eq]
  simp

/-- The difference in encoding when writing at a position is ±2^k where k is the absolute position -/
lemma encode_diff_at_write (cfg : Cfg Bool Λ) (a : Bool) :
    let cfg' := ⟨cfg.q, cfg.tape.write a⟩
    let diff := encode_diff cfg cfg'
    diff = 0 ∨ ∃ k : ℕ, diff = 2^k ∨ diff = -(2^k : ℤ) := by
  -- Case split on whether we're writing the same value or not
  by_cases h : cfg.tape.nth 0 = a
  case pos =>
    -- Writing same value: no change
    left
    unfold encode_diff encode_config
    have h_same : (cfg.tape.write a).encode = cfg.tape.encode := by
      -- Use encode_same_value_zero_diff
      have h_zero_diff := encode_same_value_zero_diff cfg a h
      unfold encode_diff at h_zero_diff
      simp only [encode_config] at h_zero_diff
      -- h_zero_diff gives us the equality with integer casts
      have h_eq : ((cfg.tape.write a).encode : ℤ) = (cfg.tape.encode : ℤ) := by linarith
      exact Nat.cast_injective h_eq
    simp [h_same]
  case neg =>
    -- Writing different value: change by ±2^|head_pos|
    right
    use Int.natAbs (-cfg.tape.head_pos)
    unfold encode_diff encode_config
    -- Case split on what value we're writing
    cases ha : a
    case false =>
      -- Writing false, so current value must be true
      right
      have h_true : cfg.tape.nth 0 = true := by
        cases h_tape : cfg.tape.nth 0
        · -- If current is false and a is false, then cfg.tape.nth 0 = a
          rw [ha] at h
          contradiction
        · rfl
      -- The encoding decreases by 2^|head_pos|
      have h_dec : cfg.tape.encode = (cfg.tape.write false).encode + 2^(Int.natAbs (-cfg.tape.head_pos)) := by
        -- We'll inline the logic from encode_strict_decrease_write_false
        unfold LeftwardTape.encode
        -- Show that cfg.tape.head_pos is in cfg.tape.true_positions_absolute
        have h_mem : cfg.tape.head_pos ∈ cfg.tape.true_positions_absolute := by
          unfold LeftwardTape.true_positions_absolute
          simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
                     LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
          refine ⟨?_, cfg.tape.head_nonpos, ?_⟩
          · simp only [sub_self, LeftwardTape.nth]
            have : cfg.tape.tape.nth 0 = true := h_true
            rw [this]
            simp
          · simp only [sub_self, LeftwardTape.nth]
            exact h_true
        -- Split the sum
        have h_split : cfg.tape.true_positions_absolute =
                      (cfg.tape.true_positions_absolute \ {cfg.tape.head_pos}) ∪ {cfg.tape.head_pos} := by
          ext x
          simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
          by_cases h : x = cfg.tape.head_pos
          · simp [h, h_mem]
          · simp [h]
        -- After writing false, cfg.tape.head_pos is removed
        have h_after : (cfg.tape.write false).true_positions_absolute =
                      cfg.tape.true_positions_absolute \ {cfg.tape.head_pos} := by
          ext i
          simp only [Finset.mem_sdiff, Finset.mem_singleton]
          unfold LeftwardTape.true_positions_absolute
          simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
                     LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
          constructor
          · intro ⟨h_ne_def, h_le, h_true_after⟩
            unfold LeftwardTape.write at h_ne_def h_true_after
            simp only [LeftwardTape.nth] at h_ne_def h_true_after
            constructor
            · refine ⟨?_, h_le, ?_⟩
              · by_cases h : i - cfg.tape.head_pos = 0
                · have : i = cfg.tape.head_pos := by linarith
                  rw [this] at h_true_after
                  simp only [sub_self] at h_true_after
                  rw [Turing.Tape.write_nth] at h_true_after
                  simp at h_true_after
                · rw [Turing.Tape.write_nth] at h_ne_def
                  simp [h] at h_ne_def
                  have h_true_before : cfg.tape.tape.nth (i - cfg.tape.head_pos) = true := by
                    rw [Turing.Tape.write_nth] at h_true_after
                    simp [h] at h_true_after
                    exact h_true_after
                  rw [h_true_before]
                  simp
              · by_cases h : i - cfg.tape.head_pos = 0
                · have : i = cfg.tape.head_pos := by linarith
                  rw [this] at h_true_after
                  simp only [sub_self] at h_true_after
                  rw [Turing.Tape.write_nth] at h_true_after
                  simp at h_true_after
                · rw [Turing.Tape.write_nth] at h_true_after
                  simp [h] at h_true_after
                  exact h_true_after
            · intro h_eq
              rw [h_eq] at h_true_after
              simp only [sub_self] at h_true_after
              rw [Turing.Tape.write_nth] at h_true_after
              simp at h_true_after
          · intro ⟨⟨h_ne_def, h_le, h_true_orig⟩, h_ne⟩
            refine ⟨?_, h_le, ?_⟩
            · unfold LeftwardTape.write
              simp only [LeftwardTape.nth]
              rw [Turing.Tape.write_nth]
              have : i - cfg.tape.head_pos ≠ 0 := fun h => h_ne (by linarith : i = cfg.tape.head_pos)
              simp [this, h_true_orig]
            · unfold LeftwardTape.write
              simp only [LeftwardTape.nth]
              rw [Turing.Tape.write_nth]
              have : i - cfg.tape.head_pos ≠ 0 := fun h => h_ne (by linarith : i = cfg.tape.head_pos)
              simp [this, h_true_orig]
        -- Complete the calculation
        rw [h_split]
        have h_disjoint : Disjoint (cfg.tape.true_positions_absolute \ {cfg.tape.head_pos}) {cfg.tape.head_pos} :=
          Finset.sdiff_disjoint
        rw [Finset.sum_union h_disjoint, ← h_after, Finset.sum_singleton, add_comm]
      -- We need to show: (cfg.tape.write false).encode - cfg.tape.encode = -2^k
      have : (↑(cfg.tape.write false).encode : ℤ) - (↑cfg.tape.encode : ℤ) = -(2^(Int.natAbs (-cfg.tape.head_pos)) : ℤ) := by
        rw [h_dec]
        simp
      exact this
    case true =>
      -- Writing true, so current value must be false
      left
      have h_false : cfg.tape.nth 0 = false := by
        cases h_tape : cfg.tape.nth 0
        · rfl
        · -- If current is true and a is true, then cfg.tape.nth 0 = a
          rw [ha] at h
          contradiction
      -- The encoding increases by 2^|head_pos|
      have h_inc : (cfg.tape.write true).encode = cfg.tape.encode + 2^(Int.natAbs (-cfg.tape.head_pos)) := by
        -- We'll inline the logic from encode_strict_increase_write_true
        unfold LeftwardTape.encode
        -- Show that cfg.tape.head_pos is not in cfg.tape.true_positions_absolute
        have h_not_mem : cfg.tape.head_pos ∉ cfg.tape.true_positions_absolute := by
          unfold LeftwardTape.true_positions_absolute
          simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
                     LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
          intro ⟨_, _, h_true⟩
          simp only [sub_self, LeftwardTape.nth] at h_true
          have : cfg.tape.tape.nth 0 = false := h_false
          rw [this] at h_true
          simp at h_true
        -- After writing true, cfg.tape.head_pos is added
        have h_after : (cfg.tape.write true).true_positions_absolute =
                      cfg.tape.true_positions_absolute ∪ {cfg.tape.head_pos} := by
          ext i
          simp only [Finset.mem_union, Finset.mem_singleton]
          unfold LeftwardTape.true_positions_absolute
          simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
                     LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
          constructor
          · intro ⟨h_ne_def, h_le, h_true_after⟩
            unfold LeftwardTape.write at h_ne_def h_true_after
            simp only [LeftwardTape.nth] at h_ne_def h_true_after
            by_cases h : i = cfg.tape.head_pos
            · right; exact h
            · left
              refine ⟨?_, h_le, ?_⟩
              · rw [Turing.Tape.write_nth] at h_ne_def
                split_ifs at h_ne_def with h_eq
                · have : i = cfg.tape.head_pos := by linarith
                  contradiction
                · exact h_ne_def
              · rw [Turing.Tape.write_nth] at h_true_after
                split_ifs at h_true_after with h_eq
                · have : i = cfg.tape.head_pos := by linarith
                  contradiction
                · exact h_true_after
          · intro h
            cases h with
            | inl h_in_orig =>
              obtain ⟨h_ne_def, h_le, h_true_orig⟩ := h_in_orig
              refine ⟨?_, h_le, ?_⟩
              · unfold LeftwardTape.write
                simp only [LeftwardTape.nth]
                rw [Turing.Tape.write_nth]
                have : i - cfg.tape.head_pos ≠ 0 := by
                  intro h_eq
                  have : i = cfg.tape.head_pos := by linarith
                  rw [this] at h_true_orig
                  simp only [sub_self, LeftwardTape.nth] at h_true_orig
                  have h_false' : cfg.tape.tape.nth 0 = false := h_false
                  rw [h_false'] at h_true_orig
                  simp at h_true_orig
                simp [this, h_true_orig]
              · unfold LeftwardTape.write
                simp only [LeftwardTape.nth]
                rw [Turing.Tape.write_nth]
                have : i - cfg.tape.head_pos ≠ 0 := by
                  intro h_eq
                  have : i = cfg.tape.head_pos := by linarith
                  rw [this] at h_true_orig
                  simp only [sub_self, LeftwardTape.nth] at h_true_orig
                  have h_false' : cfg.tape.tape.nth 0 = false := h_false
                  rw [h_false'] at h_true_orig
                  simp at h_true_orig
                simp [this, h_true_orig]
            | inr h_eq =>
              rw [h_eq]
              refine ⟨?_, cfg.tape.head_nonpos, ?_⟩
              · unfold LeftwardTape.write
                simp only [sub_self, LeftwardTape.nth]
                rw [Turing.Tape.write_nth]
                simp
              · unfold LeftwardTape.write
                simp only [sub_self, LeftwardTape.nth]
                rw [Turing.Tape.write_nth]
                simp
        -- Complete the calculation
        rw [h_after]
        have h_disjoint : Disjoint cfg.tape.true_positions_absolute {cfg.tape.head_pos} := by
          rw [Finset.disjoint_singleton_right]
          exact h_not_mem
        rw [Finset.sum_union h_disjoint, Finset.sum_singleton, add_comm]
      -- We need to show: (cfg.tape.write true).encode - cfg.tape.encode = 2^k
      have : (↑(cfg.tape.write true).encode : ℤ) - (↑cfg.tape.encode : ℤ) = (2^(Int.natAbs (-cfg.tape.head_pos)) : ℤ) := by
        rw [h_inc]
        simp
      exact this

/-- Writing false over true strictly decreases the encoding -/
lemma encode_strict_decrease_write_false (tape : LeftwardTape Bool)
    (h_pos : tape.head_pos ≤ 0)
    (h_true : tape.nth 0 = true) :
    (tape.write false).encode < tape.encode := by
  -- Strategy: show tape.encode = (tape.write false).encode + 2^|tape.head_pos|
  have h_eq : tape.encode = (tape.write false).encode + 2^(Int.natAbs (-tape.head_pos)) := by
    unfold LeftwardTape.encode

    -- Show tape.head_pos is in tape.true_positions_absolute
    have h_mem : tape.head_pos ∈ tape.true_positions_absolute := by
      unfold LeftwardTape.true_positions_absolute
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
                 LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
      refine ⟨?_, h_pos, ?_⟩
      · -- Show tape.tape.nth 0 ≠ default
        simp only [sub_self, LeftwardTape.nth]
        have : tape.tape.nth 0 = true := h_true
        rw [this]
        simp
      · -- Show tape.tape.nth 0 = true
        simp only [sub_self, LeftwardTape.nth]
        exact h_true

    -- Split the sum into tape.head_pos and everything else
    have h_split : tape.true_positions_absolute =
                  (tape.true_positions_absolute \ {tape.head_pos}) ∪ {tape.head_pos} := by
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
      by_cases h : x = tape.head_pos
      · simp [h, h_mem]
      · simp [h]

    -- Show that after writing false, true_positions_absolute loses tape.head_pos
    have h_after : (tape.write false).true_positions_absolute =
                  tape.true_positions_absolute \ {tape.head_pos} := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      unfold LeftwardTape.true_positions_absolute
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
                 LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
      constructor
      · intro ⟨h_ne_def, h_le, h_true_after⟩
        unfold LeftwardTape.write at h_ne_def h_true_after
        simp only [LeftwardTape.nth] at h_ne_def h_true_after
        constructor
        · refine ⟨?_, h_le, ?_⟩
          · by_cases h : i - tape.head_pos = 0
            · have : i = tape.head_pos := by linarith
              rw [this] at h_true_after
              simp only [sub_self] at h_true_after
              rw [Turing.Tape.write_nth] at h_true_after
              simp at h_true_after
            · rw [Turing.Tape.write_nth] at h_ne_def
              simp [h] at h_ne_def
              -- h_ne_def : tape.tape.nth (i - tape.head_pos) ≠ default
              have h_true_before : tape.tape.nth (i - tape.head_pos) = true := by
                rw [Turing.Tape.write_nth] at h_true_after
                simp [h] at h_true_after
                exact h_true_after
              rw [h_true_before]
              simp
          · by_cases h : i - tape.head_pos = 0
            · have : i = tape.head_pos := by linarith
              rw [this] at h_true_after
              simp only [sub_self] at h_true_after
              rw [Turing.Tape.write_nth] at h_true_after
              simp at h_true_after
            · rw [Turing.Tape.write_nth] at h_true_after
              simp [h] at h_true_after
              exact h_true_after

        · intro h_eq
          rw [h_eq] at h_true_after
          simp only [sub_self] at h_true_after
          rw [Turing.Tape.write_nth] at h_true_after
          simp at h_true_after
      · intro ⟨⟨h_ne_def, h_le, h_true_orig⟩, h_ne⟩
        refine ⟨?_, h_le, ?_⟩
        · unfold LeftwardTape.write
          simp only [LeftwardTape.nth]
          rw [Turing.Tape.write_nth]
          have : i - tape.head_pos ≠ 0 := fun h => h_ne (by linarith : i = tape.head_pos)
          simp [this, h_true_orig]
        · unfold LeftwardTape.write
          simp only [LeftwardTape.nth]
          rw [Turing.Tape.write_nth]
          have : i - tape.head_pos ≠ 0 := fun h => h_ne (by linarith : i = tape.head_pos)
          simp [this, h_true_orig]

    -- Complete the calculation
    rw [h_split]
    have h_disjoint : Disjoint (tape.true_positions_absolute \ {tape.head_pos}) {tape.head_pos} :=
      Finset.sdiff_disjoint
    rw [Finset.sum_union h_disjoint, ← h_after, Finset.sum_singleton, add_comm]

  -- The inequality follows
  rw [h_eq]
  simp [Nat.pow_pos Nat.zero_lt_two]

/-- Writing true over false strictly increases the encoding -/
lemma encode_strict_increase_write_true (tape : LeftwardTape Bool)
    (h_pos : tape.head_pos ≤ 0)
    (h_false : tape.nth 0 = false) :
    tape.encode < (tape.write true).encode := by
  -- Strategy: show (tape.write true).encode = tape.encode + 2^|tape.head_pos|
  have h_eq : (tape.write true).encode = tape.encode + 2^(Int.natAbs (-tape.head_pos)) := by
    unfold LeftwardTape.encode

    -- Show tape.head_pos is not in tape.true_positions_absolute
    have h_not_mem : tape.head_pos ∉ tape.true_positions_absolute := by
      unfold LeftwardTape.true_positions_absolute
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
                 LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
      intro ⟨_, _, h_true⟩
      simp only [sub_self, LeftwardTape.nth] at h_true
      have : tape.tape.nth 0 = false := h_false
      rw [this] at h_true
      simp at h_true

    -- Show that after writing true, true_positions_absolute gains tape.head_pos
    have h_after : (tape.write true).true_positions_absolute =
                  tape.true_positions_absolute ∪ {tape.head_pos} := by
      ext i
      simp only [Finset.mem_union, Finset.mem_singleton]
      unfold LeftwardTape.true_positions_absolute
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
                 LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
      constructor
      · intro ⟨h_ne_def, h_le, h_true_after⟩
        unfold LeftwardTape.write at h_ne_def h_true_after
        simp only [LeftwardTape.nth] at h_ne_def h_true_after
        by_cases h : i = tape.head_pos
        · right; exact h
        · left
          refine ⟨?_, h_le, ?_⟩
          · -- Show original has i in support
            rw [Turing.Tape.write_nth] at h_ne_def
            split_ifs at h_ne_def with h_eq
            · have : i = tape.head_pos := by linarith
              contradiction
            · exact h_ne_def
          · -- Show original has true at i
            rw [Turing.Tape.write_nth] at h_true_after
            split_ifs at h_true_after with h_eq
            · have : i = tape.head_pos := by linarith
              contradiction
            · exact h_true_after
      · intro h
        cases h with
        | inl h_in_orig =>
          obtain ⟨h_ne_def, h_le, h_true_orig⟩ := h_in_orig
          refine ⟨?_, h_le, ?_⟩
          · unfold LeftwardTape.write
            simp only [LeftwardTape.nth]
            rw [Turing.Tape.write_nth]
            have : i - tape.head_pos ≠ 0 := by
              intro h_eq
              have : i = tape.head_pos := by linarith
              rw [this] at h_true_orig
              simp only [sub_self, LeftwardTape.nth] at h_true_orig
              have h_false' : tape.tape.nth 0 = false := h_false
              rw [h_false'] at h_true_orig
              simp at h_true_orig
            simp [this, h_true_orig]
          · unfold LeftwardTape.write
            simp only [LeftwardTape.nth]
            rw [Turing.Tape.write_nth]
            have : i - tape.head_pos ≠ 0 := by
              intro h_eq
              have : i = tape.head_pos := by linarith
              rw [this] at h_true_orig
              simp only [sub_self, LeftwardTape.nth] at h_true_orig
              have h_false' : tape.tape.nth 0 = false := h_false
              rw [h_false'] at h_true_orig
              simp at h_true_orig
            simp [this, h_true_orig]
        | inr h_eq =>
          rw [h_eq]
          refine ⟨?_, h_pos, ?_⟩
          · unfold LeftwardTape.write
            simp only [sub_self, LeftwardTape.nth]
            rw [Turing.Tape.write_nth]
            simp
          · unfold LeftwardTape.write
            simp only [sub_self, LeftwardTape.nth]
            rw [Turing.Tape.write_nth]
            simp

    -- Complete the calculation
    rw [h_after]
    have h_disjoint : Disjoint tape.true_positions_absolute {tape.head_pos} := by
      rw [Finset.disjoint_singleton_right]
      exact h_not_mem
    rw [Finset.sum_union h_disjoint, Finset.sum_singleton, add_comm]

  -- The inequality follows
  rw [h_eq]
  simp [Nat.pow_pos Nat.zero_lt_two]

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

/-- Helper lemma: writing false over true gives the encoding equation -/
lemma encode_eq_write_false_plus_power (tape : LeftwardTape Bool)
    (h_pos : tape.head_pos ≤ 0)
    (h_true : tape.nth 0 = true) :
    tape.encode = (tape.write false).encode + 2^(Int.natAbs (-tape.head_pos)) := by
  -- This is extracted from the proof of encode_strict_decrease_write_false
  unfold LeftwardTape.encode
  -- Show tape.head_pos is in tape.true_positions_absolute
  have h_mem : tape.head_pos ∈ tape.true_positions_absolute := by
    unfold LeftwardTape.true_positions_absolute
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
               LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
    refine ⟨?_, h_pos, ?_⟩
    · simp only [sub_self, LeftwardTape.nth]
      have : tape.tape.nth 0 = true := h_true
      rw [this]
      simp
    · simp only [sub_self, LeftwardTape.nth]
      exact h_true
  -- Split the sum
  have h_split : tape.true_positions_absolute =
                (tape.true_positions_absolute \ {tape.head_pos}) ∪ {tape.head_pos} := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
    by_cases h : x = tape.head_pos
    · simp [h, h_mem]
    · simp [h]
  -- After writing false, tape.head_pos is removed
  have h_after : (tape.write false).true_positions_absolute =
                tape.true_positions_absolute \ {tape.head_pos} := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    unfold LeftwardTape.true_positions_absolute
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
               LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
    constructor
    · intro ⟨h_ne_def, h_le, h_true_after⟩
      unfold LeftwardTape.write at h_ne_def h_true_after
      simp only [LeftwardTape.nth] at h_ne_def h_true_after
      constructor
      · refine ⟨?_, h_le, ?_⟩
        · by_cases h : i - tape.head_pos = 0
          · have : i = tape.head_pos := by linarith
            rw [this] at h_true_after
            simp only [sub_self] at h_true_after
            rw [Turing.Tape.write_nth] at h_true_after
            simp at h_true_after
          · rw [Turing.Tape.write_nth] at h_ne_def
            simp [h] at h_ne_def
            have h_true_before : tape.tape.nth (i - tape.head_pos) = true := by
              rw [Turing.Tape.write_nth] at h_true_after
              simp [h] at h_true_after
              exact h_true_after
            rw [h_true_before]
            simp
        · by_cases h : i - tape.head_pos = 0
          · have : i = tape.head_pos := by linarith
            rw [this] at h_true_after
            simp only [sub_self] at h_true_after
            rw [Turing.Tape.write_nth] at h_true_after
            simp at h_true_after
          · rw [Turing.Tape.write_nth] at h_true_after
            simp [h] at h_true_after
            exact h_true_after
      · intro h_eq
        rw [h_eq] at h_true_after
        simp only [sub_self] at h_true_after
        rw [Turing.Tape.write_nth] at h_true_after
        simp at h_true_after
    · intro ⟨⟨h_ne_def, h_le, h_true_orig⟩, h_ne⟩
      refine ⟨?_, h_le, ?_⟩
      · unfold LeftwardTape.write
        simp only [LeftwardTape.nth]
        rw [Turing.Tape.write_nth]
        have : i - tape.head_pos ≠ 0 := fun h => h_ne (by linarith : i = tape.head_pos)
        simp [this, h_true_orig]
      · unfold LeftwardTape.write
        simp only [LeftwardTape.nth]
        rw [Turing.Tape.write_nth]
        have : i - tape.head_pos ≠ 0 := fun h => h_ne (by linarith : i = tape.head_pos)
        simp [this, h_true_orig]
  -- Complete the calculation
  rw [h_split]
  have h_disjoint : Disjoint (tape.true_positions_absolute \ {tape.head_pos}) {tape.head_pos} :=
    Finset.sdiff_disjoint
  rw [Finset.sum_union h_disjoint, ← h_after, Finset.sum_singleton, add_comm]

/-- Helper lemma: writing true over false gives the encoding equation -/
lemma encode_eq_write_true_minus_power (tape : LeftwardTape Bool)
    (h_pos : tape.head_pos ≤ 0)
    (h_false : tape.nth 0 = false) :
    (tape.write true).encode = tape.encode + 2^(Int.natAbs (-tape.head_pos)) := by
  -- This is extracted from the proof of encode_strict_increase_write_true
  unfold LeftwardTape.encode
  -- Show tape.head_pos is not in tape.true_positions_absolute
  have h_not_mem : tape.head_pos ∉ tape.true_positions_absolute := by
    unfold LeftwardTape.true_positions_absolute
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
               LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
    intro ⟨_, _, h_true⟩
    simp only [sub_self, LeftwardTape.nth] at h_true
    have : tape.tape.nth 0 = false := h_false
    rw [this] at h_true
    simp at h_true
  -- After writing true, tape.head_pos is added
  have h_after : (tape.write true).true_positions_absolute =
                tape.true_positions_absolute ∪ {tape.head_pos} := by
    ext i
    simp only [Finset.mem_union, Finset.mem_singleton]
    unfold LeftwardTape.true_positions_absolute
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf,
               LeftwardTape.has_content_at_absolute, LeftwardTape.nth_absolute]
    constructor
    · intro ⟨h_ne_def, h_le, h_true_after⟩
      unfold LeftwardTape.write at h_ne_def h_true_after
      simp only [LeftwardTape.nth] at h_ne_def h_true_after
      by_cases h : i = tape.head_pos
      · right; exact h
      · left
        refine ⟨?_, h_le, ?_⟩
        · rw [Turing.Tape.write_nth] at h_ne_def
          split_ifs at h_ne_def with h_eq
          · have : i = tape.head_pos := by linarith
            contradiction
          · exact h_ne_def
        · rw [Turing.Tape.write_nth] at h_true_after
          split_ifs at h_true_after with h_eq
          · have : i = tape.head_pos := by linarith
            contradiction
          · exact h_true_after
    · intro h
      cases h with
      | inl h_in_orig =>
        obtain ⟨h_ne_def, h_le, h_true_orig⟩ := h_in_orig
        refine ⟨?_, h_le, ?_⟩
        · unfold LeftwardTape.write
          simp only [LeftwardTape.nth]
          rw [Turing.Tape.write_nth]
          have : i - tape.head_pos ≠ 0 := by
            intro h_eq
            have : i = tape.head_pos := by linarith
            rw [this] at h_true_orig
            simp only [sub_self, LeftwardTape.nth] at h_true_orig
            have h_false' : tape.tape.nth 0 = false := h_false
            rw [h_false'] at h_true_orig
            simp at h_true_orig
          simp [this, h_true_orig]
        · unfold LeftwardTape.write
          simp only [LeftwardTape.nth]
          rw [Turing.Tape.write_nth]
          have : i - tape.head_pos ≠ 0 := by
            intro h_eq
            have : i = tape.head_pos := by linarith
            rw [this] at h_true_orig
            simp only [sub_self, LeftwardTape.nth] at h_true_orig
            have h_false' : tape.tape.nth 0 = false := h_false
            rw [h_false'] at h_true_orig
            simp at h_true_orig
          simp [this, h_true_orig]
      | inr h_eq =>
        rw [h_eq]
        refine ⟨?_, h_pos, ?_⟩
        · unfold LeftwardTape.write
          simp only [sub_self, LeftwardTape.nth]
          rw [Turing.Tape.write_nth]
          simp
        · unfold LeftwardTape.write
          simp only [sub_self, LeftwardTape.nth]
          rw [Turing.Tape.write_nth]
          simp
  -- Complete the calculation
  rw [h_after]
  have h_disjoint : Disjoint tape.true_positions_absolute {tape.head_pos} := by
    rw [Finset.disjoint_singleton_right]
    exact h_not_mem
  rw [Finset.sum_union h_disjoint, Finset.sum_singleton, add_comm]

end BinaryStepSequences

end LeftTM0
