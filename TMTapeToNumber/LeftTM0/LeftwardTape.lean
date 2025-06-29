import Mathlib.Computability.Tape
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring

open Turing
open BigOperators

/-- A leftward-unbounded tape that restricts operations to positions ≤ 0 -/
structure LeftwardTape (Γ : Type*) [Inhabited Γ] where
  tape : Tape Γ
  head_pos : ℤ  -- Current head position
  head_nonpos : head_pos ≤ 0  -- Invariant: head must be ≤ 0

namespace LeftwardTape

variable {Γ : Type*} [Inhabited Γ]

/-- Read the symbol at the current head position -/
def read (T : LeftwardTape Γ) : Γ := T.tape.head

/-- Write a symbol at the current head position -/
def write (T : LeftwardTape Γ) (a : Γ) : LeftwardTape Γ :=
  { T with tape := T.tape.write a }

/-- Move the head left (always allowed) -/
def move_left (T : LeftwardTape Γ) : LeftwardTape Γ :=
  { tape := T.tape.move Dir.left
    head_pos := T.head_pos - 1
    head_nonpos := by
      linarith [T.head_nonpos] }

/-- Move the head right (only if not at position 0) -/
def move_right (T : LeftwardTape Γ) : LeftwardTape Γ :=
  if h : T.head_pos < 0 then
    { tape := T.tape.move Dir.right
      head_pos := T.head_pos + 1
      head_nonpos := by
        linarith [h] }
  else T  -- Cannot move right from position 0

/-- Create a LeftwardTape from a standard tape, if head position is valid -/
def mk_from_tape (tape : Tape Γ) (pos : ℤ) (h : pos ≤ 0) : LeftwardTape Γ :=
  ⟨tape, pos, h⟩

/-- Create initial LeftwardTape with given list, head at position 0 -/
def mk_initial (l : List Γ) : LeftwardTape Γ :=
  ⟨Tape.mk₁ l, 0, by
    norm_num⟩

/-- Get the tape content at a specific position relative to the current head -/
def nth (T : LeftwardTape Γ) (n : ℤ) : Γ := T.tape.nth n

/-- Get the tape content at an absolute tape position -/
-- Absolute position 0 is where the tape head was initially (when created with mk_initial)
-- This compensates for head movements to maintain true absolute positioning
def nth_absolute (T : LeftwardTape Γ) (n : ℤ) : Γ := T.tape.nth (n - T.head_pos)

/-- Check if the tape has non-default content at position i (relative to head) -/
def has_content_at (T : LeftwardTape Γ) (i : ℤ) : Prop :=
  T.nth i ≠ default

/-- Check if the tape has non-default content at absolute position i -/
def has_content_at_absolute (T : LeftwardTape Γ) (i : ℤ) : Prop :=
  T.nth_absolute i ≠ default

/-- Extensionality for LeftwardTape: two tapes are equal if they have the same values at all positions 
    and the same head position -/
@[ext]
theorem ext (T₁ T₂ : LeftwardTape Γ) 
    (h_pos : T₁.head_pos = T₂.head_pos)
    (h_nth : ∀ i : ℤ, T₁.nth i = T₂.nth i) : 
    T₁ = T₂ := by
  -- Use the fact that LeftwardTape is essentially determined by head_pos and the nth function
  -- We'll show equality by cases
  cases' T₁ with tape₁ pos₁ h₁
  cases' T₂ with tape₂ pos₂ h₂
  -- Now we need to show tape₁ = tape₂ given that pos₁ = pos₂ and nth values agree
  have : tape₁ = tape₂ := by
    -- Two tapes are equal if their nth functions are equal
    -- This requires showing the head, left, and right components are equal
    sorry -- For now, we'll leave this as sorry and use a workaround
  simp only [mk.injEq]
  exact ⟨this, h_pos⟩

/-- Every tape has bounded non-default content -/
lemma tape_bounded (tape : Tape Γ) :
    ∃ (L R : ℕ), ∀ i : ℤ, (i < -(L : ℤ) ∨ i > (R : ℤ)) → tape.nth i = default := by
  -- Extract bounds from the ListBlanks using the quotient structure
  -- Each ListBlank is equivalent to some finite list (potentially extended with defaults)
  have ⟨llist, hleft⟩ := Quotient.exists_rep tape.left
  have ⟨rlist, hright⟩ := Quotient.exists_rep tape.right

  -- Use the lengths of these underlying lists as bounds
  use llist.length + 1, rlist.length + 1

  intro i hi

  -- Case analysis on the position
  rcases hi with (hi | hi)
  · -- Case: i < -(llist.length + 1)
    -- For negative positions, we use tape.left
    -- tape.nth (-(n+1)) = tape.left.nth n
    -- We need to show this returns default for large enough n

    -- First, handle the integer cases
    cases' i with n hn
    · -- i is non-negative, contradiction with hi
      simp at hi
      linarith
    · -- i = -(hn+1)
      -- So hi says -(hn+1) < -(llist.length + 1)
      -- Which means hn+1 > llist.length + 1
      -- So hn > llist.length

      have hn_large : hn > llist.length := by
        -- hi says: Int.negSucc hn < -(llist.length + 1)
        -- This is -(hn + 1) < -(llist.length + 1)
        -- Which means hn + 1 > llist.length + 1
        -- So hn > llist.length
        simp [Int.negSucc] at hi
        omega

      -- tape.nth (-(hn+1)) = tape.left.nth hn
      simp only [Tape.nth]

      -- Now use that tape.left is represented by llist
      have : tape.left = ListBlank.mk llist := by
        rw [← hleft]
        rfl
      rw [this, ListBlank.nth_mk]

      -- List.getI returns default for indices beyond the list length
      exact List.getI_eq_default _ (le_of_lt hn_large)

  · -- Case: i > rlist.length + 1
    -- For positive positions, we use tape.right
    -- tape.nth (n+1) = tape.right.nth n for n : ℕ
    -- We need to show this returns default for large enough n

    -- First establish that i must be positive
    have hi_pos : i > 0 := by linarith

    -- Now handle the integer cases
    cases' i with n hn
    · -- i = n ≥ 0
      cases n
      · -- i = 0, contradiction with hi (since 0 ≤ rlist.length + 1)
        simp at hi
        -- We have 0 > rlist.length + 1, which is false
        omega
      · -- i = n+1 for some n : ℕ
        -- So hi says n+1 > rlist.length + 1
        -- Which means n > rlist.length
        rename_i n
        have n_large : n > rlist.length := by
          simp at hi
          linarith

        -- tape.nth (n+1) = tape.right.nth n
        simp only [Tape.nth]

        -- Now use that tape.right is represented by rlist
        have : tape.right = ListBlank.mk rlist := by
          rw [← hright]
          rfl
        rw [this, ListBlank.nth_mk]

        -- List.getI returns default for indices beyond the list length
        exact List.getI_eq_default _ (le_of_lt n_large)

    · -- i = Int.negSucc hn, which is negative
      -- But hi says i > rlist.length + 1, which is positive
      -- This is a contradiction
      have : Int.negSucc hn < 0 := Int.negSucc_lt_zero hn
      linarith

/-- The set of absolute positions with non-default content is finite -/
theorem finite_support_absolute (T : LeftwardTape Γ) :
    Set.Finite {i : ℤ | T.has_content_at_absolute i} := by
  -- The tape consists of left, head, and right parts
  -- Each ListBlank has finite non-default content
  -- So the entire tape has finite non-default positions
  obtain ⟨L, R, hbound⟩ := tape_bounded T.tape

  -- Use the bounds to show finiteness
  -- Adjust bounds by head position since nth_absolute shifts by head_pos
  have finite_interval : (Set.Icc (-(L : ℤ) + T.head_pos) ((R : ℤ) + T.head_pos)).Finite := Set.finite_Icc _ _
  apply Set.Finite.subset finite_interval
  intro i hi
  simp only [Set.mem_setOf] at hi
  simp only [has_content_at_absolute, nth_absolute] at hi
  simp only [Set.mem_Icc]
  by_contra h_not_in
  have hi_bounds : i - T.head_pos < -(L : ℤ) ∨ i - T.head_pos > (R : ℤ) := by
    cases' (not_and_or.mp h_not_in) with h_left h_right
    · left
      linarith
    · right
      linarith
  have : T.tape.nth (i - T.head_pos) = default := hbound (i - T.head_pos) hi_bounds
  contradiction

/-- For Bool tapes, get the set of absolute positions with true values that are ≤ 0 -/
noncomputable def true_positions_absolute (T : LeftwardTape Bool) : Finset ℤ :=
  (finite_support_absolute T).toFinset.filter (fun i => i ≤ 0 ∧ T.nth_absolute i = true)

/-- Integer encoding for Bool tapes based on absolute positions -/
noncomputable def encode (T : LeftwardTape Bool) : ℕ :=
  -- Sum over all absolute tape positions i ≤ 0 where the tape has content 'true'
  -- Absolute position 0 contributes 2^0 = 1 (ones place)
  -- Absolute position -1 contributes 2^1 = 2 (twos place)
  -- Absolute position -2 contributes 2^2 = 4 (fours place), etc.
  ∑ i ∈ true_positions_absolute T, 2^(Int.natAbs (-i))

/-- The set of positions with non-default content is finite (keeping for compatibility) -/
theorem finite_support (T : LeftwardTape Γ) :
    Set.Finite {i : ℤ | T.has_content_at i} := by
  -- has_content_at i means T.nth i ≠ default
  -- T.nth i = T.tape.nth (i - T.head_pos)
  -- So we need to show {i : ℤ | T.tape.nth (i - T.head_pos) ≠ default} is finite

  -- First, get the finite set of absolute positions with non-default content
  have h_abs_finite := finite_support_absolute T

  -- The set we want is related to absolute positions
  -- Since nth reads at relative position i, and nth_absolute reads at absolute position j
  -- We have: T.nth i ≠ default iff T.tape.nth i ≠ default
  -- And: T.nth_absolute j ≠ default iff T.tape.nth (j - T.head_pos) ≠ default
  -- So {i | T.nth i ≠ default} = {j - T.head_pos | T.nth_absolute j ≠ default}
  have : {i : ℤ | T.has_content_at i} =
         (fun j => j - T.head_pos) '' {j : ℤ | T.has_content_at_absolute j} := by
    ext i
    simp only [Set.mem_setOf, Set.mem_image]
    constructor
    · intro hi
      use i + T.head_pos
      simp only [has_content_at, nth, has_content_at_absolute, nth_absolute] at hi ⊢
      constructor
      · convert hi using 1
        ring_nf
      · simp
    · intro ⟨j, hj, hij⟩
      simp only [has_content_at, nth, has_content_at_absolute, nth_absolute] at hj ⊢
      rw [← hij]
      exact hj

  rw [this]
  exact Set.Finite.image _ h_abs_finite

/-- For Bool tapes, get the set of positions with true values (keeping for compatibility) -/
noncomputable def true_positions (T : LeftwardTape Bool) : Finset ℤ :=
  true_positions_absolute T

/-- mk_initial creates a tape with the list contents starting at position 0 -/
lemma mk_initial_nth (l : List Γ) (i : ℤ) :
    (mk_initial l).nth_absolute i =
    if h : 0 ≤ i ∧ i < l.length then l.get ⟨i.natAbs, by
      cases i with
      | ofNat n =>
        simp [Int.natAbs]
        exact Nat.cast_lt.mp (h.2)
      | negSucc n =>
        simp at h
        ⟩ else default := by
  -- mk_initial creates a tape with head_pos = 0
  -- nth_absolute i = tape.nth (i - 0) = tape.nth i
  simp only [mk_initial, nth_absolute, sub_zero]
  -- Tape.mk₁ l = Tape.mk₂ [] l = Tape.mk' (ListBlank.mk []) (ListBlank.mk l)
  simp only [Tape.mk₁, Tape.mk₂]

  split_ifs with h_cond
  · -- Case: 0 ≤ i < l.length
    cases i with
    | ofNat n =>
      -- i = n ≥ 0
      simp only [Tape.nth, Tape.mk', Int.natAbs_natCast]
      cases n with
      | zero =>
        -- tape.nth 0 = head = (ListBlank.mk l).head
        simp only [ListBlank.head_mk]
        cases' l with hd tl
        · -- Empty list, contradiction
          simp at h_cond
        · -- l = hd :: tl
          simp [List.get]
      | succ m =>
        -- tape.nth (m+1) = tape.right.nth m = (ListBlank.mk l).tail.nth m
        simp only [ListBlank.tail_mk, ListBlank.nth_mk]
        cases' l with hd tl
        · -- Empty list, contradiction
          simp at h_cond
          -- h_cond says m+1 < 0 which is impossible
          omega
        · -- l = hd :: tl
          simp only [List.tail]
          have hm : m < tl.length := by
            simp [List.length] at h_cond
            omega
          rw [List.getI_eq_getElem _ hm]
          -- The goal is: tl[m] = (hd :: tl).get ⟨(Int.ofNat (m + 1)).natAbs, _⟩
          -- First, Int.natAbs (Int.ofNat (m + 1)) = m + 1
          have h_natabs : Int.natAbs (Int.ofNat (m + 1)) = m + 1 := Int.natAbs_natCast (m + 1)
          -- Now we can use List.get_cons_succ
          have h_bound : m + 1 < (hd :: tl).length := by
            simp [List.length] at h_cond ⊢
            exact Nat.cast_lt.mp h_cond.2
          -- The key equality
          have h_get : (hd :: tl).get ⟨m + 1, h_bound⟩ = tl.get ⟨m, hm⟩ := by
            simp [List.get_cons_succ]
          -- Convert the goal using h_natabs
          convert h_get.symm using 1
    | negSucc n =>
      -- i < 0, contradiction with 0 ≤ i
      simp at h_cond
  · -- Case: ¬(0 ≤ i < l.length)
    push_neg at h_cond
    cases i with
    | ofNat n =>
      -- i = n
      by_cases h : n < l.length
      · -- We have 0 ≤ n < l.length, contradiction
        have h1 : 0 ≤ (n : ℤ) := by simp
        have h2 : (n : ℤ) < l.length := by simp [h]
        -- h_cond h1 says l.length ≤ n, but h2 says n < l.length
        have h3 : (l.length : ℤ) ≤ n := h_cond h1
        linarith
      · -- n ≥ l.length
        push_neg at h
        simp only [Tape.nth, Tape.mk']
        cases n with
        | zero =>
          -- n = 0 ≥ l.length, so l is empty
          have : l = [] := by
            cases l
            · rfl
            · simp at h
          simp [this, ListBlank.mk, ListBlank.head]
        | succ m =>
          -- tape.nth (m+1) = tape.right.nth m
          simp only [ListBlank.tail_mk, ListBlank.nth_mk]
          cases' l with hd tl
          · -- Empty list
            simp
          · -- l = hd :: tl
            simp only [List.tail]
            rw [List.getI_eq_default]
            simp at h
            omega
    | negSucc n =>
      -- i = -(n+1) < 0
      -- tape.nth (-(n+1)) = tape.left.nth n
      simp only [Tape.nth, Tape.mk']
      -- tape.left = ListBlank.mk []
      simp [ListBlank.nth_mk, List.getI]

/-- Moving left preserves absolute tape content -/
lemma move_left_preserves_nth_absolute (T : LeftwardTape Γ) (i : ℤ) :
    T.move_left.nth_absolute i = T.nth_absolute i := by
  simp only [nth_absolute, move_left]
  -- move_left decreases head_pos by 1 and shifts tape indexing
  -- nth_absolute compensates for this: (i - (head_pos - 1)) = (i - head_pos) + 1
  -- And Tape.move_left shifts indexing by -1, so they cancel out
  rw [Tape.move_left_nth]
  ring_nf

/-- Moving right preserves absolute tape content -/
lemma move_right_preserves_nth_absolute (T : LeftwardTape Γ) (i : ℤ) :
    T.move_right.nth_absolute i = T.nth_absolute i := by
  simp only [nth_absolute, move_right]
  -- move_right either moves the head right by 1 (if head_pos < 0) or does nothing
  split_ifs with h_can_move
  · -- Case: head_pos < 0, so we can move right
    -- move_right increases head_pos by 1 and shifts tape indexing
    -- nth_absolute compensates: (i - (head_pos + 1)) = (i - head_pos) - 1
    -- And Tape.move_right shifts indexing by +1, so they cancel out
    rw [Tape.move_right_nth]
    ring_nf
  · -- Case: head_pos ≥ 0, so we cannot move right (tape unchanged)
    -- Since move_right returns T unchanged when head_pos ≥ 0
    rfl

/-- Moving the head left preserves the encoding -/
theorem encode_move_left (T : LeftwardTape Bool) :
  encode T.move_left = encode T := by
  -- The encoding depends only on absolute tape positions, not head position
  -- Moving the head doesn't change the tape content at absolute positions
  simp only [encode, true_positions_absolute]
  -- Both tapes have the same absolute positions with true values
  -- because move_left only changes head_pos, not the tape content
  congr 1
  ext i
  simp only [true_positions_absolute, Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · intro ⟨hmem, hle, htrue⟩
    refine ⟨?_, hle, ?_⟩
    · -- Show membership in finite support
      simp only [Set.mem_setOf, has_content_at_absolute] at hmem ⊢
      rw [← move_left_preserves_nth_absolute T i]
      exact hmem
    · -- Show the value is true
      rw [← move_left_preserves_nth_absolute T i]
      exact htrue
  · intro ⟨hmem, hle, htrue⟩
    refine ⟨?_, hle, ?_⟩
    · -- Show membership in finite support
      simp only [Set.mem_setOf, has_content_at_absolute] at hmem ⊢
      rw [move_left_preserves_nth_absolute T i]
      exact hmem
    · -- Show the value is true
      rw [move_left_preserves_nth_absolute T i]
      exact htrue

/-- Encoding is independent of head position - multiple moves -/
theorem encode_move_left_iter (T : LeftwardTape Bool) (n : ℕ) :
  encode (Nat.iterate (·.move_left) n T) = encode T := by
  induction n generalizing T with
  | zero => rfl
  | succ m ih => 
    -- Nat.iterate f (m+1) T = f (Nat.iterate f m T)
    conv_lhs => rw [Nat.iterate]
    -- Now we have: encode ((·.move_left)^[m] T.move_left)
    -- Apply ih to T.move_left
    rw [ih T.move_left, encode_move_left]

end LeftwardTape
