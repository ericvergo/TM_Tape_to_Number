import TMTapeToNumber.LeftTM0.LeftwardEncoding
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GeomSum

namespace LeftTM0.Theorems

open LeftTM0 LeftwardTape
open BigOperators
open Turing

variable {Λ : Type*} [Inhabited Λ]

/-- Empty tape encodes to 0 -/
theorem encode_empty_tape :
    (LeftwardTape.mk_initial ([] : List Bool)).encode = 0 := by
  -- Unfold the definition of encode
  simp only [encode, true_positions_absolute]
  -- Show that the filter produces an empty set
  -- because mk_initial [] creates a tape with only default (false) values
  have h_no_true : ∀ i ≤ 0, (mk_initial ([] : List Bool)).nth_absolute i ≠ true := by
    intro i _
    -- From mk_initial_nth, we know nth_absolute i = default = false for empty list
    rw [mk_initial_nth]
    simp
  -- The filter of positions with true values is empty
  have h_filter_empty : Finset.filter (fun i => i ≤ 0 ∧ (mk_initial ([] : List Bool)).nth_absolute i = true)
                        (finite_support_absolute (mk_initial ([] : List Bool))).toFinset = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.notMem_empty]
    constructor
    · intro ⟨_, hi_le, hi_true⟩
      -- This contradicts h_no_true
      exact h_no_true i hi_le hi_true
    · intro h
      exact False.elim h
  rw [h_filter_empty]
  simp

/-- Tape with single true at position 0 encodes to 1 -/
theorem encode_single_true_at_zero :
    (LeftwardTape.mk_initial [true]).encode = 1 := by
  -- Unfold the definition of encode
  simp only [encode, true_positions_absolute]
  -- The tape has true at position 0 and false elsewhere
  have h_at_zero : (mk_initial [true]).nth_absolute 0 = true := by
    rw [mk_initial_nth]
    simp
  have h_not_at_nonzero : ∀ i < 0, (mk_initial [true]).nth_absolute i = false := by
    intro i hi
    rw [mk_initial_nth]
    simp [hi]
  -- The filter produces exactly the singleton {0}
  have h_filter_singleton : Finset.filter (fun i => i ≤ 0 ∧ (mk_initial [true]).nth_absolute i = true)
                           (finite_support_absolute (mk_initial [true])).toFinset = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro ⟨_, hi_le, hi_true⟩
      -- i ≤ 0 and nth_absolute i = true
      -- By cases on whether i = 0 or i < 0
      by_cases h : i = 0
      · exact h
      · -- i < 0
        have hi_neg : i < 0 := lt_of_le_of_ne hi_le h
        have : (mk_initial [true]).nth_absolute i = false := h_not_at_nonzero i hi_neg
        rw [this] at hi_true
        simp at hi_true
    · intro hi_eq
      rw [hi_eq]
      refine ⟨?_, le_refl 0, h_at_zero⟩
      -- Need to show 0 ∈ (finite_support_absolute (mk_initial [true])).toFinset
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf]
      simp only [has_content_at_absolute, h_at_zero]
      trivial
  rw [h_filter_singleton]
  -- Now compute: ∑ i ∈ {0}, 2^(Int.natAbs (-i))
  simp




/-- Encoding respects the binary representation -/
theorem encode_binary_representation (tape : LeftwardTape Bool) :
    tape.encode = ∑ i ∈ tape.true_positions_absolute, 2^(Int.natAbs (-i)) := by
  -- This is just the definition of encode
  rfl

/-- Moving the head doesn't change the encoding -/
theorem encode_move_invariant (tape : LeftwardTape Bool) :
    tape.move_left.encode = tape.encode ∧
    tape.move_right.encode = tape.encode := by
  constructor
  · -- move_left case
    exact encode_move_left tape
  · -- move_right case
    -- For move_right, we need to show that absolute positions are preserved
    -- move_right either doesn't move (if at position 0) or moves right by 1
    simp only [encode, true_positions_absolute]
    -- Both sides have the same set of positions with true values
    congr 1
    ext i
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · intro ⟨hi_mem, hi_le, hi_true⟩
      refine ⟨?_, hi_le, ?_⟩
      · -- Show membership in finite support for original tape
        simp only [Set.mem_setOf, has_content_at_absolute] at hi_mem ⊢
        rw [← move_right_preserves_nth_absolute tape i]
        exact hi_mem
      · -- Show the value is true for original tape
        rw [← move_right_preserves_nth_absolute tape i]
        exact hi_true
    · intro ⟨hi_mem, hi_le, hi_true⟩
      refine ⟨?_, hi_le, ?_⟩
      · -- Show membership in finite support for moved tape
        simp only [Set.mem_setOf, has_content_at_absolute] at hi_mem ⊢
        rw [move_right_preserves_nth_absolute tape i]
        exact hi_mem
      · -- Show the value is true for moved tape
        rw [move_right_preserves_nth_absolute tape i]
        exact hi_true

-- Removed encode_write_true and encode_write_false as they're not needed for sequence proofs

/-- Bound on encoding based on leftmost true position -/
theorem encode_bound_by_leftmost (tape : LeftwardTape Bool) (n : ℕ) :
    (∀ i < -(n : ℤ), tape.nth_absolute i = false) →
    tape.encode < 2^(n.succ) := by
  intro h_bound
  -- All true positions are in range [-n, 0], so encoding ≤ ∑_{k=0}^n 2^k = 2^(n+1) - 1 < 2^(n+1)
  -- The key insight: true_positions_absolute ⊆ {-n, -n+1, ..., -1, 0}
  -- Each position -k contributes 2^k to the sum
  
  -- Step 1: Show that all true positions are in the range [-n, 0]
  have h_range : ∀ i ∈ tape.true_positions_absolute, -(n : ℤ) ≤ i ∧ i ≤ 0 := by
    intro i hi
    simp only [true_positions_absolute, Finset.mem_filter] at hi
    obtain ⟨_, hi_le, hi_true⟩ := hi
    constructor
    · -- Show -(n : ℤ) ≤ i
      by_contra h_not
      push_neg at h_not
      -- h_not : i < -(n : ℤ)
      have h_false : tape.nth_absolute i = false := h_bound i h_not
      rw [h_false] at hi_true
      simp at hi_true
    · -- Show i ≤ 0
      exact hi_le
  
  -- Step 2: The encoding is a sum over positions in [-n, 0]
  -- tape.encode = ∑ i ∈ tape.true_positions_absolute, 2^(Int.natAbs (-i))
  -- Since all i are in [-n, 0], we have -i in [0, n], so Int.natAbs(-i) ∈ [0, n]
  
  -- Step 3: Show the sum is bounded by the geometric series
  -- Key insight: map each position i to its contribution index Int.natAbs(-i)
  -- Since i ∈ [-n, 0], we have Int.natAbs(-i) ∈ [0, n]
  
  -- Create the image of true_positions_absolute under the map i ↦ Int.natAbs(-i)
  let contribution_indices := tape.true_positions_absolute.image (fun i => Int.natAbs (-i))
  
  -- Show that contribution_indices ⊆ Finset.range (n+1)
  have h_subset : contribution_indices ⊆ Finset.range n.succ := by
    intro k hk
    simp only [contribution_indices, Finset.mem_image] at hk
    obtain ⟨i, hi, rfl⟩ := hk
    -- i ∈ true_positions_absolute and k = Int.natAbs(-i)
    have ⟨hi_lower, hi_upper⟩ := h_range i hi
    -- We have -(n : ℤ) ≤ i ≤ 0
    -- So 0 ≤ -i ≤ n
    -- Therefore Int.natAbs(-i) ≤ n
    simp only [Finset.mem_range]
    -- Show Int.natAbs(-i) < n + 1
    have h_neg : 0 ≤ -i := by linarith
    have h_bound : -i ≤ n := by linarith
    -- We have -i ≤ n, and -i ≥ 0, so Int.natAbs(-i) = -i
    -- We need to show Int.natAbs(-i) < n + 1
    -- Since -i ≥ 0 and -i ≤ n, we have Int.natAbs(-i) = -i ≤ n < n + 1
    -- We need to show (-i).natAbs ≤ n
    -- Since 0 ≤ -i ≤ n, we have (-i).natAbs = -i as a natural number
    have h_eq : ((-i).natAbs : ℤ) = -i := by
      apply Int.natAbs_of_nonneg h_neg
    -- So (-i).natAbs ≤ n iff -i ≤ n as integers
    have : ((-i).natAbs : ℤ) ≤ (n : ℤ) := by
      rw [h_eq]
      exact h_bound
    -- Convert back to natural numbers
    have h_le_nat : (-i).natAbs ≤ n := by
      -- We have ((-i).natAbs : ℤ) ≤ (n : ℤ)
      -- Use that ℕ → ℤ preserves ≤
      exact Nat.cast_le.mp this
    omega
  
  -- Now we can bound the encoding
  have h_sum_bound : tape.encode ≤ ∑ k ∈ Finset.range n.succ, 2^k := by
    simp only [encode]
    -- Rewrite the sum to group by contribution index
    trans (∑ k ∈ contribution_indices, 2^k)
    · -- Show tape.encode ≤ ∑ k ∈ contribution_indices, 2^k
      -- Actually, we have equality here
      -- This uses the fact that Int.natAbs(-i) determines the contribution uniquely
      -- We use the sum_image theorem since the map i ↦ Int.natAbs(-i) is injective on true_positions_absolute
      have h_eq : tape.encode = ∑ k ∈ contribution_indices, 2^k := by
        simp only [encode, contribution_indices]
        -- We want to show: ∑ i ∈ tape.true_positions_absolute, 2^(Int.natAbs(-i)) = 
        --                  ∑ k ∈ Finset.image (fun i => Int.natAbs(-i)) tape.true_positions_absolute, 2^k
        symm
        apply Finset.sum_image
        -- Need to show: ∀ i j ∈ true_positions_absolute, Int.natAbs(-i) = Int.natAbs(-j) → i = j
        intro i hi j hj h_eq_natabs
        -- We have Int.natAbs(-i) = Int.natAbs(-j)
        -- From h_range, we know i, j ∈ [-n, 0]
        have ⟨hi_lower, hi_upper⟩ := h_range i hi
        have ⟨hj_lower, hj_upper⟩ := h_range j hj
        -- So -i, -j ∈ [0, n], hence Int.natAbs(-i) = -i and Int.natAbs(-j) = -j
        have h_neg_i : 0 ≤ -i := by linarith
        have h_neg_j : 0 ≤ -j := by linarith
        -- Since -i and -j are non-negative, Int.natAbs(-i) = (-i).toNat
        have h_i : (Int.natAbs (-i) : ℤ) = -i := Int.natAbs_of_nonneg h_neg_i
        have h_j : (Int.natAbs (-j) : ℤ) = -j := Int.natAbs_of_nonneg h_neg_j
        -- From h_eq_natabs and the fact that natAbs gives the same value
        have : (Int.natAbs (-i) : ℤ) = (Int.natAbs (-j) : ℤ) := by
          simp [h_eq_natabs]
        -- Therefore -i = -j
        have : -i = -j := by
          rw [← h_i, ← h_j, this]
        -- Therefore i = j
        linarith
      -- Now use the equality
      -- The goal is ∑ i ∈ tape.true_positions_absolute, 2^(-i).natAbs ≤ ∑ k ∈ contribution_indices, 2^k
      -- But we proved tape.encode = ∑ k ∈ contribution_indices, 2^k
      -- And tape.encode = ∑ i ∈ tape.true_positions_absolute, 2^(-i).natAbs by definition
      exact le_of_eq h_eq
    · -- Apply subset sum inequality
      apply Finset.sum_le_sum_of_subset_of_nonneg h_subset
      intro k _ _
      exact Nat.zero_le _
  
  -- Step 4: Use the geometric series formula
  have h_geom : ∑ k ∈ Finset.range n.succ, (2 : ℕ)^k = 2^n.succ - 1 := by
    -- Apply the geometric series formula: ∑_{i=0}^{n} 2^i = 2^{n+1} - 1
    clear h_bound h_range h_subset h_sum_bound contribution_indices tape
    -- Clean proof by induction
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      -- Goal: 2^n.succ - 1 + 2^n.succ = 2^(n + 1).succ - 1
      -- Simplify n.succ = n + 1 everywhere
      simp only [Nat.succ_eq_add_one]
      -- Goal: 2^(n + 1) - 1 + 2^(n + 1) = 2^(n + 1 + 1) - 1
      -- This is: 2*a - 1 = 2^(n+2) - 1 where a = 2^(n+1)
      have : 2^(n + 1) - 1 + 2^(n + 1) = 2 * 2^(n + 1) - 1 := by
        have : 1 ≤ 2^(n + 1) := Nat.one_le_two_pow
        omega
      rw [this]
      -- Now: 2 * 2^(n+1) - 1 = 2^(n+2) - 1
      congr 1
      -- Need: 2 * 2^(n+1) = 2^(n+2)
      -- But 2^(n+2) = 2^((n+1)+1) = 2^(n+1) * 2 = 2 * 2^(n+1)
      rw [pow_succ]
      ring
  
  -- Step 5: Conclude
  calc tape.encode ≤ ∑ k ∈ Finset.range n.succ, 2^k := h_sum_bound
    _ = 2^n.succ - 1 := h_geom
    _ < 2^n.succ := by
      apply Nat.sub_lt
      · -- Show 0 < 2^n.succ
        apply Nat.pow_pos
        norm_num
      · -- Show 0 < 1
        norm_num


-- Removed distinct_sets_distinct_sums and encode_determines_content as they're not needed for sequence proofs

-- Removed encode_injective_same_head_pos as it's not needed for sequence proofs


/-- Two tapes with same content at all positions have same encoding -/
theorem encode_ext (tape₁ tape₂ : LeftwardTape Bool) :
    (∀ i ≤ 0, tape₁.nth_absolute i = tape₂.nth_absolute i) →
    tape₁.encode = tape₂.encode := by
  intro h_eq
  -- Both encodings sum over the same values at the same positions
  simp only [encode, true_positions_absolute]

  -- Show both tapes have the same true positions
  have h_same_filter : (fun i => i ≤ 0 ∧ tape₁.nth_absolute i = true) = (fun i => i ≤ 0 ∧ tape₂.nth_absolute i = true) := by
    ext i
    constructor
    · intro ⟨hi_le, hi_true⟩
      constructor
      · exact hi_le
      · rw [← h_eq i hi_le]
        exact hi_true
    · intro ⟨hi_le, hi_true⟩
      constructor
      · exact hi_le
      · rw [h_eq i hi_le]
        exact hi_true

  -- Both sides filter using the same predicate (up to the equality h_eq)
  congr 1
  ext i
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
  by_cases h : i ≤ 0
  · -- Case: i ≤ 0, use h_eq
    constructor
    · intro ⟨hi_mem₁, hi_le, hi_true₁⟩
      refine ⟨?_, hi_le, ?_⟩
      · -- Show i ∈ finite_support_absolute tape₂
        simp only [Set.mem_setOf, has_content_at_absolute] at hi_mem₁ ⊢
        rw [← h_eq i h]
        exact hi_mem₁
      · -- Show tape₂.nth_absolute i = true
        rw [← h_eq i h]
        exact hi_true₁
    · intro ⟨hi_mem₂, hi_le, hi_true₂⟩
      refine ⟨?_, hi_le, ?_⟩
      · -- Show i ∈ finite_support_absolute tape₁
        simp only [Set.mem_setOf, has_content_at_absolute] at hi_mem₂ ⊢
        rw [h_eq i h]
        exact hi_mem₂
      · -- Show tape₁.nth_absolute i = true
        rw [h_eq i h]
        exact hi_true₂
  · -- Case: i > 0, both sides are false since we only consider i ≤ 0
    simp [h]

end LeftTM0.Theorems
