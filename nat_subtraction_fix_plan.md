# Plan to Fix Natural Number Subtraction Issues in TM_Tape_to_Number

## Status: ✅ COMPLETED (2025-07-04)

This plan has been successfully executed. The natural number subtraction issues have been resolved.

## Overview
The main issue is a flawed lemma `encode_diff_at_write_zero_means_equal` that incorrectly assumes `a - b = 0` implies `a = b` for natural numbers. This lemma is used in two places and has cascading effects.

## Step 1: Fix the Core Issue with `encode_diff_at_write`
The lemma `encode_diff_at_write` returns a disjunction with three cases:
1. Natural subtraction equals 0 (left case)
2. Integer difference equals 2^k (right case, positive)
3. Integer difference equals -2^k (right case, negative)

**Problem**: The left case uses natural subtraction, which makes it ambiguous when the actual difference is negative.

**Solution**: Refactor `encode_diff_at_write` to return a cleaner result:
- Change the return type to always use integer subtraction
- Return: `∃ k : ℕ, (encode_config cfg' : ℤ) - encode_config cfg ∈ {0, 2^k, -(2^k : ℤ)}`
- This eliminates the problematic natural subtraction case

## Step 2: Remove `encode_diff_at_write_zero_means_equal`
This lemma is fundamentally flawed and should be removed entirely. Its two uses need different handling:
1. In `sequence_diff_is_power_of_two` (line 862)
2. In `extract_k_value_from_step` (line 901)

## Step 3: Fix `sequence_diff_is_power_of_two`
- Instead of using `encode_diff_at_write_zero_means_equal`, directly handle the case where the encoding doesn't change
- When `encode_diff_at_write` returns that the difference is 0, we can directly conclude that `sequence_difference = 0`

## Step 4: Fix `extract_k_value_from_step`
- This lemma tries to extract the specific k value from a write operation
- Instead of relying on the flawed equality lemma, prove directly that when writing at position p, the change is ±2^|p|
- Create a new lemma `encode_write_diff_value` that directly computes the encoding difference

## Step 5: Address Related Sorries
Fix the following sorries that depend on the refactoring:
- Lines 940, 943 in `extract_k_value_from_step` 
- Lines 1296, 1310, 1374, 1428 (movement bound lemmas)
- Line 545 in Theorems.lean

## Step 6: Add Defensive Documentation
Add comments throughout the codebase warning about natural subtraction:
```lean
-- WARNING: Natural subtraction a - b = 0 only implies a ≤ b, not a = b
```

## Implementation Order
1. Create new helper lemmas for encoding differences that avoid natural subtraction
2. Refactor `encode_diff_at_write` to use only integer subtraction
3. Update `sequence_diff_is_power_of_two` to work with the new structure
4. Update `extract_k_value_from_step` with direct proofs
5. Remove `encode_diff_at_write_zero_means_equal` entirely
6. Complete remaining sorries using the cleaner structure

## Benefits
- Eliminates the fundamental confusion between `a - b = 0` and `a = b`
- Makes all subtraction behavior explicit
- Reduces the number of case analyses needed
- Creates a cleaner proof structure that's easier to complete

## Testing Strategy
After each change:
1. Run `lake build` to ensure no compilation errors
2. Use MCP tools to check that all theorems still type-check
3. Verify that the main theorems about binary step sequences remain intact

## Specific Issues Found

### Primary Problem: `encode_diff_at_write_zero_means_equal` (Lines 592-769)
- **Location**: `BinaryStepSequences/Lemmas.lean`
- **Issue**: Assumes that when `encode_config cfg' - encode_config cfg = 0`, then `encode_config cfg' = encode_config cfg`
- **Reality**: Natural subtraction `a - b = 0` only implies `a ≤ b`, not `a = b`
- **Contains**: 2 `sorry` statements where the proof fails for `cfg' < cfg` cases

### Uses of the Problematic Lemma
1. **Line 862** in `sequence_diff_is_power_of_two`
2. **Line 901** in `extract_k_value_from_step`

### Other Natural Subtraction Patterns (Correctly Handled)
- **Line 21** in `Basic.lean`: `abs_d &&& (abs_d - 1) = 0` - Properly guarded by `abs_d > 0`
- **Line 857** in `Lemmas.lean`: Uses `tsub_eq_zero_iff_le` explicitly
- **Line 1494** in `Lemmas.lean`: Uses `Nat.sub_eq_zero_of_le` when `k_i < k_j`
- **Line 280** in `Theorems.lean`: Validates `2^k ≤ s t` before subtracting

### Best Practices Already in Use
- `sequence_difference` (Basic.lean:13) casts to integers before subtracting
- Many proofs use explicit case analysis on ordering
- Bounds are checked before subtraction
- `Int.natAbs` is used appropriately with subtraction

## Root Cause Analysis
The issue stems from trying to use natural subtraction in a context where the sign of the difference matters. The `encode_diff_at_write` lemma mixes natural and integer subtraction in its return type, creating ambiguity that propagates through dependent lemmas.