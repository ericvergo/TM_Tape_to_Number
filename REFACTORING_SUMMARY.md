# Natural Subtraction Refactoring Summary

## Changes Made

### 1. Added Integer Difference Functions

#### In `EncodingDifference.lean`:
```lean
noncomputable def encode_diff (cfg cfg' : Cfg Bool Λ) : ℤ :=
  (encode_config cfg' : ℤ) - (encode_config cfg : ℤ)
```

#### In `SequenceProperties.lean`:
```lean
def sequence_diff (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ) : ℤ :=
  (sequence M init_cfg (t + 1) : ℤ) - (sequence M init_cfg t : ℤ)
```

### 2. Updated Core Lemmas

#### `encode_diff_at_write` (EncodingDifference.lean)
- **Before**: Used natural subtraction, cast to integer
- **After**: Uses `encode_diff` function directly
- **Result**: Correctly captures both positive and negative differences

#### `encode_diff_at_write_simple` (EncodingProperties.lean)
- **Before**: Said `diff = 0` when writing false over true
- **After**: Says `diff = -(2^k : ℤ)` when writing false over true
- **Result**: Preserves the actual decrease information

#### `encode_write_diff_value` (EncodingProperties.lean)
- **Before**: Said `diff = 0` when writing false over true
- **After**: Says `diff = -(2^k : ℤ)` when writing false over true
- **Result**: Correctly captures the decrease

#### `sequence_diff_is_power_of_two` (SequenceProperties.lean)
- **Before**: Used natural subtraction, lost info on decreases
- **After**: Uses `sequence_diff` function
- **Result**: Properly handles both increases and decreases

#### `sequence_k_equals_position` (SequenceProperties.lean)
- **Before**: Only handled increases
- **After**: Handles both increases and decreases
- **Result**: More general and correct

#### `sequence_k_movement_constraint` (SequenceProperties.lean)
- **Before**: Assumed only increases
- **After**: Handles both increases and decreases
- **Result**: Correctly captures all cases

## Benefits Achieved

1. **Mathematical Correctness**: The lemmas now correctly express what happens when the encoding decreases, instead of truncating to 0.

2. **Simplified Proofs**: Future proofs won't need complex workarounds for natural subtraction edge cases.

3. **Clarity**: The integer differences make the mathematical intent clearer.

4. **Consistency**: All encoding differences are now handled uniformly as integers.

## Remaining Work

1. **Update Proofs**: The `sorry` proofs need to be completed using the new definitions.

2. **Verify Theorems**: Check that the main theorems in `Theorems.lean` still work with the updated lemmas.

3. **Test Edge Cases**: Ensure the new formulations handle all edge cases correctly.

## Note on `sequence_difference`

The existing `sequence_difference` in `Basic.lean` was already defined correctly as:
```lean
def sequence_difference (s : ℕ → ℕ) (t : ℕ) : ℤ :=
  (s (t + 1) : ℤ) - (s t : ℤ)
```

This was good foresight in the original design! We added `sequence_diff` in `SequenceProperties.lean` for consistency with `encode_diff`, but they serve the same purpose.