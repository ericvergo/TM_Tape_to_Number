# Proof Strategy for Remaining Sorries

This document outlines strategies for completing the 15 remaining proofs in the TM Tape to Number formalization.

## Dependency Graph

```
sequence_change_implies_not_terminal
    ↓
encode_diff_at_write
    ↓
encode_strict_decrease_write_false, encode_strict_increase_write_true
    ↓
encode_diff_zero_implies_same, encode_same_value_zero_diff
    ↓
encode_diff_at_write_simple, encode_write_diff_value
    ↓
sequence_diff_is_power_of_two
    ↓
encode_change_from_step
    ↓
sequence_k_equals_position
    ↓
sequence_k_movement_constraint
    ↓
finite_binary_step_sequence_generable
```

## Proof Strategies

### 1. **sequence_change_implies_not_terminal** (SequenceProperties.lean:69)
**Priority**: HIGH - Blocks main theorem proofs  
**Strategy**: 
- If the sequence changes, the encoding must have changed
- Encoding only changes when a write operation occurs
- Write operations only happen when the machine hasn't terminated
- Use contradiction: assume terminal, show no writes possible

### 2. **encode_diff_at_write** (EncodingDifference.lean:35)
**Priority**: HIGH - Core lemma  
**Strategy**:
- Case split on whether `cfg.tape.nth 0 = a`
- If same: diff = 0 (use `encode_same_value_zero_diff`)
- If different: compute the bit flip at position `head_pos`
- Show this gives ±2^|head_pos|

### 3. **encode_strict_decrease_write_false** (EncodingDifference.lean:42)
**Priority**: MEDIUM  
**Strategy**:
- Writing false at position p changes bit from 1 to 0
- This decreases encoding by exactly 2^|p|
- Use properties of `LeftwardTape.encode`

### 4. **encode_strict_increase_write_true** (EncodingDifference.lean:49)
**Priority**: MEDIUM  
**Strategy**:
- Writing true at position p changes bit from 0 to 1
- This increases encoding by exactly 2^|p|
- Mirror of the decrease proof

### 5. **encode_nat_sub_zero_eq** (EncodingProperties.lean:89)
**Priority**: LOW - Helper lemma  
**Strategy**:
- If `a - b = 0` for naturals, then `a ≤ b`
- Use `Nat.sub_eq_zero_iff_le`
- Apply `Nat.le_antisymm` if we also have `b ≤ a`

### 6. **encode_diff_zero_implies_same** (EncodingProperties.lean:55)
**Priority**: MEDIUM  
**Strategy**:
- If integer diff = 0, encodings are equal
- Equal encodings with write operation implies same bit written
- Use injectivity of encoding

### 7. **encode_same_value_zero_diff** (EncodingProperties.lean:110)
**Priority**: MEDIUM  
**Strategy**:
- Writing same value doesn't change any bits
- Therefore encoding stays the same
- Direct from definition of `tape.write`

### 8. **encode_diff_at_write_simple** (EncodingProperties.lean:124)
**Priority**: MEDIUM  
**Strategy**:
- This follows directly from `encode_diff_at_write`
- Just need to extract the specific cases and compute k

### 9. **encode_write_diff_value** (EncodingProperties.lean:134)
**Priority**: MEDIUM  
**Strategy**:
- Direct computation from tape write semantics
- Use `encode_strict_increase_write_true` and `encode_strict_decrease_write_false`

### 10. **sequence_diff_is_power_of_two** (SequenceProperties.lean:36)
**Priority**: HIGH  
**Strategy**:
- `sequence (t+1) = encode (steps M (t+1) init)`
- `steps M (t+1) init = step_or_stay M (steps M t init)`
- Use `encode_change_from_step`

### 11. **encode_change_from_step** (SequenceProperties.lean:44)
**Priority**: HIGH  
**Strategy**:
- `step_or_stay` either doesn't change config or does one step
- One step can only write at current position
- Apply `encode_diff_at_write`

### 12. **sequence_k_equals_position** (SequenceProperties.lean:52)
**Priority**: MEDIUM  
**Strategy**:
- From `sequence_diff_is_power_of_two`, get that diff = ±2^k
- The only way to get 2^k is writing at position with |pos| = k
- Extract position from the step

### 13. **sequence_k_movement_constraint** (SequenceProperties.lean:63)
**Priority**: MEDIUM  
**Strategy**:
- k values correspond to head positions
- Head can move at most 1 position per step
- Therefore |k_j - k_i| ≤ j - i

### 14. **encode_nat_diff_zero_cases** (EncodingProperties.lean:118)
**Priority**: LOW  
**Strategy**:
- This is now just `Nat.sub_eq_zero_iff_le`
- Direct application

### 15. **finite_binary_step_sequence_generable** (Theorems.lean:592)
**Priority**: LOW - Constructive proof  
**Strategy**:
- Need to build explicit TM that generates sequence
- Follow the construction outlined in comments
- Implement state transitions based on sequence differences

## Recommended Order

1. Start with `sequence_change_implies_not_terminal` - unblocks other proofs
2. Then `encode_diff_at_write` - core encoding lemma
3. Then `encode_strict_decrease/increase_write_false/true` - direct computations
4. Then `sequence_diff_is_power_of_two` and `encode_change_from_step`
5. Complete remaining encoding lemmas
6. Finish with sequence properties
7. Finally tackle the constructive proof

## Tactical Hints

- Use `simp [encode_config, LeftwardTape.encode]` to unfold encodings
- Use `cases` on Bool values when needed
- Use `omega` for arithmetic goals
- Use `push_cast` for natural/integer conversions
- Remember that `tape.head_pos ≤ 0` always

## Testing

After completing each proof, run:
```bash
lake build TMTapeToNumber.BinaryStepSequences
```

This ensures no regressions and all proofs still compile.