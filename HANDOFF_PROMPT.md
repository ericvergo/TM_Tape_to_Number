# Prompt for Continuing TM Tape to Number Proof Completion

You are tasked with completing the remaining proofs in a Lean 4 formalization project. The project proves that Turing Machine computation sequences form "binary step sequences" when tape contents are encoded as natural numbers.

## Project Context

**Repository**: `/Users/eric/Documents/GitHub/TM_Tape_to_Number`
**Build Status**: ✅ Builds successfully with 25 sorries
**Completion**: ~95% (major theorems proven, technical details remain)

### Key Concepts
1. **Encoding**: Leftward-unbounded tape positions (..., -2, -1, 0) encode as: position i contributes 2^|i| if tape has 'true' at position i
2. **Binary Step Sequences**: Sequences where consecutive differences are 0 or ±2^k
3. **Main Result**: Every TM-generated sequence is a binary step sequence

### Technical Setup
- The project uses MCP tools (lean-lsp) for real-time proof assistance
- Key tactic: use `mcp__lean-lsp__lean_goal` to check proof states
- Integer differences (`encode_diff`) handle encoding changes properly
- Head position is always ≤ 0 (leftward-bounded)

## Your Primary Task

Complete the 25 remaining sorries, prioritized as follows:

### High Priority - Sum Decomposition Proofs
These are in `TMTapeToNumber/BinaryStepSequences/EncodingDifference.lean`:

1. **Inside `encode_diff_at_write`** (line ~45):
   - Prove writing same value gives diff = 0
   - Use the fact that encoding doesn't change when writing the same bit

2. **Inside `encode_diff_at_write`** (lines ~68, ~81):  
   - Prove exact difference values when writing different values
   - Writing true over false: diff = 2^k where k = |head_pos|
   - Writing false over true: diff = -2^k where k = |head_pos|

3. **Inside `encode_strict_decrease_write_false`** (line ~95):
   - Complete sum decomposition showing tape.encode = (tape.write false).encode + 2^|head_pos|
   - Key: removing a 'true' bit removes its contribution from the sum

4. **Inside `encode_strict_increase_write_true`** (line ~115):
   - Complete sum decomposition showing (tape.write true).encode = tape.encode + 2^|head_pos|
   - Key: adding a 'true' bit adds its contribution to the sum

### Medium Priority - Step Function Analysis
In `TMTapeToNumber/BinaryStepSequences/SequenceProperties.lean`:

1. **`encode_change_from_step`** (line ~55):
   - Analyze how `step` function affects encoding
   - Key insight: only write operations change encoding, movements preserve it
   - Cases: terminal (no change), move (no encoding change), write (use encode_diff_at_write)

2. **`sequence_k_equals_position`** (line ~115):
   - Complete the connection between k and head position
   - You have the structure, need to trace through how encode_diff_at_write determines k

### Lower Priority
- Movement constraints, encoding properties, constructive proof
- PowersOfTwo.lean examples (11 sorries, least important)

## Key Strategies from PROOF_STRATEGY.md

1. **For sum proofs**: Show that true_positions_absolute changes by exactly one element
2. **For encoding changes**: Remember position p contributes 2^|p| to encoding
3. **Use MCP tools**: Check goals with `mcp__lean-lsp__lean_goal` before writing tactics
4. **Common tactics**: `simp`, `omega`, `linarith`, case analysis on Bool values

## Working Approach

1. Start with the high-priority sum decomposition proofs - these unblock other proofs
2. Use `lake build` frequently to ensure no regressions
3. Read CLAUDE.md for detailed MCP tool usage patterns
4. The major theorem structures are complete - you're filling in technical details

## Example of Completed Proof Pattern

```lean
lemma sequence_change_implies_not_terminal (M : Machine Bool Λ) (init_cfg : Cfg Bool Λ) (t : ℕ)
    (h_change : sequence M init_cfg t ≠ sequence M init_cfg (t + 1)) :
    ¬is_terminal M (steps M t init_cfg) := by
  intro h_terminal
  -- If terminal, then step_or_stay keeps the same config
  have h_stay : step_or_stay M (steps M t init_cfg) = steps M t init_cfg := by
    unfold step_or_stay
    rw [h_terminal]
  -- But sequence changes, which contradicts
  have h_eq : sequence M init_cfg (t + 1) = sequence M init_cfg t := by
    unfold sequence
    rw [steps_succ, h_stay]
  exact h_change h_eq.symm
```

This shows the style: clear comments, systematic approach, leveraging definitions.

## Success Criteria

- All 25 sorries replaced with complete proofs
- Project continues to build successfully
- Maintain proof clarity and documentation
- Follow existing proof patterns in the codebase

Good luck! The framework is solid and the main theoretical work is done. You're completing the technical details that connect the abstract theorems to concrete computations.