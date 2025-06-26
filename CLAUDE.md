BEHAVIORS TO EMBODY
- Build Lean files immediately after editing them to check for errors. NEVER truncate error messages - it is critical to read the full output.
- **ALWAYS** save build output to a text file using `| tee build_output.txt` for complete error analysis
- Break up proofs into smaller lemmas to help chunk out work
- Keep notes in comments about proof attempts that didn't work
- Always read the ENTIRE build output - every error, warning, and goal state
- Address errors systematically, one at a time
- Use `have` statements liberally to break down complex goals

BEHAVIORS TO AVOID
- Don't replace a sorry with another sorry and consider it making progress
- Shying away from complexity
- Truncating or skipping parts of error messages
- Making assumptions about what an error means without reading it fully
- Trying to fix multiple errors at once without understanding each one
- **NEVER** run build commands without saving output to build_output.txt

ITERATIVE PROOF WORKFLOW
When proving theorems with sorries:
1. First pass: Read the file completely to understand all theorems that need proving
2. For each theorem with sorry:
   a. Replace the sorry with a proof attempt
   b. **MANDATORY**: Build the file with: `lake build <module> 2>&1 | tee build_output.txt`
   c. **MANDATORY**: Read build_output.txt completely - EVERY line of errors/warnings
   d. Copy the COMPLETE error message including:
      - The goal state
      - All hypotheses
      - The exact error description
      - Any suggestions from Lean
   e. Address the specific error in context
   f. Rebuild and repeat until clean
3. Only move to the next theorem after the current one builds cleanly
4. If stuck, consider:
   - Breaking the proof into helper lemmas
   - Looking for similar proofs in the codebase
   - Checking mathlib for relevant theorems

**MANDATORY BUILD COMMAND FORMAT:**
```
lake build <module_name> 2>&1 | tee build_output.txt
```

Example workflow:
```
1. Edit file, attempt proof
2. **ALWAYS RUN**: lake build TMTapeToNumber.LeftTM0.LeftwardSequences 2>&1 | tee build_output.txt
3. **ALWAYS READ**: build_output.txt completely - never skip this step
4. Address each error based on the full context
5. Repeat until no errors remain
```

**CRITICAL**: Every single build command MUST include `2>&1 | tee build_output.txt` to capture the complete output for analysis. This is non-negotiable for effective debugging.

PROOF STRATEGIES
- For equality proofs: Consider `rfl`, `simp`, `rw`, or `congr`
- For inequalities: Consider `linarith`, `omega`, or manual calculation
- For existential proofs: Provide explicit witnesses with `use`
- For inductive proofs: Use `induction` with clear base and step cases
- For case analysis: Use `cases` or `match` with exhaustive patterns
- When goals get complex: Extract sub-goals with `have` statements

ERROR HANDLING
Common Lean errors and solutions:
- "failed to synthesize instance": You're missing a typeclass instance
- "type mismatch": Check exact types with `#check`, use `show` to clarify
- "tactic failed": The tactic doesn't apply - read why from the goal state
- "declaration uses sorry": You still have incomplete proofs
- Goal state shows `⊢ False`: You've reached a contradiction - check your assumptions

When to split into lemmas:
- When you prove something that could be reused
- When the goal has multiple independent parts
- When you need to prove a property by induction separately

SEARCH TIPS
- When making mathlib inquiries, use a local grep search constrained to /Users/eric/Documents/GitHub/TM_Tape_to_Number/.lake/packages/mathlib/Mathlib. This is a local, complete mathlib build
- When trying to find import statements, look in /Users/eric/Documents/GitHub/TM_Tape_to_Number/.lake/packages/mathlib/Mathlib.lean. This file contains every possible mathlib import statement, one per line
- Search patterns for mathlib:
  - For theorems about specific functions: `grep -r "theorem.*function_name" .lake/packages/mathlib/Mathlib`
  - For instances: `grep -r "instance.*TypeClass" .lake/packages/mathlib/Mathlib`
  - For definitions: `grep -r "^def.*keyword" .lake/packages/mathlib/Mathlib`
- Use `#check` in Lean files to explore theorem signatures
- Use `by exact?` to search for applicable theorems

TYPE CONVERSION AND CASTING
- When working with Int.natAbs, remember it returns a Nat, not an Int
- For non-negative integers, Int.natAbs_of_nonneg gives (Int.natAbs n : ℤ) = n
- Use Nat.cast_le.mp to convert (a : ℤ) ≤ (b : ℤ) to a ≤ b for naturals
- When proving equalities between natural numbers via their casts, use Nat.cast_injective
- Be careful with Int.toNat vs Int.natAbs - they behave differently on negative numbers

REWRITING TACTICS
- When `rw` fails with "did not find instance of the pattern", check:
  - Exact syntactic match (2 * x vs x * 2 matters without commutativity)
  - Implicit arguments and type ascriptions
  - Whether you need to unfold definitions first
- Use `simp only [specific_lemmas]` instead of `simp` for more control
- When stuck, use `show` to make the goal's expected form explicit

MANAGING COMPLEX PROOFS
- When induction generates many unused hypotheses, use `clear` to simplify context
- For standard results (like geometric series), sometimes direct induction is cleaner than searching mathlib
- Break complex expressions into named pieces with `have` statements
- Use `calc` blocks for multi-step inequalities or equalities

WORKING WITH FINITE SUMS
- Finset.sum_image requires proving injectivity on the support set
- When reindexing sums, be explicit about the bijection
- For subset sums, use Finset.sum_le_sum_of_subset_of_nonneg
- Remember that sum indices must be in Finsets, not general Sets

INEQUALITY PROOFS
- Convert equalities to inequalities with le_of_eq when needed
- Use `omega` for arithmetic inequalities involving addition/subtraction
- For power inequalities, Nat.pow_pos and Nat.one_le_two_pow are useful
- Build inequality chains with `calc` or transitive lemmas

DEBUGGING BUILD ERRORS
- "no goals to be solved" often means a branch of a proof is already complete
- When seeing "unsolved goals", check all branches of case splits and inductions
- Pay attention to whether you're inside a tactic block or term mode
- Use `by exact` instead of just providing a term when Lean expects a tactic

PROOF ARCHITECTURE
- Extract commonly needed facts as separate lemmas
- State lemmas in their most general useful form
- When a proof gets too nested, refactor with helper lemmas
- Name your `have` statements when they represent meaningful facts

COMMON PROOF PATTERNS
Sum reindexing pattern:
```lean
-- To prove: ∑ i ∈ s, f(g(i)) = ∑ j ∈ g(s), f(j)
apply Finset.sum_image
-- Prove g is injective on s
intro x hx y hy hxy
-- Show x = y from g(x) = g(y)
```

Bound by subset pattern:
```lean
-- To prove: ∑ i ∈ s, f(i) ≤ ∑ i ∈ t, f(i)
apply Finset.sum_le_sum_of_subset_of_nonneg
· -- Prove s ⊆ t
· -- Prove all terms are non-negative
```

Equality to inequality pattern:
```lean
have h_eq : a = b := by ...
-- To use in inequality goal a ≤ c:
rw [h_eq]  -- if goal becomes b ≤ c
-- OR
exact le_of_eq h_eq  -- if goal is a ≤ b
```

Geometric series pattern:
```lean
-- For ∑ k in range n, r^k = (r^n - 1)/(r - 1)
-- Often easier to prove by induction than finding the right theorem
induction n with
| zero => simp
| succ n ih => 
  rw [sum_range_succ, ih]
  -- Algebraic manipulation
```