MCP TOOLS AVAILABLE
The lean-lsp MCP server provides powerful tools for real-time Lean development:
- `lean_goal` - See proof goals at any position (essential for understanding what to prove)
- `lean_diagnostic_messages` - Get errors without building
- `lean_hover_info` - Instant type information and documentation
- `lean_state_search` - Find theorems applicable to current goal (3req/30s limit)
- `lean_leansearch` - Natural language theorem search (3req/30s limit)
- `lean_loogle` - Pattern-based theorem search (3req/30s limit)
- `lean_multi_attempt` - Test multiple tactics quickly
- `lean_completions` - Explore available tactics and lemmas
- `lean_term_goal` - Understand expected types
- `lean_run_code` - Test proof snippets without file modification
- `lean_declaration_file` - Find where symbols are defined
- `lean_build` - Build project when needed

BEHAVIORS TO EMBODY
- Use MCP tools to check proof states and errors in real-time without building
- When editing proofs, use `lean_goal` to understand the current proof state
- Use `lean_diagnostic_messages` to get immediate feedback on errors
- Break up proofs into smaller lemmas to help chunk out work
- Keep notes in comments about proof attempts that didn't work
- Address errors systematically, one at a time using MCP diagnostics
- Use `have` statements liberally to break down complex goals
- Only run full builds (`lake build`) when finalizing changes or if MCP tools are insufficient
- When user says "we are spinning", immediately add a `sorry` and move to the next proof
- Clean up all build errors before diving into proof details - a building codebase is better than a partially proven one
- Use TodoWrite/TodoRead tools extensively to track progress and prioritize work

BEHAVIORS TO AVOID
- Replacing a sorry with another sorry + comments
- Shying away from complexity
- Truncating or skipping parts of error messages
- Making assumptions about what an error means without reading it fully
- Trying to fix multiple errors at once without understanding each one
- Overusing rate-limited search tools - respect the 3 requests per 30 seconds limit
- Running full builds when MCP tools can provide immediate feedback
- Getting stuck on trivial arithmetic when the user wants progress
- Spending too long on one proof - use sorry and move on when stuck

MCP-POWERED PROOF WORKFLOW
When proving theorems with sorries:
1. First pass: Use `lean_file_contents` to read and understand all theorems
2. For each theorem with sorry:
   a. Use `lean_goal` at the sorry location to see the exact proof state
   b. Use `lean_state_search` to find applicable theorems from the current state
   c. Use `lean_multi_attempt` to test multiple proof strategies quickly
   d. Once you have a promising approach, replace the sorry with the proof
   e. Use `lean_diagnostic_messages` to check for errors immediately
   f. If errors occur:
      - Use `lean_hover_info` to understand type mismatches
      - Use `lean_completions` to explore available tactics/lemmas
      - Use `lean_term_goal` to understand expected types
   g. Iterate until `lean_diagnostic_messages` shows no errors
3. Only run `lake build` for final verification or when MCP tools are insufficient
4. If stuck, use in order:
   - `lean_state_search` - Find theorems applicable to current goal
   - `lean_leansearch` - Natural language search for relevant concepts
   - `lean_loogle` - Pattern-based search for specific theorem shapes


PROOF STRATEGIES
- For equality proofs: Consider `rfl`, `simp`, `rw`, or `congr`
- For inequalities: Consider `linarith`, `omega`, or manual calculation
- For existential proofs: Provide explicit witnesses with `use`
- For inductive proofs: Use `induction` with clear base and step cases
- For case analysis: Use `cases` or `match` with exhaustive patterns
- When goals get complex: Extract sub-goals with `have` statements

MCP-POWERED ERROR HANDLING
Real-time error diagnosis without building:
1. **Check errors immediately**: `lean_diagnostic_messages(file_path)`
2. **Understand type mismatches**: 
   - `lean_hover_info(file_path, line, column)` on the problematic term
   - `lean_term_goal(file_path, line, column)` to see expected type
3. **Debug tactic failures**:
   - `lean_goal(file_path, line, column)` to see the actual goal
   - `lean_multi_attempt` to test alternative tactics
4. **Explore available options**: `lean_completions(file_path, line, column)`

Common Lean errors and MCP solutions:
- "failed to synthesize instance": 
  - Use `lean_hover_info` to check required instances
  - Use `lean_completions` to find available instances
- "type mismatch": 
  - Use `lean_hover_info` on both sides of the mismatch
  - Use `lean_term_goal` to see what type is expected
- "tactic failed": 
  - Use `lean_goal` to see the exact goal state
  - Use `lean_state_search` to find applicable theorems
- "declaration uses sorry": 
  - Use `lean_diagnostic_messages` to find all sorries
  - Use workflow above to complete each one
- Goal state shows `⊢ False`: 
  - You've reached a contradiction
  - Use `lean_goal` with column positions before the contradiction to trace assumptions

When to split into lemmas:
- When you prove something that could be reused
- When the goal has multiple independent parts
- When you need to prove a property by induction separately
- When you beliebe the proof is getting complex

MCP SEARCH TOOLS (PRIMARY - USE THESE FIRST)
- **lean_state_search** (limit: 3req/30s): Finds theorems applicable to current proof state
  - Most powerful for finding relevant lemmas when you have a specific goal
  - Automatically uses the first goal if multiple exist
- **lean_leansearch** (limit: 3req/30s): Natural language theorem search
  - Query patterns: "Cauchy Schwarz", "n < m implies n + 1 < m + 1"
  - Mixed queries: "natural numbers. from: n < m, to: n + 1 < m + 1"
  - Can search by concept names or Lean terms
- **lean_loogle** (limit: 3req/30s): Pattern-based theorem search
  - By constant: `Real.sin`
  - By subexpression: `_ * (_ ^ _)`
  - By type shape: `(?a -> ?b) -> List ?a -> List ?b`
  - By conclusion: `|- tsum _ = _ * tsum _`
- **lean_hover_info**: Get instant documentation and type info
- **lean_completions**: Explore available tactics, lemmas, and identifiers

TYPE CONVERSION AND CASTING
- When working with Int.natAbs, remember it returns a Nat, not an Int
- For non-negative integers, Int.natAbs_of_nonneg gives (Int.natAbs n : ℤ) = n
- Use Nat.cast_le.mp to convert (a : ℤ) ≤ (b : ℤ) to a ≤ b for naturals
- When proving equalities between natural numbers via their casts, use Nat.cast_injective
- Be careful with Int.toNat vs Int.natAbs - they behave differently on negative numbers
- Natural number subtraction (a - b) is 0 when a < b, different from integer subtraction
- When dealing with Nat/Int conversions in goals, `push_cast` is often helpful
- `omega` is powerful for arithmetic but sometimes fails - have `linarith` as backup

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

DEBUGGING ERRORS WITH MCP
- Use `lean_diagnostic_messages` to get real-time error information
- "no goals to be solved" often means a branch of a proof is already complete
- When seeing "unsolved goals", use `lean_goal` to check all branches
- Pay attention to whether you're inside a tactic block or term mode
- Use `by exact` instead of just providing a term when Lean expects a tactic

PATTERN MATCHING AND CASE ANALYSIS
- In tactic mode, use `cases h with | inl h1 => ... | inr h2 => ...` not `match`
- For existentials in `cases`, use `obtain ⟨var1, var2⟩ := h` to extract components
- When matching on TM0.Stmt, remember to handle all cases (move left/right, write)
- `unfold` at hypotheses sometimes fails - try unfolding only at the goal `⊢`
- For structure updates, use `{ cfg with field := value }` syntax carefully

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

MCP TOOL USAGE PATTERNS

Exploring a sorry:
```lean
-- 1. Get the proof state
lean_goal(file_path, line_of_sorry, column)

-- 2. Search for applicable theorems
lean_state_search(file_path, line_of_sorry, column, num_results=10)

-- 3. Test multiple approaches quickly
lean_multi_attempt(file_path, line_of_sorry, 
  ["simp", "omega", "linarith", "ring", "field_simp", "norm_num"])
```

Understanding type errors:
```lean
-- 1. Hover over the problematic term
lean_hover_info(file_path, line, column_at_start_of_term)

-- 2. Check expected type at position
lean_term_goal(file_path, line, column)

-- 3. Get completions to see valid options
lean_completions(file_path, line, column)
```

Finding the right lemma:
```lean
-- 1. Natural language search
lean_leansearch("if a divides b and b divides c then a divides c", num_results=5)

-- 2. Pattern search for specific shape
lean_loogle("_ ∣ _ → _ ∣ _ → _ ∣ _", num_results=8)

-- 3. Search by current goal state
lean_state_search(file_path, line, column)
```

Testing proof ideas without editing:
```lean
-- Test if a theorem applies
lean_run_code("""
import Mathlib.Data.Nat.Basic
example (n : ℕ) : n + 0 = n := by
  rw [Nat.add_zero]
""")

-- Try multiple tactics at once
lean_multi_attempt(file_path, line, 
  ["exact Nat.add_comm", "rw [Nat.add_comm]", "simp [Nat.add_comm]"])
```

Finding declarations:
```lean
-- 1. First check if symbol is available
lean_hover_info(file_path, line, column_of_symbol)

-- 2. If found, get its definition file
lean_declaration_file(file_path, "Nat.add_comm")

-- 3. Read the declaration's implementation
lean_file_contents(declaration_file_path)
```

Remember: MCP tools give instant feedback without the overhead of full compilation, making the proof development cycle much faster!

# REPOSITORY MAINTENANCE
Keep the repository clean and focused:
- Remove completed refactoring documentation after changes are merged
- Delete backup files (.bak) and test files  
- Clean up old build outputs
- Keep only essential documentation (README, PROJECT_STATUS, CLAUDE.md)
- Ensure all content is either in active use or preserved in version control history