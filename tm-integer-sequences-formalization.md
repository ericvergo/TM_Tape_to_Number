# Turing Machine Integer Sequences: Complete Specification for Formalization

## Critical Non-Standard Feature: Leftward-Unbounded Tape

**WARNING**: This construction uses a **leftward-unbounded tape with a rightmost boundary**, which is non-traditional and will require careful handling in Mathlib.

Standard Turing machine formalizations typically use:
- Bidirectionally infinite tapes
- Rightward-infinite tapes (with leftmost cell at position 0)
- Finite tapes

Our construction is distinctive: the tape extends infinitely to the left from a fixed rightmost position. This creates unique challenges for formalization.

## Core Construction

### Definition: TM-to-Integer Encoding with Leftward-Unbounded Tape

Given a Turing machine $M$ with binary alphabet $\{0, 1\}$ and a tape that extends infinitely to the left from a rightmost boundary, we define a function that maps each computational step to an integer.

**Components:**
- **Tape**: Indexed by non-positive integers $\{\ldots, -2, -1, 0\}$ where 0 is the rightmost cell
- **Initial configuration**: Finitely many 1s (all but finitely many cells contain 0)
- **Head**: Current position on the tape (a non-positive integer)
- **State**: Current state of the TM
- **Transition function**: $\delta: Q \times \{0,1\} \rightarrow Q \times \{0,1\} \times \{L, R\}$

**Integer Encoding Function:**
At time step $t$, if the tape has non-zero cells at positions $-m, -(m-1), \ldots, -1, 0$ with values $b_{-m}, b_{-(m-1)}, \ldots, b_{-1}, b_0$, then:

$E(t) = a_t = \sum_{i=0}^{m} b_{-i} \cdot 2^i = b_0 \cdot 2^0 + b_{-1} \cdot 2^1 + \cdots + b_{-m} \cdot 2^m$

Note: We read from right (position 0) to left (negative positions), with the rightmost bit being least significant.

This creates a sequence $(a_0, a_1, a_2, \ldots)$ where $a_t$ is the integer value of the tape at step $t$.

### Formalization Challenge: Leftward-Unbounded Representation

Mathlib's existing TM definitions likely assume rightward-unbounded or bidirectional tapes. We need to either:
1. **Adapt existing definitions** by using a bijection between $\mathbb{Z}_{\leq 0}$ and $\mathbb{N}$
2. **Create new definitions** specifically for leftward-unbounded TMs
3. **Use a finite approximation** that grows dynamically as needed

The encoding function naturally handles the infinite tape because at any finite time, only finitely many cells are non-zero.

### Example: Powers of 2 Generator (Leftward-Unbounded Tape)

A concrete 3-state TM that generates the sequence $1, 2, 4, 8, 16, \ldots$:

**States**: $Q = \{q_0, q_1, q_{halt}\}$  
**Initial state**: $q_0$  
**Initial tape**: All zeros except position 0 which contains 1  
**Initial head position**: Position 0 (rightmost cell)

**Transition function** $\delta$:
| Current State | Read Symbol | Write Symbol | Move | Next State |
|--------------|-------------|--------------|------|------------|
| $q_0$ | 0 | 0 | L | $q_0$ |
| $q_0$ | 1 | 0 | R | $q_1$ |
| $q_1$ | 0 | 1 | R | $q_1$ |
| $q_1$ | 1 | 1 | L | $q_0$ |

**Execution trace** (showing positions -4 to 0):
```
Step 0: [...0][0][0][0][0][1]  head at pos 0, state q_0  → a_0 = 1
        pos: -4 -3 -2 -1  0

Step 1: [...0][0][0][0][1][0]  head at pos -1, state q_1  → a_1 = 2
        pos: -4 -3 -2 -1  0

Step 2: [...0][0][0][1][0][0]  head at pos -2, state q_0  → a_2 = 4
        pos: -4 -3 -2 -1  0

Step 3: [...0][0][1][0][0][0]  head at pos -3, state q_1  → a_3 = 8
        pos: -4 -3 -2 -1  0

Step 4: [...0][1][0][0][0][0]  head at pos -4, state q_0  → a_4 = 16
        pos: -4 -3 -2 -1  0
```

Note: The ellipsis [...] represents the infinite leftward extension of zeros.

## Key Properties

### Property 1: Finite Support at Each Step
Despite the leftward-unbounded tape, at any finite time $t$, only finitely many cells contain 1. This ensures $a_t$ is always finite.

### Property 2: Single-Step Changes
Each TM step can modify at most one cell, changing one bit in the binary representation.

### Property 3: Head Movement Constraints
The head can move at most distance $k$ in $k$ steps. Starting from position $p$, after $k$ steps the head is in range $[p-k, p+k]$ (bounded by 0 on the right).

## Formal Bounds on Generated Sequences

### Bound 1: Growth Rate Limit
If the head starts at position 0 and only finitely many cells initially contain 1, then after $t$ steps:
$a_t \leq 2^{t+c} - 1$
where $c$ is the leftmost position of an initial 1.

**Proof sketch**: The head can reach at most position $-t$, so at most $t + c + 1$ bits can be non-zero.

### Bound 2: Single-Step Difference
The difference between consecutive values remains constrained:
$a_{t+1} - a_t \in \{0\} \cup \{2^i : i \in \mathbb{N}\} \cup \{-2^i : i \in \mathbb{N}\}$

**Proof sketch**: At step $t \to t+1$, the TM can:
- Leave the current cell unchanged (difference = 0)
- Change cell at position $-i$ from 0 to 1 (difference = $+2^i$)
- Change cell at position $-i$ from 1 to 0 (difference = $-2^i$)

### Bound 3: k-Step Reachability Bound
If the head starts at position $p$ at time $t$, then after $k$ steps:
$|a_{t+k} - a_t| \leq \sum_{i=\max(0,p-k)}^{\max(0,p+k)} 2^i$

**Proof sketch**: From position $p$, the head can reach cells in range $[\max(p-k, -\infty), \min(p+k, 0)]$. The maximum change occurs by flipping all reachable bits. Note that positions are non-positive, so position $-i$ contributes $2^i$ to the value.

### Bound 4: Hamming Distance Constraint
For any $k$ steps:
$$\text{HammingDistance}(\text{tape}_t, \text{tape}_{t+k}) \leq k$$

This translates to an integer bound:
$$|a_{t+k} - a_t| \leq \sum_{j=1}^{\min(k,n)} 2^{i_j}$$
where $i_1, \ldots, i_{\min(k,n)}$ are the positions of the (at most $k$) changed bits.

### Bound 5: Monotonicity Under Write Constraints
If the TM only writes 1s (never 0s) during interval $[t_1, t_2]$:
$$a_{t_1} \leq a_{t_1+1} \leq \cdots \leq a_{t_2}$$

Similarly, if the TM only writes 0s:
$$a_{t_1} \geq a_{t_1+1} \geq \cdots \geq a_{t_2}$$

### Bound 6: Periodicity Bound
If the TM configuration (tape + head position + state) repeats with period $p$:
$$\exists t_0 : \forall t \geq t_0 : a_{t+p} = a_t$$

## Formalization Goals

### Primary Objectives
1. **Adapt Mathlib's TM framework** for leftward-unbounded tapes
2. Formalize the encoding function $E: \text{TMConfig} \to \mathbb{N}$ for infinite configurations
3. Prove all bounds as formal theorems, accounting for the infinite nature
4. Implement the powers-of-2 example and verify it generates $(2^k)_{k \in \mathbb{N}}$

### Critical Formalization Challenges

**Challenge 1: Tape Representation**
Mathlib likely expects tapes indexed by $\mathbb{N}$ (rightward from 0). We need tapes indexed by $\mathbb{Z}_{\leq 0}$. Options:
- Define a bijection `neg_to_nat : ℤ≤0 → ℕ` mapping $-i \mapsto i$
- Create custom tape type for leftward-unbounded TMs
- Use cofinite support (tape as function with finite non-zero positions)

**Challenge 2: Configuration Finiteness**
Despite infinite tape, configurations must have finite support for encoding to yield finite integers.

### Key Definitions Needed
```lean
-- Leftward-unbounded tape (positions are non-positive integers)
structure LeftTape where
  cells : ℤ≤0 → Bool
  finite_support : {i : ℤ≤0 | cells i = true}.Finite
  
-- TM configuration with leftward-unbounded tape
structure LeftTMConfig where
  tape : LeftTape
  head : ℤ≤0  -- head position (non-positive)
  state : State
  
-- Encoding function for leftward-unbounded tape
def encode (cfg : LeftTMConfig) : ℕ :=
  -- Sum over positions where tape is 1
  -- Position -i contributes 2^i to the value
  (cfg.tape.finite_support.toFinset).sum (fun i => 2^(-i.val))
  
-- Alternative using cofinite support
def encode' (tape : ℤ≤0 →₀ Bool) : ℕ :=
  tape.sum (fun pos val => if val then 2^(-pos) else 0)
  
-- Sequence generation
def tmSequence (m : LeftTuringMachine) (init : LeftTMConfig) : ℕ → ℕ :=
  fun t => encode (m.run init t)
```

### Theorems to Prove
1. `theorem growth_bound : ∀ t, tmSequence m init t ≤ 2^(t + leftmost_initial_one) - 1`
2. `theorem single_step_diff : tmSequence m init (t+1) - tmSequence m init t ∈ {0} ∪ {±2^i | i ∈ ℕ}`
3. `theorem k_step_bound : |tmSequence m init (t+k) - tmSequence m init t| ≤ ...`
4. `theorem hamming_bound : ...`
5. `theorem monotonicity_write_ones : ...`
6. `theorem periodicity_implies_sequence_period : ...`

### Integration with Existing Mathlib

**Key consideration**: Mathlib's `computability.turing_machine` assumes standard tape indexing. We must either:
1. **Extend the existing framework** with a new tape variant
2. **Build parallel definitions** for leftward-unbounded machines
3. **Use an isomorphism** to map our construction to standard TMs

**Recommended approach**: Define a wrapper that converts between leftward-unbounded and standard representations, proving they preserve computational equivalence.

## Extensions and Questions

### Open Questions
1. **Characterization**: Which integer sequences can be generated by some TM under this encoding?
2. **Complexity**: What is the relationship between TM complexity and sequence properties?
3. **Decidability**: Is it decidable whether a given computable sequence can be TM-generated?

### Potential Extensions
1. Alternative encodings (left-to-right, different bases)
2. Infinite tape variants (with appropriate convergence conditions)
3. Multi-dimensional generalizations (2D tapes, etc.)

This document provides the complete specification for formalizing the construction of integer sequences from Turing machine execution traces, with all necessary definitions and bounds ready for implementation in a proof assistant.