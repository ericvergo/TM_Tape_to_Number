# Blueprint Creation Plan for TM_Tape_to_Number Project

## Goal
Create an interactive dependency graph visualization centered around the theorem `finite_binary_step_sequence_generable`, similar to the Covering Spaces Project example at https://alexkontorovich.github.io/CoveringSpacesProject/web/dep_graph_document.html

## Implementation Steps

### 1. Install leanblueprint
- Install graphviz system dependencies: `sudo apt install graphviz libgraphviz-dev` (or equivalent for macOS)
- Install Python package: `pip install leanblueprint`

### 2. Initialize Blueprint Infrastructure
- Run `leanblueprint new` in the project root
- Configure for GitHub Pages deployment
- Set up the blueprint directory structure

### 3. Create LaTeX Blueprint from Existing Paper
- Convert the existing paper LaTeX to blueprint format
- Add blueprint-specific annotations:
  - Mark theorems/lemmas with `\label{}`
  - Add `\lean{}` commands to link to Lean declarations
  - Use `\leanok` for fully formalized results
  - Use `\notready` for results with `sorry`
  - Add `\uses{}` to specify dependencies

### 4. Map Key Components for Dependency Graph
Focus on `finite_binary_step_sequence_generable` and its dependencies:
- Binary step sequence definition (`is_binary_step_sequence`)
- Supporting lemmas:
  - `encode_diff_at_write`
  - `sequence_diff_is_power_of_two`
  - `sequence_k_equals_position`
  - `sequence_k_bound`
  - `sequence_k_movement_constraint`
- Main theorems:
  - `tm_sequence_is_binary_step_sequence` (forward characterization)
  - `binary_step_sequence_growth_bound` (growth bounds)
  - `finite_binary_step_sequence_generable` (reverse characterization)
- Construction function (`construct_tm_for_sequence`)

### 5. Create GitHub Actions Workflow
- Set up automatic blueprint building and deployment
- Configure GitHub Pages to serve from gh-pages branch

### 6. Generate and Test
- Run `leanblueprint pdf` to generate PDF version
- Run `leanblueprint web` to generate HTML with dependency graph
- Run `leanblueprint serve` to test locally on port 8000

## File Structure to Create
```
blueprint/
├── src/
│   ├── web.tex          # Web version main file
│   ├── print.tex        # PDF version main file
│   ├── content.tex      # Main content (converted from paper)
│   └── macros/
│       ├── common.tex   # Shared macros
│       ├── web.tex      # Web-specific macros
│       └── print.tex    # Print-specific macros
└── blueprint.yml        # Configuration file

.github/workflows/
└── blueprint.yml        # GitHub Actions workflow
```

## Dependency Graph Structure

The dependency graph will show:

### Main Theorem
- `finite_binary_step_sequence_generable` (Theorem 3 in paper)

### Direct Dependencies
1. `is_finite_binary_step_sequence` (definition)
2. `construct_tm_for_sequence` (construction method)
3. `tm_sequence_is_binary_step_sequence` (forward characterization - Theorem 1)

### Supporting Lemmas
- `encode_diff_at_write` - encoding changes are powers of 2
- `sequence_diff_is_power_of_two` - TM steps produce valid differences
- `sequence_k_equals_position` - k values correspond to positions
- `sequence_k_bound` - k ≤ t constraint
- `sequence_k_movement_constraint` - |k_j - k_i| ≤ j - i constraint
- `binary_step_sequence_growth_bound` - growth bound theorem

### Foundation
- `is_binary_step_sequence` - main definition
- `sequence_difference` - helper function
- `change_indices` - indices where sequence changes
- Encoding functions from `LeftwardEncoding`
- Machine definitions from `LeftTM0`

## Status Indicators
- **White bubbles with green borders**: Formalized statement, proof incomplete (has `sorry`)
- **Blue bubbles with green borders**: Fully formalized (no `sorry`)
- **Red borders**: Not yet formalized in Lean

## Current Status
Based on the codebase analysis:
- Main theorem statements: Formalized (white/green)
- Several supporting lemmas: Partially complete (white/green)
- Core definitions: Fully formalized (blue/green)
- Construction proof: Not complete (white/green)

## Expected Outcome
An interactive web page with:
1. Dependency graph visualization showing relationships
2. Click-through to theorem statements
3. Links to Lean documentation
4. Color coding showing formalization progress
5. Human-readable descriptions from the paper