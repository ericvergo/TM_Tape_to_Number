# Lean LSP MCP Setup Guide

This document describes the Model Context Protocol (MCP) server setup for enhanced Lean 4 development assistance in the TM_Tape_to_Number project.

## Setup Complete ✅

The lean-lsp-mcp server has been configured for this project. To activate it:

1. **Restart Claude Code** - The MCP server will be loaded on next startup
2. The server is configured at project scope in `.claude/mcp_settings.json`

## Available MCP Tools

Once active, Claude will have access to these Lean-specific tools:

### Core LSP Tools
- `lean_file_contents` - Read Lean file contents
- `lean_diagnostic_messages` - Get errors/warnings for files
- `lean_goal` - Get proof goals at cursor position (essential for proof completion!)
- `lean_term_goal` - Get expected type at position
- `lean_hover_info` - Get documentation/type info
- `lean_completions` - Get code completions
- `lean_multi_attempt` - Try multiple proof strategies
- `lean_run_code` - Test proof snippets

### Search Tools
- `lean_leansearch` - Natural language theorem search
- `lean_loogle` - Pattern-based theorem lookup
- `lean_state_search` - Find theorems applicable to current proof state

## Usage for Remaining Proofs

For the 10 remaining `sorry` obligations in this project:

1. **Check proof state**: Use `lean_goal` at each `sorry` location
2. **Search for theorems**: Use `lean_state_search` to find applicable lemmas
3. **Test approaches**: Use `lean_multi_attempt` to try different tactics
4. **Verify solutions**: Use `lean_diagnostic_messages` to ensure no errors

## Example Workflow

```lean
-- At a sorry location:
theorem some_theorem : P := by
  sorry  -- Use lean_goal here to see what needs to be proven
```

Claude can then:
1. Get the exact proof goal
2. Search mathlib for relevant theorems
3. Test multiple proof strategies
4. Provide a working solution

## Prerequisites

- ✅ uv package manager installed
- ✅ Project builds successfully with `lake build`
- ✅ MCP server configured

## Troubleshooting

If MCP tools aren't available after restart:
1. Check with `claude mcp list`
2. Reconfigure if needed: `claude mcp add lean-lsp -s project uvx lean-lsp-mcp`
3. Ensure project path is correct (should auto-detect from lakefile.toml)

## Benefits

This MCP integration provides:
- Real-time proof state information
- Direct access to mathlib search
- Ability to test proofs without file modification
- Enhanced theorem discovery capabilities

Perfect for completing the formalization of binary step sequences!