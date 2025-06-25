-- Import the new TM0-based infrastructure
import TMTapeToNumber.LeftTM0.Examples.PowersOfTwo
import TMTapeToNumber.LeftwardTape
import Mathlib.Data.Finsupp.Basic

-- Re-export key definitions for easy access
namespace TMTapeToNumber

-- Core types from the new infrastructure
export LeftTM0 (Machine Cfg sequence)

-- Main example
export LeftTM0.Examples (powers_sequence powers_machine)

-- Convenience aliases for backward compatibility
noncomputable def powersSequence : ℕ → ℕ := LeftTM0.Examples.powers_sequence

-- Initial configuration
def powersInitial : LeftTM0.Cfg Bool LeftTM0.Examples.PowersState := 
  LeftTM0.Examples.powers_initial

-- Basic correctness property: the sequence starts with 1
theorem powersSequence_zero : powersSequence 0 = 1 := 
  LeftTM0.Examples.powers_sequence_zero

end TMTapeToNumber

-- Legacy compatibility layer (for old interface)
namespace Legacy

-- Bool instance for finsupp
instance : Zero Bool := ⟨false⟩

-- The old LeftTape type (now deprecated in favor of LeftwardTape)
@[deprecated (since := "2024-01-01")] 
def LeftTape : Type := ℤ →₀ Bool

-- Old configuration type (now deprecated)
@[deprecated (since := "2024-01-01")]  
structure LeftTMConfig (State : Type) where
  tape : LeftTape
  head : ℤ
  state : Option State

-- Migration helper: convert old to new
noncomputable def migrate_to_new_interface (old_cfg : LeftTMConfig LeftTM0.Examples.PowersState) : 
    LeftTM0.Cfg Bool LeftTM0.Examples.PowersState :=
  sorry  -- Implementation would require proper conversion

end Legacy