import TMTapeToNumber

/-!
This file is used by leanblueprint to check that all declarations mentioned
in the blueprint exist in the Lean project.
-/

-- Core definitions
#check LeftTM0.encode_config
#check LeftTM0.is_binary_step_sequence

-- Main theorems
#check LeftTM0.tm_sequence_is_binary_step_sequence
#check LeftTM0.binary_step_sequence_growth_bound
#check LeftTM0.finite_binary_step_sequence_generable

-- Supporting lemmas with correct namespaces
#check LeftTM0.BinaryStepSequences.encode_diff_at_write
#check LeftTM0.BinaryStepSequences.sequence_diff_is_power_of_two
#check LeftTM0.BinaryStepSequences.sequence_k_equals_position
#check LeftTM0.BinaryStepSequences.sequence_k_movement_constraint

-- Additional lemmas from the blueprint
#check LeftTM0.BinaryStepSequences.encode_diff_zero_implies_same
#check LeftTM0.BinaryStepSequences.encode_same_value_zero_diff
#check LeftTM0.BinaryStepSequences.encode_nat_diff_zero_cases

-- Construction function
#check LeftTM0.construct_tm_for_sequence