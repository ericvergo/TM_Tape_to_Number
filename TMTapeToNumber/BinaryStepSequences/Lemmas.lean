/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean FRO Team
-/
import TMTapeToNumber.BinaryStepSequences.Basic
import TMTapeToNumber.BinaryStepSequences.EncodingDifference
import TMTapeToNumber.BinaryStepSequences.EncodingProperties
import TMTapeToNumber.BinaryStepSequences.SequenceProperties
import TMTapeToNumber.LeftwardSequences.Theorems
import TMTapeToNumber.LeftTM0.LeftwardTape
import TMTapeToNumber.LeftTM0.Step
import TMTapeToNumber.LeftwardEncoding.Properties
import Mathlib.Data.Nat.Log

/-!
# Helper Lemmas for Binary Step Sequences

This file contains miscellaneous helper lemmas that don't fit cleanly
into the other categorized files. Most of the main lemmas have been
moved to:

- `EncodingDifference.lean` - Core encoding difference lemmas
- `EncodingProperties.lean` - Properties of encoding operations and simplified versions
- `SequenceProperties.lean` - Properties of TM sequences
-/

set_option linter.unusedSectionVars false

namespace LeftTM0

namespace BinaryStepSequences

open Turing LeftTM0 LeftwardTape

variable {Λ : Type*} [Inhabited Λ]

-- Any remaining helper lemmas that don't fit in the other files can go here

end BinaryStepSequences

end LeftTM0