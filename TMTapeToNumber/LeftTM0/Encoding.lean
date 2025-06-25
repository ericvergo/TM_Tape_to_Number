import TMTapeToNumber.LeftTM0.Step
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.MinMax
import Mathlib.Data.List.MinMax

namespace LeftTM0

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Encode a configuration's tape as a natural number -/
noncomputable def encode_config (cfg : Cfg Bool Λ) : ℕ :=
  cfg.tape.encode

/-- Encode just the tape content -/
noncomputable def encode_tape (tape : LeftwardTape Bool) : ℕ :=
  tape.encode

/-- Check if a position has true content (relative to head) -/
def has_true_at (cfg : Cfg Bool Λ) (pos : ℤ) : Bool :=
  cfg.tape.nth pos

/-- Check if an absolute tape position has true content -/
def has_true_at_absolute (cfg : Cfg Bool Λ) (pos : ℤ) : Bool :=
  cfg.tape.nth_absolute pos

/-- Get the leftmost absolute position with true content -/
noncomputable def leftmost_true_pos (cfg : Cfg Bool Λ) : Option ℤ :=
  -- Get all absolute positions with true values
  let true_positions := cfg.tape.true_positions_absolute
  match true_positions.toList.minimum with
  | ⊤ => none
  | (x : ℤ) => some x

/-- Get the rightmost absolute position with true content -/
noncomputable def rightmost_true_pos (cfg : Cfg Bool Λ) : Option ℤ :=
  -- Get all absolute positions with true values  
  let true_positions := cfg.tape.true_positions_absolute
  match true_positions.toList.maximum with
  | ⊥ => none
  | (x : ℤ) => some x

-- Properties of encoding (now using absolute positions)
theorem encode_config_zero (cfg : Cfg Bool Λ) :
    cfg.tape.nth_absolute 0 = false → 
    (∀ i < 0, cfg.tape.nth_absolute i = false) →
    encode_config cfg = 0 := by sorry

theorem encode_config_single_true_at_zero (cfg : Cfg Bool Λ) :
    cfg.tape.nth_absolute 0 = true → 
    (∀ i < 0, cfg.tape.nth_absolute i = false) →
    encode_config cfg = 1 := by sorry

theorem encode_config_monotone_right_shift (cfg : Cfg Bool Λ) :
    -- If we shift all absolute content one position left, encoding doubles
    ∀ (cfg' : Cfg Bool Λ), (∀ i, cfg'.tape.nth_absolute (i-1) = cfg.tape.nth_absolute i) →
    cfg'.tape.nth_absolute 0 = false →
    encode_config cfg' = 2 * encode_config cfg := by sorry

/-- Bound on encoding based on tape content -/
theorem encode_config_bound (cfg : Cfg Bool Λ) :
    match leftmost_true_pos cfg with
    | none => encode_config cfg = 0
    | some pos => encode_config cfg ≤ 2^(Int.natAbs pos) - 1 := by sorry

/-- Single step can change encoding by at most a power of 2 -/
theorem encode_step_diff (M : Machine Bool Λ) (cfg cfg' : Cfg Bool Λ) :
    step M cfg = some cfg' →
    ∃ k : ℕ, |Int.ofNat (encode_config cfg') - Int.ofNat (encode_config cfg)| ≤ 2^k := by sorry

end LeftTM0