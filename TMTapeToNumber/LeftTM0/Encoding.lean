import TMTapeToNumber.LeftTM0.Step

namespace LeftTM0

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Encode a configuration's tape as a natural number -/
noncomputable def encode_config (cfg : Cfg Bool Λ) : ℕ :=
  cfg.tape.encode

/-- Encode just the tape content -/
noncomputable def encode_tape (tape : LeftwardTape Bool) : ℕ :=
  tape.encode

/-- Check if a position has true content -/
def has_true_at (cfg : Cfg Bool Λ) (pos : ℤ) : Bool :=
  cfg.tape.nth pos

/-- Get the leftmost position with true content (approximation) -/
def leftmost_true_pos (cfg : Cfg Bool Λ) : ℤ :=
  -- Search in a reasonable range for the leftmost true
  let range := List.range 100  -- Check positions 0, -1, -2, ..., -99
  let positions := range.map (fun k => -Int.ofNat k)
  match positions.find? (fun pos => has_true_at cfg pos) with
  | none => 0  -- Default if no true found
  | some pos => pos

/-- Get the rightmost position with true content -/
def rightmost_true_pos (cfg : Cfg Bool Λ) : ℤ :=
  -- Since we're leftward-bounded, rightmost is at most 0
  let range := List.range 100
  let positions := range.map (fun k => -Int.ofNat k)
  let reversed_positions := positions.reverse  -- Start from 0 and go left
  match reversed_positions.find? (fun pos => has_true_at cfg pos) with
  | none => 0
  | some pos => pos

-- Properties of encoding
theorem encode_config_zero (cfg : Cfg Bool Λ) :
    cfg.tape.nth 0 = false → 
    (∀ i < 0, cfg.tape.nth i = false) →
    encode_config cfg = 0 := by sorry

theorem encode_config_single_true_at_zero (cfg : Cfg Bool Λ) :
    cfg.tape.nth 0 = true → 
    (∀ i < 0, cfg.tape.nth i = false) →
    encode_config cfg = 1 := by sorry

theorem encode_config_monotone_right_shift (cfg : Cfg Bool Λ) :
    -- If we shift all content one position left, encoding doubles
    ∀ (cfg' : Cfg Bool Λ), (∀ i, cfg'.tape.nth (i-1) = cfg.tape.nth i) →
    cfg'.tape.nth 0 = false →
    encode_config cfg' = 2 * encode_config cfg := by sorry

/-- Bound on encoding based on tape content -/
theorem encode_config_bound (cfg : Cfg Bool Λ) :
    encode_config cfg ≤ 2^(Int.natAbs (leftmost_true_pos cfg)) - 1 := by sorry

/-- Single step can change encoding by at most a power of 2 -/
theorem encode_step_diff (M : Machine Bool Λ) (cfg cfg' : Cfg Bool Λ) :
    step M cfg = some cfg' →
    ∃ k : ℕ, |Int.ofNat (encode_config cfg') - Int.ofNat (encode_config cfg)| ≤ 2^k := by sorry

end LeftTM0