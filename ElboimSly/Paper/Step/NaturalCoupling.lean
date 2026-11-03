/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Driven
public import ElboimSly.Paper.Step.Concatenation
public import Mathlib

/-!
# The natural coupling

The natural coupling (ES22 §7, ES22 §7).

For a path `Y` (the canonical SRW), an offset `a ≥ 0` and lengths `s 0, …, s (ℓ-1) > 0`, put
`S j = s 0 + ⋯ + s (j-1)` and `Z j := stepReg β (θ_{a + S j} Y)`, `W := Z 0`, `W_j := Z j |_{[0, s j]}`.
`stepNatTilde` is `W̃ = W_0 ⌢ ⋯ ⌢ W_{ℓ-1}`. Because `stepCatList` does not use the length of the last
path, it is also `W̃^∞ = W_0 ⌢ ⋯ ⌢ W_{ℓ-2} ⌢ Z_{ℓ-1}`; the two agree on `[0, S ℓ]` as in the
written proof (`stepNatTilde` is only meaningful there).
-/

@[expose] public section

open scoped NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The partial sums `S j = s 0 + ⋯ + s (j-1)`. -/
def stepPartial (s : ℕ → ℝ≥0) (j : ℕ) : ℝ≥0 := ∑ i ∈ Finset.range j, s i

/-- The `j`-th driven regenerated walk `Z j = W_reg^{θ_{a + S j} Y}`. -/
noncomputable def stepWalkZ (β : ℝ) (a : ℝ≥0) (s : ℕ → ℝ≥0) (Y : ℝ≥0 → Fin d → ℤ) (j : ℕ) :
    ℝ≥0 → Fin d → ℤ :=
  stepReg β (stepShift (a + stepPartial s j) Y)

/-- The concatenation `W̃` (equivalently `W̃^∞`, on `[0, S ℓ]`). -/
noncomputable def stepNatTilde (β : ℝ) (a : ℝ≥0) (s : ℕ → ℝ≥0) (ℓ : ℕ)
    (Y : ℝ≥0 → Fin d → ℤ) : ℝ≥0 → Fin d → ℤ :=
  stepCatList ((List.range ℓ).map fun j => (s j, stepWalkZ β a s Y j))

theorem stepWalkZ_zero (β : ℝ) (a : ℝ≥0) (s : ℕ → ℝ≥0) (Y : ℝ≥0 → Fin d → ℤ) :
    stepWalkZ β a s Y 0 = stepReg β (stepShift a Y) := by
  simp [stepWalkZ, stepPartial]

/-- For `ℓ = 1`, `W̃ = W`. -/
theorem stepNatTilde_one (β : ℝ) (a : ℝ≥0) (s : ℕ → ℝ≥0) (Y : ℝ≥0 → Fin d → ℤ) :
    stepNatTilde β a s 1 Y = stepReg β (stepShift a Y) := by
  simp [stepNatTilde, stepCatList, stepWalkZ_zero]

end ElboimSly.Paper
