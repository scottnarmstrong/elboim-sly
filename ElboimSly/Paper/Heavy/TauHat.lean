/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Agree

/-!
# The stopping times `τ̌` and `τ̂`

The stopping times checkτ and hatτ; The functionals before closing.

* `heavyTauCheck`: `τ̌(w) = T(w) ∧ τ_fast ∧ τ_jump ∧ τ' ∧ τ_bad` for a cyclic path `w`.
* `heavyTauHat`: `τ̂(w) = t_n ∧ τ̌(w)`.
* `heavyTauHatReg tReg`: for the regenerated walk, `t_n ∧ T_reg ∧ τ_fast ∧ τ_jump ∧ τ' ∧ τ_bad`
  (`tReg` the first regeneration time).
* `heavyTauCheck_le_iff_of_agree`, `heavyTauHatReg_le_iff_of_agree`: the functionals before closing.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ}

/-- The stopping times checkτ and hatτ. `τ̌(w) = T(w) ∧ τ_fast(w) ∧ τ_jump(w) ∧ τ'(w) ∧ τ_bad(w)`. -/
noncomputable def heavyTauCheck (d : ℕ) (β t₀ : ℝ) (n : ℕ) (w : ℝ → Fin d → ℤ) : ℝ≥0∞ :=
  min (cycClosingTime β w) (min (pathTfastCube w n) (min (pathTjumpCube w n)
    (min (heavyTauPrime d t₀ n w) (heavyTauBad d β t₀ n w))))

/-- The stopping times checkτ and hatτ. `τ̂(w) = t_n ∧ τ̌(w)`. -/
noncomputable def heavyTauHat (d : ℕ) (β t₀ : ℝ) (n : ℕ) (w : ℝ → Fin d → ℤ) : ℝ≥0∞ :=
  min (ENNReal.ofReal (indScale t₀ n)) (heavyTauCheck d β t₀ n w)

/-- The stopping times checkτ and hatτ, regenerated walk. `τ̂ = t_n ∧ T_reg ∧ τ_fast ∧ τ_jump ∧ τ' ∧
τ_bad`; `tReg` is the first regeneration time `T_reg`. -/
noncomputable def heavyTauHatReg (d : ℕ) (β t₀ : ℝ) (n : ℕ) (tReg : ℝ≥0∞)
    (w : ℝ → Fin d → ℤ) : ℝ≥0∞ :=
  min (min (ENNReal.ofReal (indScale t₀ n)) tReg) (min (pathTfastCube w n) (min (pathTjumpCube w n)
    (min (heavyTauPrime d t₀ n w) (heavyTauBad d β t₀ n w))))

variable {w w' : ℝ → Fin d → ℤ} {β t₀ : ℝ} {n : ℕ}

/-- The functionals before closing for `τ̌`. -/
theorem heavyTauCheck_le_iff_of_agree (hw : IsCyclicPath w) (hw' : IsCyclicPath w') (hβ : 0 < β)
    (htk : 0 ≤ heavyTkPrime d t₀ n) (hn : 1 ≤ n) {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ s ∈ Icc 0 T, w s = w' s) :
    heavyTauCheck d β t₀ n w ≤ ENNReal.ofReal T ↔ heavyTauCheck d β t₀ n w' ≤ ENNReal.ofReal T := by
  have hL : 0 < (n : ℝ) ^ 3 := by positivity
  unfold heavyTauCheck pathTfastCube pathTjumpCube
  simp only [min_le_iff]
  rw [cycClosingTime_le_iff_of_agree hβ hT h, pathTfast_le_iff_of_agree hw hw' hL hT h,
    pathTjump_le_iff_of_agree hw hw' hL h, heavyTauPrime_le_iff_of_agree hw hw' hn hT h,
    heavyTauBad_le_iff_of_agree hw hw' hβ htk hT h]

/-- The functionals before closing for the regenerated-walk `τ̂` (with the same `T_reg`). -/
theorem heavyTauHatReg_le_iff_of_agree (hw : IsCyclicPath w) (hw' : IsCyclicPath w') (hβ : 0 < β)
    (htk : 0 ≤ heavyTkPrime d t₀ n) (hn : 1 ≤ n) (tReg : ℝ≥0∞) {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ s ∈ Icc 0 T, w s = w' s) :
    heavyTauHatReg d β t₀ n tReg w ≤ ENNReal.ofReal T ↔
      heavyTauHatReg d β t₀ n tReg w' ≤ ENNReal.ofReal T := by
  have hL : 0 < (n : ℝ) ^ 3 := by positivity
  unfold heavyTauHatReg pathTfastCube pathTjumpCube
  simp only [min_le_iff]
  rw [pathTfast_le_iff_of_agree hw hw' hL hT h,
    pathTjump_le_iff_of_agree hw hw' hL h, heavyTauPrime_le_iff_of_agree hw hw' hn hT h,
    heavyTauBad_le_iff_of_agree hw hw' hβ htk hT h]

end ElboimSly.Paper
