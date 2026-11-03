/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.CoreRel
public import ElboimSly.Paper.Avoid.CoreBad
public import ElboimSly.Paper.Avoid.CoreParams
public import ElboimSly.Foundations.Brownian.Freeze
public import Mathlib

/-!
# ES22 §4: Lemma 4.1, core form

ES22 Lemma 4.1 (ES22 Lemma 4.1 proof, ES22 §4).

Let `ℋ ≤ 𝒜'` be a `σ`-algebra, `a ≤ T` be `ℋ`-measurable, `w` a random path whose recorded history
`h(s) = w((a + s) ∧ T)` is `ℋ`-measurable (jointly in `(ω, s)`) and right-continuous, and `X̃` a
process with right-continuous paths, independent of `ℋ`, with the law of the regenerated walk `W`.
Put `W'(r) = w(T) + X̃(r)`. Then `Rel = {T relaxed along w|[a,T]} ∈ ℋ` and for every `A ∈ ℋ`,
`A ⊆ Rel`: `P(A ∩ {τ' ≥ 4ⁿ}) ≥ (1 - C β^{-δ/30}) P(A)`, i.e.
`P(τ' ≥ 4ⁿ | ℋ) ≥ 1 - C β^{-δ/30}` a.s. on `Rel`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

variable {d : ℕ}

/-- The right side of the exponent: `C` times `β^{-δ/30}`. -/
theorem half_pow_le {β : ℝ} (hβ1 : 1 ≤ β) (δ : ℝ) (_hδ : 0 < δ) :
    (β ^ δ / 2) ^ (-(1 : ℝ) / 30) ≤ 2 * β ^ (-δ / 30) := by
  have hβ0 : 0 < β := by linarith
  have hb : 0 < β ^ δ := Real.rpow_pos_of_pos hβ0 _
  rw [Real.div_rpow hb.le (by norm_num), ← Real.rpow_mul hβ0.le]
  have e1 : (2 : ℝ) ^ (-(1 : ℝ) / 30) = ((2 : ℝ) ^ ((1 : ℝ) / 30))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num)]; congr 1; ring
  have e2 : (2 : ℝ) ^ ((1 : ℝ) / 30) ≤ 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 30) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have e3 : β ^ (δ * (-(1 : ℝ) / 30)) = β ^ (-δ / 30) := by congr 1; ring
  rw [e3, e1, div_eq_mul_inv, inv_inv]
  have hp : 0 < β ^ (-δ / 30) := Real.rpow_pos_of_pos hβ0 _
  nlinarith

end ElboimSly.Paper

end
