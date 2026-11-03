/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycThitDrivenStep3
public import Mathlib

/-!
# ES22 Lemma 2.1: Lemma 2.1, pathwise driven form

ES22 Lemma 2.1 (§2).

Let `x ∈ cycCF`, `W = w^x`, and `t_hit = drivenThit b x` the hitting time (`eq:cyc-thit`) of the
regenerated driven walk with first piece `W`. For `x' = x(t + ·) - x(t)` (`shiftPath x t`) and
`0 < t < treg^x`: `t_hit(t) ≤ treg^x`, `treg^{x'} > t_hit(t) - t` (both infinite if `t_hit(t) = ∞`),
and `W(t + s) - W(t) = W^{x'}(s)` for all `s ∈ [0, t_hit(t) - t]`. For `t = 0`, `x' = x`.

Statement differences: the written proof's "`treg^{X'} > t_hit(t) - t`" is stated in `ℝ≥0∞` as
`t_hit < ⊤ → t_hit < t + treg^{x'}` together with `t_hit = ⊤ → treg^{x'} = ⊤`, the case `t_hit = ∞`
being where the strict inequality reads `∞ > ∞`. The walk `w^{x'}` is defined for all times, so the
identity needs no restriction to `[0, treg^{x'})`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {b : ℝ≥0} {x : ℝ≥0 → Fin d → ℤ}

/-- For `t = 0`, `X' = X`. -/
theorem shiftPath_zero (hx : IsDrivingPath x) : shiftPath x 0 = x := by
  funext s; simp [shiftPath_apply, hx.zero]

/-- **ES22 Lemma 2.1** (ES22 Lemma 2.1, pathwise driven form). -/
theorem cyc_hit_couple_driven (hb : 0 < b) (hx : x ∈ CycCF b) {t : ℝ≥0} (ht0 : 0 < t)
    (htτ : (t : ℝ≥0∞) < drivenTreg b x) :
    drivenThit b x t ≤ drivenTreg b x ∧
    (drivenThit b x t = ⊤ → drivenTreg b (shiftPath x t) = ⊤) ∧
    (drivenThit b x t < ⊤ → drivenThit b x t < t + drivenTreg b (shiftPath x t)) ∧
    ∀ s : ℝ≥0, ((t + s : ℝ≥0) : ℝ≥0∞) ≤ drivenThit b x t →
      drivenWalk b x (t + s) - drivenWalk b x t = drivenWalk b (shiftPath x t) s := by
  refine ⟨drivenThit_le_treg hb hx ht0 htτ, fun htop => ?_, fun hlt => ?_,
    fun s hs => step2 hb hx ht0 htτ hs s le_rfl⟩
  · by_contra hne
    obtain ⟨T0, hT0⟩ : ∃ T0 : ℝ≥0, drivenTreg b (shiftPath x t) = T0 :=
      ⟨_, (ENNReal.coe_toNNReal hne).symm⟩
    exact step3 hb hx ht0 htτ hT0 (by rw [htop]; exact le_top)
  · by_cases htop : drivenTreg b (shiftPath x t) = ⊤
    · rw [htop]; simpa using hlt
    · obtain ⟨T0, hT0⟩ : ∃ T0 : ℝ≥0, drivenTreg b (shiftPath x t) = T0 :=
        ⟨_, (ENNReal.coe_toNNReal htop).symm⟩
      rw [hT0]
      by_contra hge
      rw [not_lt] at hge
      exact step3 hb hx ht0 htτ hT0 (by exact_mod_cast hge)

end ElboimSly.Cyclic

end
