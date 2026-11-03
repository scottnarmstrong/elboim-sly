/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMergeMeas
import Mathlib

/-!
# Joint measurability of the cyclic walk; negative powers of `π_β`

Measurability (`W_{u,q}(t)` for all `t`, jointly measurable in `(ν, t)`;
`π_β^k` for `k ∈ ℤ`).
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- `(ν, q, s) ↦ W^ν_{u,q}(s)` is measurable on the good configurations, for all real `s`. -/
theorem measurable_cycWalk_joint (u : Fin d → ℤ) :
    Measurable (fun p : GoodSet d β × ℝ × ℝ => cycWalk p.1.1 u p.2.1 p.2.2) := by
  have hq : Measurable (fun p : GoodSet d β × ℝ × ℝ => p.2.1) := measurable_fst.comp measurable_snd
  have hs : Measurable (fun p : GoodSet d β × ℝ × ℝ => p.2.2) := measurable_snd.comp measurable_snd
  have hqs : Measurable (fun p : GoodSet d β × ℝ × ℝ => p.2.1 + p.2.2) := hq.add hs
  have hF : Measurable (fun p : GoodSet d β × ℝ × ℝ => fwdTraj p.1.2 u p.2.1 (p.2.1 + p.2.2)) :=
    (measurable_fwdTraj u).comp (measurable_fst.prodMk (hq.prodMk hqs))
  have hB : Measurable (fun p : GoodSet d β × ℝ × ℝ => bwdTraj p.1.2 u p.2.1 (p.2.1 + p.2.2)) :=
    (measurable_bwdTraj u).comp (measurable_fst.prodMk (hq.prodMk hqs))
  have e : (fun p : GoodSet d β × ℝ × ℝ => cycWalk p.1.1 u p.2.1 p.2.2) = fun p =>
      if 0 ≤ p.2.2 then fwdTraj p.1.2 u p.2.1 (p.2.1 + p.2.2)
      else bwdTraj p.1.2 u p.2.1 (p.2.1 + p.2.2) := by
    funext p
    by_cases h : 0 ≤ p.2.2
    · simp only [h, ite_true]; exact cycWalk_of_nonneg p.1.2 u p.2.1 h
    · simp only [h, ite_false]; exact cycWalk_of_nonpos p.1.2 u p.2.1 (not_le.mp h).le
  rw [e]
  exact Measurable.ite (measurableSet_le measurable_const hs) hF hB

end ElboimSly.Cyclic

end
