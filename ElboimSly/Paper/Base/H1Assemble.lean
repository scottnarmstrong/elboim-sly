/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.H1Lag2
public import ElboimSly.Paper.Base.H1Occ
public import Mathlib

/-!
# (H1) at the base: the deterministic assembly

ES22 Lemma 8.1, Steps 2 to 4 on a good sample point.

* `h1_relTimes_of_good`: on the good events, the relaxed times of the path have measure at least
  `19 T / 20`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Brownian

variable {d : ℕ}

theorem h1_relTimes_of_good {Ω : Type*} (hd : 1 ≤ d) (B : ℝ≥0 → Ω → Fin d → ℝ) (ω : Ω)
    (γ : SRW.PathSpace d) (T : ℝ≥0) {n : ℕ} (hn : 2 ≤ n) {β : ℝ} (hβ : 0 < β)
    (hTβ : (T : ℝ) ≤ β) (hb4 : 4 ≤ β ^ indDelta d)
    (hB3 : 20 ≤ (β ^ indDelta d / 2) ^ (es8Zeta d ^ 3))
    {R : ℝ} {M m0 : ℕ} (hR : 0 ≤ R) (hM : (2 * R + 1) ^ d ≤ (M : ℝ) ^ (5 / 2 : ℝ))
    (hm2 : 2 * (n : ℝ) ^ 10 ≤ m0) (hm5 : (5 * (n : ℝ) ^ 10) ^ ((5 * d : ℝ) / 2) < m0)
    (hm0b : (m0 : ℝ) ≤ β ^ indDelta d)
    (hg : H1Good n T R M m0 γ (fun u => B u ω))
    (hlag : ω ∉ h1LagEvent d (β ^ indDelta d) T B) :
    ENNReal.ofReal (19 / 20 * (T : ℝ)) ≤ volume (h1RelTimes β T γ) := by
  have hn10 : 2 * (n : ℝ) ^ 10 ≤ β ^ indDelta d := hm2.trans hm0b
  refine h1_relTimes_volume (fun t _ htT r hr => ?_) ?_
  · exact h1_not_heavy hn hg hR hM hm2 hm5 htT (hm0b.trans hr)
  · exact h1_badTimes_volume_le hd B ω γ T hβ hTβ hb4 hn10 hB3 hg.cpl hlag

end ElboimSly.Paper

end
