/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenEnv
public import Mathlib

/-!
# The constructions of the regenerated walk (i): the glued walk is `regenWalk`

The constructions of the regenerated walk (i). The gluing `gluedWalk` of the pieces `cycWalk (ν k) 0 0` at the
partial sums of `cycTreg (ν k)` is `regenWalk ν` of regenerated cyclic walk.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
theorem gluedCount_coe (ν : ℕ → Measure (RingSpace d β)) (t : ℝ≥0) :
    gluedCount (partialSums fun k => ElboimSly.cycTreg (ν k)) t =
      ElboimSly.regenCount ν (t : ℝ) := by
  unfold gluedCount ElboimSly.regenCount ElboimSly.regenSigma partialSums
  rw [ENNReal.ofReal_coe_nnreal]

theorem sigma_gluedCount_le (σ : ℕ → ℝ≥0∞) (h0 : σ 0 = 0) (t : ℝ≥0) :
    σ (gluedCount σ t) ≤ t := by
  by_cases hb : BddAbove {k : ℕ | σ k ≤ t}
  · exact Nat.sSup_mem ⟨0, by simp [h0]⟩ hb
  · unfold gluedCount
    rw [Nat.sSup_of_not_bddAbove hb]
    simp [h0]

omit [Fact (0 < β)] in
/-- The gluing of the slice walks is the regenerated walk of regenerated cyclic walk. -/
theorem gluedWalk_eq_regenWalk (ν : ℕ → Measure (RingSpace d β)) (t : ℝ≥0) :
    gluedWalk (partialSums fun k => ElboimSly.cycTreg (ν k))
        (fun k s => ElboimSly.cycWalk (ν k) 0 0 (s : ℝ)) t = ElboimSly.regenWalk ν (t : ℝ) := by
  have h0 : partialSums (fun k => ElboimSly.cycTreg (ν k)) 0 = 0 := by simp [partialSums]
  have hle := sigma_gluedCount_le _ h0 t
  unfold gluedWalk ElboimSly.regenWalk ElboimSly.regenStart
  rw [← gluedCount_coe]
  beta_reduce
  rw [NNReal.coe_sub (by simpa using ENNReal.toNNReal_mono ENNReal.coe_ne_top hle)]
  rfl

/-- **the constructions of the regenerated walk (i)**: for a good environment, `W_reg` of the environment final record
of `𝒫_reg` is the regenerated walk built from the slices `ν^k`. -/
theorem regRecWalk_envFinal_eq_regenWalk {ν : Measure (ℕ × RingSpace d β)} (hν : CycGood ν)
    (t : ℝ≥0) :
    regRecWalk ((regPlan d β).envFinal ν) t =
      ElboimSly.regenWalk (fun k => cycSlice k ν) (t : ℝ) := by
  rw [regRecWalk_envFinal hν, gluedWalk_eq_regenWalk]

end ElboimSly.Cyclic

end
