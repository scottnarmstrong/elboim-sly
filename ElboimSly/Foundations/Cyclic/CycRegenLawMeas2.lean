/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenLawMeas
public import ElboimSly.Foundations.Cyclic.CycRegenDrivenShift
public import ElboimSly.Foundations.Cyclic.CycRegenDrivenPieces
public import Mathlib

/-!
# Measurability of the driven regenerated walks

The constructions of the regenerated walk (ii), (iii).

* `measurable_drivenRegenWalk_at`: construction (ii), the walk `W_reg` built from a measurable
  family `Y k` of driving paths, is measurable in the parameter;
* `drivenRegenWalkCut_eq_drivenRegenFrom`: construction (iii), the pieces of one path cut at the
  regeneration times, equals `W^x_reg` (`drivenRegenFrom`), whose measurability is
  `measurable_drivenRegenFrom_at`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {b : ℝ≥0}

section Meas

variable {α : Type*} [MeasurableSpace α]

theorem measurable_drivenRegenWalk_at (hb : 0 < b) {Y : ℕ → α → CPath (Fin d → ℤ)}
    (hY : ∀ k, Measurable (Y k)) (t : ℝ≥0) :
    Measurable fun a => drivenRegenWalk b (fun k => (Y k a).fn) t := by
  have hσ : ∀ n, Measurable fun a => partialSums (fun k => drivenTreg b (Y k a).fn) n := fun n =>
    Finset.measurable_sum _ fun k _ => (measurable_drivenTreg hb).comp (hY k)
  have hF : ∀ n, Measurable fun a => drivenWalk b (Y n a).fn
      (t - (partialSums (fun k => drivenTreg b (Y k a).fn) n).toNNReal) := fun n =>
    measurable_drivenWalk_at (X := Y n) hb (hY n)
      (measurable_const.sub (ENNReal.measurable_toNNReal.comp (hσ n)))
  exact measurable_index (measurable_gluedCount_of hσ t) hF

end Meas

variable {x : ℝ≥0 → Fin d → ℤ}

theorem cutTimes_eq_drivenSigma (h0 : x 0 = 0) (k : ℕ) :
    cutTimes b x k = drivenSigma b x k ∧
      (drivenSigma b x k < ⊤ → drivenPieces b x k = shiftPath x (drivenSigma b x k).toNNReal) := by
  induction k with
  | zero =>
    refine ⟨by simp [cutTimes, drivenSigma_zero], fun _ => ?_⟩
    funext s
    simp [drivenPieces, drivenSigma_zero, shiftPath_apply, h0]
  | succ k ih =>
    obtain ⟨hc, hp⟩ := ih
    by_cases htop : drivenSigma b x k = ⊤
    · have h1 : cutTimes b x (k + 1) = ⊤ := by
        show cutTimes b x k + _ = _
        rw [hc, htop, top_add]
      have h2 : drivenSigma b x (k + 1) = ⊤ := by
        rw [drivenSigma_succ, htop, top_add]
      exact ⟨h1.trans h2.symm, fun h => absurd h (by rw [h2]; exact lt_irrefl _)⟩
    · have hlt : drivenSigma b x k < ⊤ := lt_top_iff_ne_top.2 htop
      have hpk := hp hlt
      refine ⟨?_, fun hlt' => ?_⟩
      · show cutTimes b x k + drivenTreg b (shiftPath x (cutTimes b x k).toNNReal) = _
        rw [drivenSigma_succ, hc, ← hc, hpk]
        simp [hc]
      · obtain ⟨h1, h2⟩ := drivenSigma_succ_lt hlt'
        rw [drivenPieces, hpk, shiftPath_add]
        congr 1
        rw [drivenSigma_succ, ENNReal.toNNReal_add h1.ne h2.ne, hpk]

theorem drivenRegenWalkCut_eq_drivenRegenFrom (hb : 0 < b) (h0 : x 0 = 0) (t : ℝ≥0) :
    drivenRegenWalkCut b x t = drivenRegenFrom b x t := by
  have hc : cutTimes b x = drivenSigma b x := funext fun k => (cutTimes_eq_drivenSigma h0 k).1
  obtain ⟨hs1, -⟩ := gluedCount_spec' hb x t
  have hlt : drivenSigma b x (gluedCount (drivenSigma b x) t) < ⊤ :=
    lt_of_le_of_lt hs1 ENNReal.coe_lt_top
  have hp := (cutTimes_eq_drivenSigma h0 (gluedCount (drivenSigma b x) t)).2 hlt
  unfold drivenRegenWalkCut drivenRegenFrom drivenRegenWalk gluedWalk
  rw [hc]
  show cutPiece b x _ _ = _
  unfold cutPiece
  rw [hc, ← hp]
  rfl

end ElboimSly.Cyclic

end
