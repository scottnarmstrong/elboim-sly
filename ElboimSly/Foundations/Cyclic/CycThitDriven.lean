/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenDriven
public import ElboimSly.Foundations.Cyclic.CycRegenShift
public import ElboimSly.Foundations.Cyclic.CycRegenCut
public import Mathlib

/-!
# The regenerated driven walk and its hitting time

ES22 Lemma 2.1 (definitions), ES22 Lemma 2.1.

For a driving path `x` the regenerated walk `W^x_reg` glues the pieces `W^{x^{(i)}}`, where
`x^{(1)} = x` and `x^{(i+1)} = x^{(i)}(τ_i + ·) - x^{(i)}(τ_i)`, `τ_i = treg^{x^{(i)}}`. Then
`drivenThit` is `t_hit` of hitting the history; moving fast (`eq:cyc-thit`) for this walk, with `α(t)` the last
regeneration time at or before `t`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ}

/-- The successive driving paths `x^{(i)}` (indexed from `0`) of the regenerated driven walk. -/
noncomputable def drivenPieces (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) : ℕ → ℝ≥0 → Fin d → ℤ
  | 0 => x
  | n + 1 => shiftPath (drivenPieces b x n) (drivenTreg b (drivenPieces b x n)).toNNReal

/-- The regeneration times `σ_i = ∑_{k<i} treg^{x^{(k)}}`. -/
noncomputable def drivenSigma (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) : ℕ → ℝ≥0∞ :=
  partialSums fun k => drivenTreg b (drivenPieces b x k)

/-- The regenerated walk `W^x_reg` driven by `x`. -/
noncomputable def drivenRegenFrom (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) : ℝ≥0 → Fin d → ℤ :=
  drivenRegenWalk b (drivenPieces b x)

/-- `α(t)`: the last regeneration time at or before `t`. -/
noncomputable def drivenRegenAlpha (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) : ℝ≥0 :=
  (drivenSigma b x (gluedCount (drivenSigma b x) t)).toNNReal

/-- `t_hit(t) = inf {s > t : ∃ s' ∈ s + βℤ, α(t) < s' < t, ‖W(s) - W(s')‖ ≤ 1}` for the regenerated
driven walk `W = W^x_reg`. Hitting the history; moving fast, `eq:cyc-thit`. -/
noncomputable def drivenThit (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) : ℝ≥0∞ :=
  ⨅ s ∈ {s : ℝ≥0 | t < s ∧ ∃ k : ℤ, ∃ s' : ℝ≥0, (s' : ℝ) = s + k * b ∧
      drivenRegenAlpha b x t < s' ∧ s' < t ∧
      ‖drivenRegenFrom b x s - drivenRegenFrom b x s'‖ ≤ 1}, (s : ℝ≥0∞)

theorem drivenSigma_zero (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) : drivenSigma b x 0 = 0 := by
  simp [drivenSigma, partialSums]

theorem drivenSigma_one (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) : drivenSigma b x 1 = drivenTreg b x := by
  simp [drivenSigma, partialSums, drivenPieces]

theorem drivenSigma_succ (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) (n : ℕ) :
    drivenSigma b x (n + 1) = drivenSigma b x n + drivenTreg b (drivenPieces b x n) :=
  partialSums_succ _ _

theorem drivenSigma_mono (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) : Monotone (drivenSigma b x) :=
  monotone_nat_of_le_succ fun n => by rw [drivenSigma_succ]; exact le_self_add

theorem le_pathTreg (b : ℝ≥0) (w : ℝ≥0 → Fin d → ℤ) : (b : ℝ≥0∞) ≤ pathTreg b w := by
  refine le_iInf fun k => ?_
  have : (1 : ℝ≥0) ≤ k.1 := by exact_mod_cast k.2.1
  exact_mod_cast le_mul_of_one_le_left zero_le this

theorem gluedCount_eq {σ : ℕ → ℝ≥0∞} (hm : Monotone σ) {n : ℕ} {t : ℝ≥0} (h1 : σ n ≤ t)
    (h2 : (t : ℝ≥0∞) < σ (n + 1)) : gluedCount σ t = n := by
  unfold gluedCount
  apply le_antisymm
  · refine csSup_le ⟨n, h1⟩ fun k hk => ?_
    by_contra hkn
    have hk' : σ k ≤ t := hk
    exact absurd (lt_of_le_of_lt ((hm (Nat.succ_le_of_lt (not_le.1 hkn))).trans hk') h2)
      (lt_irrefl _)
  · refine le_csSup ⟨n, fun k hk => ?_⟩ h1
    by_contra hkn
    have hk' : σ k ≤ t := hk
    exact absurd (lt_of_le_of_lt ((hm (Nat.succ_le_of_lt (not_le.1 hkn))).trans hk') h2)
      (lt_irrefl _)

/-- Before the first closing time, the regenerated walk is `W^x` and `α = 0`. -/
theorem gluedCount_lt_treg (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < drivenTreg b x) : gluedCount (drivenSigma b x) t = 0 :=
  gluedCount_eq (drivenSigma_mono b x) (by rw [drivenSigma_zero]; exact zero_le)
    (by rw [drivenSigma_one]; exact ht)

theorem drivenRegenFrom_of_lt (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < drivenTreg b x) : drivenRegenFrom b x t = drivenWalk b x t := by
  unfold drivenRegenFrom drivenRegenWalk gluedWalk
  have : gluedCount (partialSums fun k => drivenTreg b (drivenPieces b x k)) t = 0 :=
    gluedCount_lt_treg b x ht
  rw [this]
  simp [partialSums, drivenPieces]

theorem drivenRegenAlpha_of_lt (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < drivenTreg b x) : drivenRegenAlpha b x t = 0 := by
  unfold drivenRegenAlpha
  rw [gluedCount_lt_treg b x ht, drivenSigma_zero]; rfl

/-- Just after the first closing time, the regenerated walk is at `0` (the next piece starts). -/
theorem drivenRegenFrom_after (b : ℝ≥0) (hb : 0 < b) {x : ℝ≥0 → Fin d → ℤ}
    (hx : IsRegPath x) {τ : ℝ≥0} (hτ : drivenTreg b x = τ) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ u : ℝ≥0, u < ε → drivenRegenFrom b x (τ + u) = 0 := by
  have hx1 : IsRegPath (drivenPieces b x 1) := isRegPath_shiftPath hx _
  obtain ⟨ε0, hε0, hε⟩ : ∃ ε0 : ℝ≥0, 0 < ε0 ∧ ∀ u : ℝ≥0, u < ε0 →
      drivenWalk b (drivenPieces b x 1) u = 0 := by
    have h := (drivenWalk_isRegPath hx1 hb).rc 0
    rw [drivenWalk_zero hx1 hb] at h
    have h' := (mem_nhdsGE_iff_exists_Ico_subset (a := (0 : ℝ≥0))).1 h
    obtain ⟨c, hc, hsub⟩ := h'
    exact ⟨c, hc, fun u hu => hsub ⟨zero_le, hu⟩⟩
  refine ⟨min ε0 b, lt_min hε0 hb, fun u hu => ?_⟩
  have hσ1 : drivenSigma b x 1 = (τ : ℝ≥0∞) := by rw [drivenSigma_one, hτ]
  have hσ2 : (drivenSigma b x 2 : ℝ≥0∞) = τ + drivenTreg b (drivenPieces b x 1) := by
    rw [drivenSigma_succ, hσ1]
  have hbt : (b : ℝ≥0∞) ≤ drivenTreg b (drivenPieces b x 1) := le_pathTreg _ _
  have hc : gluedCount (drivenSigma b x) (τ + u) = 1 := by
    refine gluedCount_eq (drivenSigma_mono b x) (by rw [hσ1]; exact_mod_cast le_self_add) ?_
    rw [hσ2]
    have : (u : ℝ≥0∞) < b := by exact_mod_cast lt_of_lt_of_le hu (min_le_right _ _)
    calc ((τ + u : ℝ≥0) : ℝ≥0∞) = τ + u := by push_cast; rfl
      _ < τ + b := ENNReal.add_lt_add_left (by simp) this
      _ ≤ _ := add_le_add le_rfl hbt
  unfold drivenRegenFrom drivenRegenWalk gluedWalk
  change drivenWalk b (drivenPieces b x
    (gluedCount (drivenSigma b x) (τ + u))) _ = 0
  have hc' : gluedCount (partialSums fun k => drivenTreg b (drivenPieces b x k)) (τ + u) = 1 := hc
  have hp : partialSums (fun k => drivenTreg b (drivenPieces b x k)) 1 = τ := hσ1
  rw [hc', hp]
  rw [hc]
  rw [ENNReal.toNNReal_coe, add_tsub_cancel_left]
  exact hε u (lt_of_lt_of_le hu (min_le_left _ _))

end ElboimSly.Cyclic

end
