/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycHitThit
public import ElboimSly.Foundations.Cyclic.CycHitCov
public import ElboimSly.Foundations.Cyclic.CycRegion
public import Mathlib

/-!
# ES22 Lemma 2.1, Step 2: agreement

ES22 Lemma 2.1, Step 2. For good `ν`, `ν'` that agree off the explored region
`ℛ_{(0,t]}(W)`, the recentred walk of `ν'` from `(W(t), t)` follows `W(t + ·) - W(t)` up to the
hitting time `τ̂_hit(t)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν ν' : Measure (RingSpace d β)}

theorem norm_le_one_of_lt_two (w : Fin d → ℤ) (h : ‖w‖ < 2) : ‖w‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have h1 : ‖w i‖ < 2 := (norm_le_pi_norm w i).trans_lt h
  rw [Int.norm_eq_abs] at h1 ⊢
  have h2 : |w i| < 2 := by exact_mod_cast h1
  have h3 : |w i| ≤ 1 := by omega
  exact_mod_cast h3

/-- The regions explored before and after `t` are disjoint up to the hitting time. -/
theorem region_disjoint_of_hit {t s : ℝ≥0}
    (hs : ((t + s : ℝ≥0) : ℝ≥0∞) ≤ cycHatThit β (fun r => ElboimSly.cycWalk ν 0 0 r) t) :
    Disjoint (cycRegion β (fun r => ElboimSly.cycWalk ν 0 0 r) (t : ℝ) ((t + s : ℝ≥0) : ℝ))
      (cycRegion β (fun r => ElboimSly.cycWalk ν 0 0 r) 0 (t : ℝ)) := by
  refine cyc_disjoint _ fun s₁ hs₁ s₂ hs₂ z z' hz hz' ⟨k, hk⟩ => ?_
  by_contra hcon
  rw [not_le] at hcon
  have h1 := norm_le_one_of_lt_two _ hcon
  obtain ⟨l, hl, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hz
  obtain ⟨l', hl', hsub'⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hz'
  have hl1 : l < s₁ := hl
  have hl1' : l' < s₂ := hl'
  have hs₁t : (t : ℝ) < s₁ := hs₁.1
  have hs₁u : s₁ ≤ ((t + s : ℝ≥0) : ℝ) := hs₁.2
  have hs₂0 : 0 < s₂ := hs₂.1
  have hs₂t : s₂ ≤ (t : ℝ) := hs₂.2
  set ε : ℝ := min (min (s₁ - l) (s₂ - l')) (min (s₁ - t) s₂) / 2 with hε
  have hpos : 0 < min (min (s₁ - l) (s₂ - l')) (min (s₁ - t) s₂) :=
    lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) hs₂0)
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hle1 : min (min (s₁ - l) (s₂ - l')) (min (s₁ - t) s₂) ≤ s₁ - l :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hle2 : min (min (s₁ - l) (s₂ - l')) (min (s₁ - t) s₂) ≤ s₂ - l' :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hle3 : min (min (s₁ - l) (s₂ - l')) (min (s₁ - t) s₂) ≤ s₁ - t :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hle4 : min (min (s₁ - l) (s₂ - l')) (min (s₁ - t) s₂) ≤ s₂ :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hu1 : (t : ℝ) < s₁ - ε := by rw [hε]; linarith
  have hu2 : 0 < s₂ - ε := by rw [hε]; linarith
  have hz1 : ElboimSly.cycWalk ν 0 0 (s₁ - ε) = z :=
    hsub ⟨by rw [hε]; linarith, by linarith⟩ hu1
  have hz2 : ElboimSly.cycWalk ν 0 0 (s₂ - ε) = z' :=
    hsub' ⟨by rw [hε]; linarith, by linarith⟩ hu2
  have hT : (t : ℝ) ≠ 0 := by linarith
  have hτ := cycHatThit_le (β := β) (W := fun r => ElboimSly.cycWalk ν 0 0 r) (T := t)
    (s := s₁ - ε) (s' := s₂ - ε) hT hu1 (-k) (by push_cast; linarith) hu2 (by linarith) (by
      simp only [hz1, hz2]; exact h1)
  have h3 : ENNReal.ofReal (s₁ - ε) < ENNReal.ofReal s₁ :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have h4 : ENNReal.ofReal s₁ ≤ ((t + s : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hs₁u
  exact absurd (hτ.trans_lt (h3.trans_le (h4.trans hs))) (lt_irrefl _)

/-- ES22 Lemma 2.1, Step 2: if `ν'` is good and agrees with `ν` off the region
`ℛ_{(0,t]}(W)`, then the walk of `(φ_{(W(t), t)})_* ν'` follows `W(t + ·) - W(t)` up to `τ̂_hit(t)`. -/
theorem hit_agree (hν : Good ν) (hν' : Good ν') (t : ℝ≥0)
    (hag : ν'.restrict (cycRegion β (fun r => ElboimSly.cycWalk ν 0 0 r) 0 (t : ℝ))ᶜ =
      ν.restrict (cycRegion β (fun r => ElboimSly.cycWalk ν 0 0 r) 0 (t : ℝ))ᶜ)
    (s : ℝ≥0)
    (hs : ((t + s : ℝ≥0) : ℝ≥0∞) ≤ cycHatThit β (fun r => ElboimSly.cycWalk ν 0 0 r) t) :
    ElboimSly.cycWalk (ν'.map (hitPhi (ElboimSly.cycWalk ν 0 0 t) (t : ℝ))) 0 0 (s : ℝ) =
      ElboimSly.cycWalk ν 0 0 ((t : ℝ) + s) - ElboimSly.cycWalk ν 0 0 t := by
  have hx : ElboimSly.cycWalk ν 0 0 (t : ℝ) = fwdTraj hν 0 0 (t : ℝ) := by
    rw [cycWalk_of_nonneg hν 0 0 (NNReal.coe_nonneg t), zero_add]
  have hW : ∀ u ∈ Icc (t : ℝ) ((t : ℝ) + s), fwdTraj hν (fwdTraj hν 0 0 (t : ℝ)) t u =
      ElboimSly.cycWalk ν 0 0 u := by
    intro u hu
    have hu0 : 0 ≤ u := (NNReal.coe_nonneg t).trans hu.1
    rw [cycWalk_of_nonneg hν 0 0 hu0, zero_add]
    exact (fwdTraj_restart hν 0 (NNReal.coe_nonneg t) hu.1).symm
  have hreg : cycRegion β (fwdTraj hν (fwdTraj hν 0 0 (t : ℝ)) t) (t : ℝ) ((t : ℝ) + s) =
      cycRegion β (fun r => ElboimSly.cycWalk ν 0 0 r) (t : ℝ) ((t : ℝ) + s) :=
    cycRegion_congr hW
  have hdis := region_disjoint_of_hit (ν := ν) hs
  have hsub : cycRegion β (fun r => ElboimSly.cycWalk ν 0 0 r) (t : ℝ) ((t : ℝ) + s) ⊆
      (cycRegion β (fun r => ElboimSly.cycWalk ν 0 0 r) 0 (t : ℝ))ᶜ :=
    fun p hp hp' => Set.disjoint_left.1 (by simpa using hdis) hp hp'
  have hres : ν.restrict (cycRegion β (fwdTraj hν (fwdTraj hν 0 0 (t : ℝ)) t) (t : ℝ)
      ((t : ℝ) + s)) = ν'.restrict (cycRegion β (fwdTraj hν (fwdTraj hν 0 0 (t : ℝ)) t) (t : ℝ)
      ((t : ℝ) + s)) := by
    rw [hreg, ← Measure.restrict_restrict_of_subset hsub (μ := ν),
      ← Measure.restrict_restrict_of_subset hsub (μ := ν'), hag]
  obtain ⟨hloc, -⟩ := cyc_locality hν hν' (fwdTraj hν 0 0 (t : ℝ)) (le_add_of_nonneg_right (NNReal.coe_nonneg s)) hres
  rw [hx, cycWalk_map_hitPhi hν' _ _ (NNReal.coe_nonneg s), cycWalk_of_nonneg hν' _ _ (NNReal.coe_nonneg s)]
  have := hloc ((t : ℝ) + s) ⟨le_add_of_nonneg_right (NNReal.coe_nonneg s), le_rfl⟩
  rw [this, ← hW _ ⟨le_add_of_nonneg_right (NNReal.coe_nonneg s), le_rfl⟩]

end ElboimSly.Cyclic

end
