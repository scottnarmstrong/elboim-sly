/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.ReversalLaw
public import Mathlib

/-!
# Time reversal of the walk

Time reversal.

For `N` a Poisson point process with intensity `clockIntensity (Dir d)`, `T > 0` and
`X = canonical d N`, the reversed walk is `X̂ = revPath T X`, `X̂(u) = X(T) - X((T-u)-)` for `u < T`
and `X̂(u) = X(T)` for `u ≥ T`.

* (a) `isRegularPath_revPath_canonical` (all paths regular) and `reversal_law` (the stopped
  processes `X̂(· ∧ T)` and `-X̂(· ∧ T)` both have the law of `X(· ∧ T)`).
* (b) `ae_range_revPath_canonical`: almost surely
  `{X(s) : s ∈ [0,T]} = {X(T) - X̂(u) : u ∈ [0,T]}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : Ω → Measure (Dir d × ℝ)}
  {P : Measure Ω}

/-- The sign-flipping permutation of the directions. -/
def negPerm (d : ℕ) : Dir d ≃ Dir d := Equiv.prodCongr (Equiv.refl _) Equiv.boolNot

theorem vec_negPerm (v : Dir d) : (negPerm d v).vec = -v.vec := by
  obtain ⟨i, b⟩ := v
  cases b <;> simp [negPerm, Dir.vec, ← Pi.single_neg]

theorem pastFun_revProc_neg (T : ℝ≥0) (ν : Measure (Dir d × ℝ)) :
    pastFun d T (revProc (negPerm d) T ν) = fun s => -pastFun d T (revProc (Equiv.refl _) T ν) s := by
  funext s
  rw [pastFun_revProc, pastFun_revProc, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [vec_negPerm]
  simp

omit mΩ in
/-- Time reversal (a), regularity. -/
theorem isRegularPath_revPath_canonical (N : Ω → Measure (Dir d × ℝ)) (T : ℝ≥0) (ω : Ω) :
    IsRegularPath (revPath T (canonical d N ω)) :=
  isRegularPath_revPath_can (N ω) T

/-- Time reversal (a), law: the stopped reversed walk and its negative have the
law of the stopped walk. -/
theorem reversal_law (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (T : ℝ≥0) :
    AEMeasurable (fun ω => stopPath T (revPath T (canonical d N ω))) P ∧
    P.map (fun ω => stopPath T (revPath T (canonical d N ω))) =
      P.map (fun ω => stopPath T (canonical d N ω)) ∧
    P.map (fun ω u => -stopPath T (revPath T (canonical d N ω)) u) =
      P.map (fun ω => stopPath T (canonical d N ω)) := by
  have hrestr := hN.restrict
    (MeasurableSet.univ.prod (measurableSet_Ioc (a := (0 : ℝ)) (b := (T : ℝ))))
  have hΦ := measurable_pastFun d T
  have hlaw : ∀ σ : Dir d ≃ Dir d,
      P.map (fun ω => pastFun d T (revProc σ T (N ω))) =
        P.map (fun ω => stopPath T (canonical d N ω)) := by
    intro σ
    have h1 := hrestr.map_eq_map (isPPP_revProc hN σ T)
    have h2 := IsPoissonPointProcess.map_comp (P := P) (isPPP_revProc hN σ T).measurable hΦ
    have h3 := IsPoissonPointProcess.map_comp (P := P) hrestr.measurable hΦ
    rw [h2, h1, ← h3]
    exact Measure.map_congr (by
      filter_upwards [stopPath_canonical_ae hN T] with ω hω using hω.symm)
  have hae : ∀ᵐ ω ∂P, stopPath T (revPath T (canonical d N ω)) =
      pastFun d T (revProc (Equiv.refl _) T (N ω)) := by
    filter_upwards [ae_good hN, ae_tot_singleton_eq_zero hN (T : ℝ)] with ω h1 h2
    exact stopPath_revPath_can_eq h1 h2
  have hmeas : ∀ σ : Dir d ≃ Dir d,
      Measurable fun ω => pastFun d T (revProc σ T (N ω)) := fun σ =>
    hΦ.comp (isPPP_revProc hN σ T).measurable
  refine ⟨(hmeas _).aemeasurable.congr (hae.mono fun ω h => h.symm), ?_, ?_⟩
  · rw [Measure.map_congr hae]; exact hlaw _
  · have : (fun ω u => -stopPath T (revPath T (canonical d N ω)) u) =ᵐ[P]
        fun ω => pastFun d T (revProc (negPerm d) T (N ω)) := by
      filter_upwards [hae] with ω h
      rw [pastFun_revProc_neg, h]
    rw [Measure.map_congr this]; exact hlaw _

/-- Time reversal (b): almost surely
`{X(s) : s ∈ [0,T]} = {X(T) - X̂(u) : u ∈ [0,T]}`. -/
theorem ae_range_revPath_canonical (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    {T : ℝ≥0} (hT : 0 < T) :
    ∀ᵐ ω ∂P, canonical d N ω '' Icc 0 T =
      (fun u => canonical d N ω T - revPath T (canonical d N ω) u) '' Icc 0 T := by
  filter_upwards [ae_walk_leftConst hN (t := (T : ℝ)) (by exact_mod_cast hT)] with ω h
  refine range_revPath_can (N ω) ?_
  obtain ⟨δ, hδ, hc⟩ := h
  have hTδ : 0 < min δ (T : ℝ) := lt_min hδ (by exact_mod_cast hT)
  refine leftLim_eq_of_const (a := (T - (min δ (T : ℝ)).toNNReal)) ?_ ?_
  · exact tsub_lt_self hT (Real.toNNReal_pos.2 hTδ)
  · intro s hs1 hs2
    have hδ'T : (min δ (T : ℝ)).toNNReal ≤ T := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hTδ.le]; exact min_le_right _ _
    have hcoe : ((T - (min δ (T : ℝ)).toNNReal : ℝ≥0) : ℝ) = (T : ℝ) - min δ T := by
      rw [NNReal.coe_sub hδ'T, Real.coe_toNNReal _ hTδ.le]
    have h1 := NNReal.coe_le_coe.2 hs1
    rw [hcoe] at h1
    exact hc s ⟨by linarith [min_le_left δ (T : ℝ)], by exact_mod_cast hs2⟩

end SRW
end ElboimSly
