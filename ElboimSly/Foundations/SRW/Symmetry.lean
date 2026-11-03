/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.AdmissibleSRW
public import ElboimSly.Foundations.PPP.Invariance
public import Mathlib

/-!
# Hyperoctahedral symmetry

Hyperoctahedral symmetry.

A signed permutation is encoded by a bijection `σ` of the directions together with an additive map
`g` of `ℤ^d` with `g (v.vec) = (σ v).vec`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (Dir d × ℝ)}

theorem clock_perm (σ : Dir d ≃ Dir d) :
    (clockIntensity (Dir d)).map (Prod.map σ id) = clockIntensity (Dir d) := by
  unfold clockIntensity
  exact count_prod_map_invariant _ σ measurable_id Measure.map_id

theorem perm_ppp (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (σ : Dir d ≃ Dir d) :
    IsPoissonPointProcess (fun ω => (N ω).map (Prod.map σ id)) (clockIntensity (Dir d)) P := by
  have h := hN.map_measure ((measurable_of_countable σ).prodMap (measurable_id : Measurable (id : ℝ → ℝ)))
  rwa [clock_perm σ] at h

theorem cnt_perm (σ : Dir d ≃ Dir d) (ν : Measure (Dir d × ℝ)) (w : Dir d) (t : ℝ) :
    cnt (ν.map (Prod.map σ id)) w t = cnt ν (σ.symm w) t := by
  unfold cnt
  rw [Measure.map_apply ((measurable_of_countable σ).prodMap measurable_id)
    (measurableSet_rect w _ measurableSet_Ioc)]
  congr 1
  ext ⟨v, x⟩
  simp only [mem_preimage, Prod.map_apply, id_eq, mem_prod, mem_singleton_iff, mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by rw [← h1]; simp, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by rw [h1]; simp, h2⟩

theorem walk_perm_ae (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (σ : Dir d ≃ Dir d)
    (g : (Fin d → ℤ) →+ (Fin d → ℤ)) (hg : ∀ v : Dir d, g v.vec = (σ v).vec) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, walk d ((N ω).map (Prod.map σ id)) s = g (walk d (N ω) s) := by
  filter_upwards [ae_good hN, ae_good (perm_ppp hN σ)] with ω h1 h2 s
  rw [walk_of_good h1, walk_of_good h2, map_sum]
  simp only [cnt_perm, map_zsmul, hg]
  exact Fintype.sum_equiv σ.symm _ _ (fun w => by simp)

/-- Hyperoctahedral symmetry: the image of an SRW under a signed permutation is an SRW. -/
theorem IsSRW.map_signedPerm {Z : Ω → PathSpace d} (hZ : IsSRW P Z) (σ : Dir d ≃ Dir d)
    (g : (Fin d → ℤ) →+ (Fin d → ℤ)) (hg : ∀ v : Dir d, g v.vec = (σ v).vec) :
    IsSRW P (fun ω s => g (Z ω s)) := by
  obtain ⟨hm, hreg, Ω', mΩ', P', N', hN', hlaw⟩ := hZ
  have hgm : Measurable (fun γ : PathSpace d => fun s => g (γ s)) :=
    measurable_pi_iff.2 fun s => (measurable_of_countable g).comp (measurable_pi_apply s)
  refine ⟨hgm.comp hm, fun ω t => ?_, Ω', mΩ', P', fun ω => (N' ω).map (Prod.map σ id),
    perm_ppp hN' σ, ?_⟩
  · obtain ⟨δ, hδ, h⟩ := hreg ω t
    exact ⟨δ, hδ, fun s hs1 hs2 => by simp only [h s hs1 hs2]⟩
  · have h1 : P.map (fun ω s => g (Z ω s)) = (P.map Z).map (fun γ s => g (γ s)) :=
      (Measure.map_map hgm hm).symm
    rw [h1, hlaw, Measure.map_map hgm (measurable_canonical hN'.measurable)]
    refine Measure.map_congr ?_
    filter_upwards [walk_perm_ae hN' σ g hg] with ω hω
    funext s
    exact (hω s).symm

end SRW
end ElboimSly
