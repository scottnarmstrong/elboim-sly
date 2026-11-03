/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.ShiftWalk
public import Mathlib

/-!
# Independence of past and future for the canonical walk

Independent stationary increments; Markov property at fixed times (a), (b) with trivial `𝒢₀`; count calculus (c), (e).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {N : Ω → Measure (Dir d × ℝ)} {P : Measure Ω}

/-- The path stopped at time `a`. -/
def stopPath (a : ℝ≥0) (γ : PathSpace d) : PathSpace d := fun s => γ (min s a)

theorem measurable_stopPath (a : ℝ≥0) : Measurable (stopPath (d := d) a) :=
  measurable_pi_iff.2 fun s => measurable_pi_apply (min s a)

/-- A function of the restriction of `ν` to `D × (0,a]` only, equal to the stopped walk. -/
noncomputable def pastFun (d : ℕ) (a : ℝ≥0) (ρ : Measure (Dir d × ℝ)) : PathSpace d :=
  fun s => ∑ v : Dir d, ((natOf (ρ (({v} : Set (Dir d)) ×ˢ Ioc 0 ((min s a : ℝ≥0) : ℝ))) : ℕ) : ℤ)
    • v.vec

theorem measurable_pastFun (d : ℕ) (a : ℝ≥0) : Measurable (pastFun d a) := by
  refine measurable_pi_iff.2 fun s => ?_
  refine Finset.measurable_fun_sum _ fun v _ => ?_
  have h : Measurable fun ρ : Measure (Dir d × ℝ) =>
      natOf (ρ (({v} : Set (Dir d)) ×ˢ Ioc 0 ((min s a : ℝ≥0) : ℝ))) :=
    measurable_natOf.comp (Measure.measurable_coe (measurableSet_rect v _ measurableSet_Ioc))
  exact (Measurable.of_discrete (f := fun n : ℕ => ((n : ℤ) • v.vec))).comp h

theorem stopPath_canonical_ae (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    (a : ℝ≥0) : ∀ᵐ ω ∂P, stopPath a (canonical d N ω) =
      pastFun d a ((N ω).restrict (univ ×ˢ Ioc 0 (a : ℝ))) := by
  filter_upwards [ae_good hN] with ω hω
  funext s
  simp only [stopPath, canonical, pastFun]
  rw [walk_of_good hω]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 3
  unfold cnt
  rw [Measure.restrict_apply (measurableSet_rect v _ measurableSet_Ioc)]
  congr 1
  refine (inter_eq_left.2 ?_).symm
  intro p hp
  simp only [mem_prod, mem_singleton_iff, mem_Ioc, mem_univ, true_and] at hp ⊢
  exact ⟨hp.2.1, hp.2.2.trans (by exact_mod_cast min_le_right s a)⟩

theorem theta_canonical_eq (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (a : ℝ≥0) :
    ∀ᵐ ω ∂P, theta a (canonical d N ω) = canonical d
      (fun ω => ((N ω).restrict (univ ×ˢ Ioi (a : ℝ))).map (shiftMap d a)) ω :=
  theta_canonical_ae hN a

/-- Independent stationary increments; Markov property at fixed times (b) (trivial `𝒢₀`): the stopped walk and the shifted walk are
independent. -/
theorem indepFun_stop_theta (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (a : ℝ≥0) :
    IndepFun (fun ω => stopPath a (canonical d N ω)) (fun ω => theta a (canonical d N ω)) P := by
  have hR : MeasurableSet (univ ×ˢ Ioc 0 (a : ℝ) : Set (Dir d × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ioc
  have hB : MeasurableSet (univ ×ˢ Ioi (a : ℝ) : Set (Dir d × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ioi
  have hdis : Disjoint (univ ×ˢ Ioc 0 (a : ℝ) : Set (Dir d × ℝ)) (univ ×ˢ Ioi (a : ℝ)) := by
    refine Set.disjoint_left.2 fun p hp hq => ?_
    simp only [mem_prod, mem_Ioc, mem_Ioi, mem_univ, true_and] at hp hq
    linarith [hp.2, hq]
  have hI := hN.indepFun_restrict hR hB hdis
  have hH : Measurable fun ρ : Measure (Dir d × ℝ) => canonical d (fun _ : Unit => ρ.map (shiftMap d a)) () := by
    exact measurable_pi_iff.2 fun s => (measurable_walk d s).comp
      (measurable_map_measure (measurable_shiftMap d a))
  have h1 := hI.comp (measurable_pastFun d a) hH
  refine IndepFun.congr h1 ?_ ?_
  · exact (stopPath_canonical_ae hN a).mono fun ω h => h.symm
  · exact (theta_canonical_eq hN a).mono fun ω h => h.symm

end SRW
end ElboimSly
