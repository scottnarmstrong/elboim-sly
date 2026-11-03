/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Iid
public import ElboimSly.Foundations.SRW.FixedLaw
public import Mathlib

/-!
# Coordinates of the walk

Coordinates.

The `i`-th coordinate process of the canonical `d`-dimensional walk is a one-dimensional SRW, built
from the sub-process `N^{(i)}` of the points moving in direction `±e_i`, and the coordinates are
independent processes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (Dir d × ℝ)}

/-- The direction set of the `i`-th axis. -/
def axisSet (d : ℕ) (i : Fin d) : Set (Dir d) := {v | v.1 = i}

/-- Collapse the `i`-th axis to the unique axis of dimension one. -/
def axisMap (d : ℕ) : Dir d → Dir 1 := fun v => (0, v.2)

theorem measurableSet_axisSet (i : Fin d) : MeasurableSet (axisSet d i) :=
  (Set.to_countable _).measurableSet

/-- The sub-process `N^{(i)}`. -/
noncomputable def axisProcess (i : Fin d) (ν : Measure (Dir d × ℝ)) : Measure (Dir 1 × ℝ) :=
  relabel (axisSet d i) (axisMap d) ν

theorem axisProcess_ppp (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (i : Fin d) :
    IsPoissonPointProcess (fun ω => axisProcess i (N ω)) (clockIntensity (Dir 1)) P := by
  refine relabel_ppp hN (measurableSet_axisSet i) ?_ ?_
  · intro a ha b hb hab
    have h2 : a.2 = b.2 := (Prod.mk.inj hab).2
    exact Prod.ext (ha.trans hb.symm) h2
  · intro v; exact ⟨(i, v.2), rfl, Prod.ext (Subsingleton.elim _ _) rfl⟩

theorem cnt_axisProcess (i : Fin d) (ν : Measure (Dir d × ℝ)) (b : Bool) (s : ℝ) :
    cnt (axisProcess i ν) ((0 : Fin 1), b) s = cnt ν (i, b) s := by
  unfold cnt axisProcess relabel
  have hm : Measurable (Prod.map (axisMap d) (id : ℝ → ℝ)) :=
    (measurable_of_countable _).prodMap measurable_id
  rw [Measure.map_apply hm (measurableSet_rect _ _ measurableSet_Ioc),
    Measure.restrict_apply (hm (measurableSet_rect _ _ measurableSet_Ioc))]
  congr 1
  ext ⟨v, x⟩
  simp only [mem_inter_iff, mem_preimage, Prod.map_apply, id_eq, mem_prod, mem_singleton_iff,
    mem_Ioc, axisSet, axisMap, mem_ofPred_eq, mem_univ, and_true]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have : v = (i, b) := Prod.ext h3 (Prod.mk.inj h1).2
    exact ⟨this, h2⟩
  · rintro ⟨h1, h2⟩
    subst h1
    exact ⟨⟨Prod.ext (Subsingleton.elim _ _) rfl, h2⟩, rfl⟩

theorem walk_axisProcess_ae (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (i : Fin d) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, (fun _ : Fin 1 => walk d (N ω) s i) = walk 1 (axisProcess i (N ω)) s := by
  filter_upwards [ae_good hN, ae_good (axisProcess_ppp hN i)] with ω h1 h2 s
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  rw [walk_apply h1, walk_apply h2, cnt_axisProcess, cnt_axisProcess]

/-- Coordinates: each coordinate of the canonical walk is a one-dimensional SRW. -/
theorem isSRW_coordinate (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (i : Fin d) :
    IsSRW P (fun ω s => fun _ : Fin 1 => walk d (N ω) (s : ℝ) i) := by
  have hmeas : Measurable fun ω => fun (s : ℝ≥0) (_ : Fin 1) => walk d (N ω) (s : ℝ) i := by
    refine measurable_pi_iff.2 fun s => measurable_pi_iff.2 fun j => ?_
    exact ((measurable_pi_apply i).comp ((measurable_walk d s).comp hN.measurable))
  refine ⟨hmeas, fun ω t => ?_, Ω, inferInstance, P, fun ω => axisProcess i (N ω),
    axisProcess_ppp hN i, ?_⟩
  · obtain ⟨δ, hδ, h⟩ := isRegularPath_canonical N ω t
    exact ⟨δ, hδ, fun s hs1 hs2 => by
      funext j
      have := congrFun (h s hs1 hs2) i
      simpa [canonical] using this⟩
  · refine Measure.map_congr ?_
    filter_upwards [walk_axisProcess_ae hN i] with ω hω
    funext s
    exact hω s

/-- The signed count `N_{(i,+)}(t) - N_{(i,-)}(t)` as a function of the restriction of `ν` to the
`i`-th axis. -/
noncomputable def axisFun (d : ℕ) (i : Fin d) (ρ : Measure (Dir d × ℝ)) : ℝ≥0 → ℤ := fun s =>
  (natOf (ρ (({(i, true)} : Set (Dir d)) ×ˢ Ioc 0 (s : ℝ))) : ℤ) -
    natOf (ρ (({(i, false)} : Set (Dir d)) ×ˢ Ioc 0 (s : ℝ)))

theorem measurable_axisFun (i : Fin d) : Measurable (axisFun d i) := by
  refine measurable_pi_iff.2 fun s => ?_
  have h1 : ∀ b : Bool, Measurable fun ρ : Measure (Dir d × ℝ) =>
      natOf (ρ (({(i, b)} : Set (Dir d)) ×ˢ Ioc 0 (s : ℝ))) := fun b =>
    measurable_natOf.comp (Measure.measurable_coe (measurableSet_rect _ _ measurableSet_Ioc))
  exact (measurable_from_top.comp (h1 true)).sub (measurable_from_top.comp (h1 false))

/-- Coordinates: the coordinate processes of the canonical walk are independent. -/
theorem iIndepFun_coordinates (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) :
    iIndepFun (fun (i : Fin d) ω => fun s : ℝ≥0 => walk d (N ω) (s : ℝ) i) P := by
  have hS : ∀ i : Fin d, MeasurableSet (axisSet d i ×ˢ (univ : Set ℝ)) := fun i =>
    (measurableSet_axisSet i).prod MeasurableSet.univ
  have hdis : Pairwise (Function.onFun Disjoint fun i : Fin d => axisSet d i ×ˢ (univ : Set ℝ)) := by
    intro a b hab
    refine Set.disjoint_left.2 fun p hp hq => hab ?_
    simp only [axisSet, mem_prod, mem_ofPred_eq, mem_univ, and_true] at hp hq
    rw [← hp, hq]
  have hi := (hN.iIndepFun_restrict hS hdis).comp (fun i ρ => axisFun d i ρ)
    (fun i => measurable_axisFun i)
  refine (iIndepFun_congr ?_).2 hi
  intro i
  filter_upwards [ae_good hN] with ω hω
  funext s
  change walk d (N ω) (s : ℝ) i = axisFun d i ((N ω).restrict (axisSet d i ×ˢ univ)) s
  unfold axisFun
  rw [walk_apply hω]
  have key : ∀ b : Bool, (N ω).restrict (axisSet d i ×ˢ univ)
      (({(i, b)} : Set (Dir d)) ×ˢ Ioc 0 (s : ℝ)) = cnt (N ω) (i, b) s := by
    intro b
    rw [Measure.restrict_apply (measurableSet_rect _ _ measurableSet_Ioc)]
    unfold cnt
    congr 1
    refine inter_eq_left.2 ?_
    intro p hp
    simp only [mem_prod, mem_singleton_iff, axisSet, mem_ofPred_eq, mem_univ, and_true] at hp ⊢
    rw [hp.1]
  rw [key true, key false]

end SRW
end ElboimSly
