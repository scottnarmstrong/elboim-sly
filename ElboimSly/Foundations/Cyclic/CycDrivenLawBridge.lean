/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenLawMeas
public import ElboimSly.Foundations.Cyclic.CycSchemeDrvDef
public import ElboimSly.Foundations.SRW.Iid
public import ElboimSly.Foundations.Interchange.GoodAs
public import ElboimSly.Foundations.PPP.Operations
public import Mathlib

/-!
# One copy as a single-index family

Driven and environment walks agree in law. The multi-exploration theorem is stated for an environment on
`J × S_β` and a driver on `(𝒟 × J) × ℝ`; for the single walk of `𝒫₁` the index sets are `Unit`.

* an environment `ν` on `S_β` becomes `ν.map (Prod.mk )` on `Unit × S_β`
  (`isPPP_envUnit`, `cycSlice_map_unit`);
* a driver `N₀` on `𝒟 × ℝ` becomes `relabel univ (v ↦ (v, )) N₀` on `(𝒟 × Unit) × ℝ`
  (`isPPP_drvUnit`, `relabel_sub_unit`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
theorem cycSlice_map_unit (ν : Measure (RingSpace d β)) :
    cycSlice () (ν.map (Prod.mk ())) = ν := by
  ext A hA
  unfold cycSlice
  rw [(measurableEmbedding_prodMk_left ()).comap_apply,
    Measure.map_apply measurable_prodMk_left
      ((measurableEmbedding_prodMk_left ()).measurableSet_image.2 hA)]
  congr 1
  exact Set.preimage_image_eq _ (fun a b h => (Prod.mk.inj h).2)

omit [Fact (0 < β)] in
theorem cycGood_map_unit {ν : Measure (RingSpace d β)} (h : Good ν) :
    CycGood (ν.map (Prod.mk ())) := fun ι => by
  rw [show ι = () from Subsingleton.elim _ _, cycSlice_map_unit]
  exact h

theorem cycIntensity_unit :
    cycIntensity Unit d β = (ringIntensity d β).map (Prod.mk ()) := by
  unfold cycIntensity
  rw [Unique.count_eq_dirac, Measure.dirac_prod]

theorem isPPP_envUnit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ν : Ω → Measure (RingSpace d β)}
    (hν : IsPoissonPointProcess ν (ringIntensity d β) P) :
    IsPoissonPointProcess (fun ω => (ν ω).map (Prod.mk ())) (cycIntensity Unit d β) P := by
  rw [cycIntensity_unit]
  exact hν.map_measure measurable_prodMk_left

/-- The embedding of a driver on `𝒟 × ℝ` as a driver on `(𝒟 × Unit) × ℝ`. -/
noncomputable def drvUnit (N₀ : Measure (Dir d × ℝ)) : Measure ((Dir d × Unit) × ℝ) :=
  relabel univ (fun v : Dir d => (v, ())) N₀

theorem relabel_sub_unit (N₀ : Measure (Dir d × ℝ)) :
    relabel {x : Dir d × Unit | x.2 = ()} Prod.fst (drvUnit N₀) = N₀ := by
  have hS : {x : Dir d × Unit | x.2 = ()} = univ := Set.eq_univ_of_forall fun x => by simp
  unfold relabel drvUnit relabel
  rw [hS]
  simp only [univ_prod_univ, Measure.restrict_univ]
  rw [Measure.map_map ((measurable_of_countable Prod.fst).prodMap measurable_id)
    ((measurable_of_countable _).prodMap measurable_id)]
  have : (Prod.map (Prod.fst : Dir d × Unit → Dir d) (id : ℝ → ℝ)) ∘
      Prod.map (fun v : Dir d => (v, ())) (id : ℝ → ℝ) = id := rfl
  rw [this, Measure.map_id]

theorem isPPP_drvUnit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N₀ : Ω → Measure (Dir d × ℝ)} (h : IsPoissonPointProcess N₀ (clockIntensity (Dir d)) P) :
    IsPoissonPointProcess (fun ω => drvUnit (N₀ ω)) (drvIntensity d Unit) P :=
  relabel_ppp h MeasurableSet.univ (fun _a _ _b _ hab => (Prod.mk.inj hab).1)
    (fun b => ⟨b.1, mem_univ _, Prod.ext rfl (Subsingleton.elim _ _)⟩)

theorem srwPath_drvUnit_fn (N₀ : Measure (Dir d × ℝ)) (s : ℝ≥0) :
    (srwPath (drvUnit N₀) ()).1.fn s = walk d N₀ (s : ℝ) := by
  rw [srwPath_fn, relabel_sub_unit]

end ElboimSly.Cyclic

end
