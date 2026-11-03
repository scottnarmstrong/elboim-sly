/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Relabel
public import ElboimSly.Foundations.SRW.Jumps
public import ElboimSly.Foundations.PPP.Indep
public import Mathlib

/-!
# The canonical walk is an SRW; independent families of walks

Path space, laws, SRWs, admissible filtrations (c), independent families.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ}

theorem isRegularPath_canonical {Ω : Type*} (N : Ω → Measure (Dir d × ℝ)) (ω : Ω) :
    IsRegularPath (canonical d N ω) := by
  intro t
  obtain ⟨δ, hδ, h⟩ := exists_const_right (ν := N ω) (t : ℝ) t.2
  refine ⟨δ.toNNReal, Real.toNNReal_pos.2 hδ, fun s hs1 hs2 => ?_⟩
  exact h s ⟨by exact_mod_cast hs1, by
    have h1 : ((s : ℝ≥0) : ℝ) < ((t + δ.toNNReal : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.2 hs2
    rw [NNReal.coe_add, Real.coe_toNNReal _ hδ.le] at h1
    exact h1⟩

/-- The canonical walk built from a Poisson point process is an SRW (Path space, laws, SRWs, admissible filtrations (c)). -/
theorem canonical_isSRW {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (Dir d × ℝ)} (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) :
    IsSRW P (canonical d N) :=
  ⟨measurable_canonical hN.measurable, isRegularPath_canonical N, Ω, inferInstance, P, N, hN, rfl⟩

section Iid

variable {ι : Type} [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
  {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {Ñ : Ω → Measure ((Dir d × ι) × ℝ)}

/-- The `ι`-th sub-process `N^ι(A) = Ñ({((v,ι),s) : (v,s) ∈ A})`. -/
noncomputable def subProcess (Ñ : Ω → Measure ((Dir d × ι) × ℝ)) (j : ι) (ω : Ω) :
    Measure (Dir d × ℝ) :=
  relabel {x : Dir d × ι | x.2 = j} Prod.fst (Ñ ω)

theorem subProcess_ppp (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × ι)) P) (j : ι) :
    IsPoissonPointProcess (subProcess Ñ j) (clockIntensity (Dir d)) P := by
  refine relabel_ppp h (S := {x : Dir d × ι | x.2 = j}) (measurableSet_eq_fun measurable_snd
    measurable_const) ?_ ?_
  · intro a ha b hb hab
    exact Prod.ext hab (ha.trans hb.symm)
  · intro v; exact ⟨(v, j), rfl, rfl⟩

/-- Independent families: the sub-processes are independent. -/
theorem iIndepFun_subProcess (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × ι)) P) :
    iIndepFun (fun j => subProcess Ñ j) P := by
  have hS : ∀ j : ι, MeasurableSet ({x : Dir d × ι | x.2 = j} ×ˢ (univ : Set ℝ)) := fun j =>
    (measurableSet_eq_fun measurable_snd measurable_const).prod MeasurableSet.univ
  have hdis : Pairwise (Function.onFun Disjoint fun j : ι =>
      ({x : Dir d × ι | x.2 = j} ×ˢ (univ : Set ℝ))) := by
    intro a b hab
    refine Set.disjoint_left.2 fun p hp hq => hab ?_
    simp only [mem_prod, mem_ofPred_eq, mem_univ, and_true] at hp hq
    rw [← hp, hq]
  have hi := h.iIndepFun_restrict hS hdis
  have := hi.comp (fun j ν => (ν.map (Prod.map Prod.fst id) : Measure (Dir d × ℝ)))
    (fun j => measurable_map_measure ((measurable_fst).prodMap measurable_id))
  exact this

/-- The canonical walks `X^ι` are independent processes. -/
theorem iIndepFun_canonical_subProcess (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × ι)) P) :
    iIndepFun (fun j => canonical d (subProcess Ñ j)) P := by
  have hG : Measurable fun ν : Measure (Dir d × ℝ) => fun s : ℝ≥0 => walk d ν (s : ℝ) :=
    measurable_pi_iff.2 fun s => measurable_walk d s
  exact (iIndepFun_subProcess h).comp (fun _ => (fun (ν : Measure (Dir d × ℝ)) (s : ℝ≥0) => walk d ν (s : ℝ))) (fun _ => hG)

/-- Independent families: each `X^ι` is an SRW. -/
theorem isSRW_subProcess (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × ι)) P) (j : ι) :
    IsSRW P (canonical d (subProcess Ñ j)) :=
  canonical_isSRW (subProcess_ppp h j)

end Iid

end SRW
end ElboimSly
