/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycLines
public import Mathlib

/-!
# Measurability of the stopping length

Measurability of record functionals (c): for a plan `𝒫` and `k ≤ K`, the stopping length is a measurable
function of `(ρ, p) ∈ CycRec_{k-1} × CycPath`.

Also the building blocks: measurability of `(p, ℓ) ↦ p(· ∧ ℓ)` and of `snoc`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ}

theorem measurable_cpath_cut {V : Type*} [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] :
    Measurable (fun q : CPath V × ℝ≥0∞ => q.1.cut q.2) := by
  rw [CPath.measurable_iff]
  refine ⟨by simpa using measurable_snd, fun s => ?_⟩
  simp only [CPath.cut_fn]
  have hg : Measurable fun q : CPath V × ℝ≥0∞ => (min (s : ℝ≥0∞) q.2).toNNReal :=
    (measurable_const.min measurable_snd).ennreal_toNNReal
  exact measurable_fn_at (fun q : CPath V × ℝ≥0∞ => q.1) measurable_fst _ hg

theorem measurable_cycPath_cut :
    Measurable (fun q : CycPath d × ℝ≥0∞ => q.1.cut q.2) := by
  refine Measurable.subtype_mk ?_
  exact measurable_cpath_cut.comp ((measurable_subtype_coe.comp measurable_fst).prodMk
    measurable_snd)

theorem measurable_snoc {k : ℕ} :
    Measurable (fun q : CycRecN I d k × CycEntry I d => CycRec.snoc q.1 q.2) := by
  refine measurable_pi_iff.mpr fun i => ?_
  induction i using Fin.lastCases with
  | last =>
    simp only [CycRec.snoc, Fin.snoc_last]
    exact measurable_snd
  | cast j =>
    simp only [CycRec.snoc, Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst

namespace CycPlan

variable (P : CycPlan I d β)

theorem measurable_hatRec (k : ℕ) (a : ℕ) :
    Measurable (fun q : CycRecN I d k × CycPath d => P.hatRec k q.1 q.2 a) := by
  unfold CycPlan.hatRec
  refine measurable_snoc.comp (measurable_fst.prodMk ?_)
  refine ((P.measurable_start k).comp measurable_fst).prodMk ?_
  refine measurable_cycPath_cut.comp (measurable_snd.prodMk ?_)
  exact (CPath.measurable_jt a).comp (measurable_subtype_coe.comp measurable_snd)

/-- Measurability of record functionals (c). The stopping length is measurable in `(ρ, p)`. -/
theorem measurable_stopLen (k : ℕ) :
    Measurable (fun q : CycRecN I d k × CycPath d => P.stopLen k q.1 q.2) := by
  have hjt : ∀ a, Measurable fun q : CycRecN I d k × CycPath d => q.2.1.jt a := fun a =>
    (CPath.measurable_jt a).comp (measurable_subtype_coe.comp measurable_snd)
  have hst : ∀ a, MeasurableSet {q : CycRecN I d k × CycPath d | P.st k (P.hatRec k q.1 q.2 a) = true} :=
    fun a => (P.measurable_st k).comp (P.measurable_hatRec k a) (measurableSet_singleton true)
  have hdl : ∀ a, Measurable fun q : CycRecN I d k × CycPath d => P.dl k (P.hatRec k q.1 q.2 a) :=
    fun a => (P.measurable_dl k).comp (P.measurable_hatRec k a)
  let f1 : ℕ → CycRecN I d k × CycPath d → ℝ≥0∞ := fun a q =>
    open scoped Classical in
    if 1 ≤ a ∧ q.2.1.jt a < ⊤ ∧ P.st k (P.hatRec k q.1 q.2 a) = true then q.2.1.jt a else ⊤
  let f2 : ℕ → CycRecN I d k × CycPath d → ℝ≥0∞ := fun a q =>
    open scoped Classical in
    if q.2.1.jt a < ⊤ ∧ q.2.1.jt a + P.dl k (P.hatRec k q.1 q.2 a) < q.2.1.jt (a + 1)
    then q.2.1.jt a + P.dl k (P.hatRec k q.1 q.2 a) else ⊤
  have heq : (fun q : CycRecN I d k × CycPath d => P.stopLen k q.1 q.2) =
      fun q => ⨅ a, (f1 a q ⊓ f2 a q) := by
    funext q
    unfold CycPlan.stopLen
    apply le_antisymm
    · refine le_iInf fun a => le_inf ?_ ?_
      · by_cases h : 1 ≤ a ∧ q.2.1.jt a < ⊤ ∧ P.st k (P.hatRec k q.1 q.2 a) = true
        · simp only [f1, ite_eq_left h]
          exact sInf_le (Or.inl ⟨a, h.1, h.2.1, h.2.2, rfl⟩)
        · simp only [f1, ite_eq_right h]; exact le_top
      · by_cases h : q.2.1.jt a < ⊤ ∧ q.2.1.jt a + P.dl k (P.hatRec k q.1 q.2 a) < q.2.1.jt (a + 1)
        · simp only [f2, ite_eq_left h]
          exact sInf_le (Or.inr ⟨a, h.1, rfl, h.2⟩)
        · simp only [f2, ite_eq_right h]; exact le_top
    · refine le_sInf ?_
      rintro t (⟨a, ha, hj, hs, rfl⟩ | ⟨a, hj, rfl, hlt⟩)
      · exact (iInf_le _ a).trans (inf_le_left.trans (by simp only [f1, ite_eq_left (And.intro ha (And.intro hj hs))]; exact le_rfl))
      · exact (iInf_le _ a).trans (inf_le_right.trans (by simp only [f2, ite_eq_left (And.intro hj hlt)]; exact le_rfl))
  rw [heq]
  refine Measurable.iInf fun a => Measurable.inf ?_ ?_
  · refine Measurable.ite ?_ (hjt a) measurable_const
    exact (MeasurableSet.const (1 ≤ a)).inter
      ((measurableSet_lt (hjt a) measurable_const).inter (hst a))
  · refine Measurable.ite ?_ ((hjt a).add (hdl a)) measurable_const
    exact (measurableSet_lt (hjt a) measurable_const).inter
      (measurableSet_lt ((hjt a).add (hdl a)) (hjt (a + 1)))

end CycPlan

end ElboimSly.Cyclic

end
