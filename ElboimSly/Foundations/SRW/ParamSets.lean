/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.ParamEvents
public import Mathlib

/-!
# Regular sets defined by variable times

Evaluation at variable times (b), (c), (d).

Here `E` is a measurable space, `α β : E → ℝ≥0` are measurable and `K ⊆ E × ℤ^d` is measurable,
with sections `K_z`.  We give explicit measurable versions of
* `{(z,γ) : γ(α z) ∈ K_z}` (`isVersion_eval`),
* `{(z,γ) : γ(s) ∈ K_z for all s ∈ [α z, β z]}` (`isVersion_forall_Icc`),
* `{(z,γ) : γ(s) ∈ K_z for some s ≥ α z}` (`isVersion_exists_Ici`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly
namespace SRW

variable {d : ℕ} {E : Type*} [MeasurableSpace E] {α β : E → ℝ≥0} {K : Set (E × (Fin d → ℤ))}

theorem measurable_pair_apply (q : ℝ≥0) :
    Measurable fun p : E × PathSpace d => (p.1, p.2 q) :=
  measurable_fst.prodMk ((measurable_pi_apply q).comp measurable_snd)

/-- Evaluation at variable times (b). -/
theorem isVersion_eval (hα : Measurable α) (hK : MeasurableSet K) :
    IsVersion {p : E × PathSpace d | (p.1, p.2 (α p.1)) ∈ K}
      {p | (p.1, ev (α p.1) p.2) ∈ K} := by
  refine ⟨?_, fun z γ hγ => ?_⟩
  · have : Measurable fun p : E × PathSpace d => (p.1, ev (α p.1) p.2) :=
      measurable_fst.prodMk (measurable_ev.comp ((hα.comp measurable_fst).prodMk measurable_snd))
    exact this hK
  · simp only [mem_ofPred_eq, ev_of_regular hγ]

/-- Evaluation at variable times (c). -/
theorem isVersion_forall_Icc (hα : Measurable α) (hβ : Measurable β) (hK : MeasurableSet K) :
    IsVersion {p : E × PathSpace d | ∀ s, α p.1 ≤ s → s ≤ β p.1 → (p.1, p.2 s) ∈ K}
      ({p | β p.1 < α p.1} ∪ ({p | (p.1, ev (β p.1) p.2) ∈ K} ∩
        ⋂ r : ℚ, ({p | ¬ (α p.1 ≤ ratNN r ∧ ratNN r < β p.1)} ∪
          {p | (p.1, p.2 (ratNN r)) ∈ K}))) := by
  refine ⟨?_, fun z γ hγ => ?_⟩
  · refine (measurableSet_lt (hβ.comp measurable_fst) (hα.comp measurable_fst)).union
      (MeasurableSet.inter ?_ (MeasurableSet.iInter fun r => ?_))
    · have : Measurable fun p : E × PathSpace d => (p.1, ev (β p.1) p.2) :=
        measurable_fst.prodMk
          (measurable_ev.comp ((hβ.comp measurable_fst).prodMk measurable_snd))
      exact this hK
    · refine MeasurableSet.union ?_ ((measurable_pair_apply (ratNN r)) hK)
      refine MeasurableSet.compl ?_
      exact (measurableSet_le (hα.comp measurable_fst)
        (measurable_const (a := ratNN r))).inter
        (measurableSet_lt (f := fun _ : E × PathSpace d => ratNN r) (g := fun p => β p.1)
          measurable_const (hβ.comp measurable_fst))
  · simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_iInter]
    by_cases hab : β z < α z
    · simp only [hab, true_or, iff_true]
      intro s h1 h2
      exact absurd (h1.trans h2) (not_le.2 hab)
    · have hab' : α z ≤ β z := not_lt.1 hab
      have key := hγ.forall_Icc_iff (fun _ y => (z, y) ∈ K)
        (fun y s _ => ⟨1, one_pos, fun s' _ _ => by simpa using ‹_›⟩) hab'
      simp only [hab, false_or]
      rw [key, ev_of_regular hγ]
      refine and_congr Iff.rfl (forall_congr' fun r => ?_)
      constructor
      · intro h
        by_cases hr : α z ≤ ratNN r ∧ ratNN r < β z
        · exact Or.inr (h hr.1 hr.2)
        · exact Or.inl hr
      · rintro (h | h) h1 h2
        · exact absurd ⟨h1, h2⟩ h
        · exact h

/-- Evaluation at variable times (d). -/
theorem isVersion_exists_Ici (hα : Measurable α) (hK : MeasurableSet K) :
    IsVersion {p : E × PathSpace d | ∃ s, α p.1 ≤ s ∧ (p.1, p.2 s) ∈ K}
      (⋃ r : ℚ, {p | α p.1 ≤ ratNN r ∧ (p.1, p.2 (ratNN r)) ∈ K}) := by
  refine ⟨MeasurableSet.iUnion fun r => ?_, fun z γ hγ => ?_⟩
  · exact (measurableSet_le (hα.comp measurable_fst) (measurable_const (a := ratNN r))).inter
      ((measurable_pair_apply (ratNN r)) hK)
  · have := hγ.exists_Ici_iff {y | (z, y) ∈ K} (α z)
    simp only [mem_ofPred_eq, mem_iUnion] at this ⊢
    exact this

end SRW
end ElboimSly
