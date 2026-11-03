/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.FwdBridge
public import ElboimSly.Foundations.Cyclic.GoodMeas
import Mathlib

/-!
# Measurability of the forward trajectory

Measurability (the stronger statement of the proof: `(ν, a, s) ↦ γ^ν_{x,a}(s)`
is measurable on `Good`).
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The good configurations, with the trace σ-algebra. -/
abbrev GoodSet (d : ℕ) (β : ℝ) [Fact (0 < β)] : Type := {ν : Measure (RingSpace d β) // Good ν}

theorem measurable_niceOfGood : Measurable (fun ν : GoodSet d β => (⟨ν.1, good_nice ν.2⟩ : NiceSet d β)) :=
  Measurable.subtype_mk measurable_subtype_coe

theorem measurable_stepT (z : Fin d → ℤ) :
    Measurable (fun p : GoodSet d β × ℝ => stepT p.1.1 z p.2) :=
  (measurable_nxtJ (Ez_finite z)).comp ((measurable_niceOfGood.comp measurable_fst).prodMk measurable_snd)

theorem measurable_stepW (z : Fin d → ℤ) :
    Measurable (fun p : GoodSet d β × ℝ => stepW p.1.1 z p.2) := by
  refine measurable_to_countable' fun y => ?_
  let Q : Edge d → Set (GoodSet d β × ℝ) := fun e =>
    {p | p.1.1 ∈ hasRingSet {e}} ∩ {p | nxtJ p.1.1 {e} p.2 = nxtJ p.1.1 (Ez d z) p.2}
  have hH : MeasurableSet {p : GoodSet d β × ℝ | p.1.1 ∈ hasRingSet (Ez d z)} :=
    (measurable_subtype_coe.comp measurable_fst) (measurableSet_hasRingSet _)
  have hQ : ∀ e, MeasurableSet (Q e) := fun e =>
    ((measurable_subtype_coe.comp measurable_fst) (measurableSet_hasRingSet _)).inter
      (measurableSet_eq_fun ((measurable_nxtJ (Set.finite_singleton e)).comp
        ((measurable_niceOfGood.comp measurable_fst).prodMk measurable_snd)) (measurable_stepT z))
  have hStep : MeasurableSet (⋃ e : Edge d, ({_p : GoodSet d β × ℝ | e ∈ Ez d z ∧ e.1 = s(z, y)} ∩ Q e)) :=
    MeasurableSet.iUnion fun e => (MeasurableSet.const _).inter (hQ e)
  have : (fun p : GoodSet d β × ℝ => stepW p.1.1 z p.2) ⁻¹' {y} =
      ({p | p.1.1 ∈ hasRingSet (Ez d z)} ∩ (⋃ e : Edge d,
        ({_p : GoodSet d β × ℝ | e ∈ Ez d z ∧ e.1 = s(z, y)} ∩ Q e))) ∪
      ({p | p.1.1 ∈ hasRingSet (Ez d z)}ᶜ ∩ {_p | y = z}) := by
    ext ⟨⟨ν, hν⟩, t⟩
    have hn : Nice ν := good_nice hν
    have hQe : ∀ e, e ∈ Ez d z → (((⟨ν, hν⟩, t) : GoodSet d β × ℝ) ∈ Q e ↔
        HasRing ν {e} ∧ nxt ν {e} t = nxt ν (Ez d z) t) := by
      intro e he
      simp only [Q, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rw [mem_hasRingSet_iff hn]
      constructor
      · rintro ⟨hRe, h⟩
        have hR : HasRing ν (Ez d z) := by
          obtain ⟨u, e', he', hr⟩ := hRe
          rw [Set.mem_singleton_iff] at he'; subst he'
          exact ⟨u, e', he, hr⟩
        rw [nxtJ_of_hasRing t hR, nxtJ_of_hasRing t hRe] at h
        exact ⟨hRe, h⟩
      · rintro ⟨hRe, h⟩
        have hR : HasRing ν (Ez d z) := by
          obtain ⟨u, e', he', hr⟩ := hRe
          rw [Set.mem_singleton_iff] at he'; subst he'
          exact ⟨u, e', he, hr⟩
        rw [nxtJ_of_hasRing t hR, nxtJ_of_hasRing t hRe]
        exact ⟨hRe, h⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion]
    rw [mem_hasRingSet_iff hn]
    by_cases hR : HasRing ν (Ez d z)
    · rw [stepW_eq_iff hν z t hR]
      simp only [hR, true_and, not_true_eq_false, false_and, or_false, StepP]
      constructor
      · rintro ⟨e, he, hs, h⟩
        exact ⟨e, ⟨he, hs⟩, (hQe e he).mpr h⟩
      · rintro ⟨e, ⟨he, hs⟩, h⟩
        exact ⟨e, he, hs, (hQe e he).mp h⟩
    · rw [stepW_of_not z t hR]
      simp [hR, eq_comm]
  rw [this]
  exact (hH.inter hStep).union ((hH.compl).inter (MeasurableSet.const _))

theorem measurable_fseq (x : Fin d → ℤ) (k : ℕ) :
    Measurable (fun p : GoodSet d β × ℝ => fseq p.1.1 x p.2 k) := by
  have hG : Measurable (fun s : (GoodSet d β × ℝ) × (Fin d → ℤ) =>
      ((stepT s.1.1.1 s.2 s.1.2, stepW s.1.1.1 s.2 s.1.2) : ℝ × (Fin d → ℤ))) :=
    measurable_from_prod_countable_left fun z => (measurable_stepT z).prodMk (measurable_stepW z)
  induction k with
  | zero => exact measurable_snd.prodMk measurable_const
  | succ k ih =>
    exact hG.comp ((measurable_fst.prodMk ih.fst).prodMk ih.snd)

end ElboimSly.Cyclic

end
