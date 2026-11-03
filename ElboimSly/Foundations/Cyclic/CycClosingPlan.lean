/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycPlan
public import ElboimSly.Foundations.Cyclic.CPathJump
public import Mathlib

/-!
# Plans with the closing rule

The driven walk is a driven world-line (the plan `𝒫₁` and the closing rule), the constructions of the regenerated walk
(the plan `𝒫_reg`).

For a world-line of length `ς` with path `p`, the closing rule is
`st := 1` iff `ς ∈ βℤ_{≥1}` and `p(ς) = 0`, and `dl := β⌈max(ς, β)/β⌉ - ς` if `ς < ∞` and
`p(ς) = 0`, `dl := ∞` otherwise. `closingPlan` is the plan with this rule for every walk.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ}

/-- The decision of the closing rule for a path: `ς ∈ βℤ_{≥1}` and `p(ς) = 0`. -/
noncomputable def closeSt (β : ℝ) (p : CycPath d) : Bool :=
  open scoped Classical in
  decide (∃ j : ℕ, 1 ≤ j ∧ p.1.len = ENNReal.ofReal (j * β) ∧ p.1.fn p.1.len.toNNReal = 0)

/-- The deadline of the closing rule for a path. -/
noncomputable def closeDl (β : ℝ) (p : CycPath d) : ℝ≥0∞ :=
  open scoped Classical in
  if p.1.len ≠ ⊤ ∧ p.1.fn p.1.len.toNNReal = 0 then
    ENNReal.ofReal (β * (⌈max p.1.len.toReal β / β⌉₊ : ℕ)) - p.1.len
  else ⊤

theorem measurable_closeSt (β : ℝ) : Measurable (closeSt (d := d) β) := by
  classical
  refine measurable_to_bool ?_
  have : closeSt (d := d) β ⁻¹' {true} = ⋃ j : ℕ, ⋃ (_ : 1 ≤ j),
      ({p : CycPath d | p.1.len = ENNReal.ofReal (j * β)} ∩
        {p : CycPath d | p.1.fn (ENNReal.ofReal (j * β)).toNNReal = 0}) := by
    ext p
    simp only [closeSt, mem_preimage, mem_singleton_iff, decide_eq_true_eq, mem_iUnion, mem_inter_iff,
      mem_ofPred_eq]
    constructor
    · rintro ⟨j, hj, h1, h2⟩
      exact ⟨j, hj, h1, h1 ▸ h2⟩
    · rintro ⟨j, hj, h1, h2⟩
      exact ⟨j, hj, h1, h1 ▸ h2⟩
  rw [this]
  refine MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => ?_
  refine MeasurableSet.inter ?_ ?_
  · exact (CPath.measurable_len.comp measurable_subtype_coe) (measurableSet_singleton _)
  · exact ((CPath.measurable_eval _).comp measurable_subtype_coe) (measurableSet_singleton _)

theorem measurable_closeDl (β : ℝ) : Measurable (closeDl (d := d) β) := by
  classical
  unfold closeDl
  have hlen : Measurable fun p : CycPath d => p.1.len :=
    CPath.measurable_len.comp measurable_subtype_coe
  have hev : Measurable fun p : CycPath d => p.1.fn p.1.len.toNNReal :=
    measurable_fn_at (fun p : CycPath d => p.1) measurable_subtype_coe _
      (ENNReal.measurable_toNNReal.comp hlen)
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (hlen (measurableSet_singleton _).compl).inter (hev (measurableSet_singleton _))
  · refine Measurable.sub ?_ hlen
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.const_mul ?_ _
    refine (measurable_from_top (f := fun n : ℕ => (n : ℝ))).comp ?_
    refine Nat.measurable_ceil.comp ?_
    refine Measurable.div_const ?_ _
    exact (ENNReal.measurable_toReal.comp hlen).max measurable_const

/-- The plan with `K` walks, start data `start`, and the closing rule for every walk. -/
noncomputable def closingPlan (β : ℝ) {I : Type*} [MeasurableSpace I] (K : ℕ∞)
    (start : ∀ k : ℕ, CycRecN I d k → CycData I d) (hs : ∀ k, Measurable (start k)) :
    CycPlan I d β where
  K := K
  start := start
  dl k ρ := closeDl β (ρ (Fin.last k)).2
  st k ρ := closeSt β (ρ (Fin.last k)).2
  measurable_start := hs
  measurable_dl k :=
    (measurable_closeDl β).comp (measurable_snd.comp (measurable_pi_apply (Fin.last k)))
  measurable_st k :=
    (measurable_closeSt β).comp (measurable_snd.comp (measurable_pi_apply (Fin.last k)))

end ElboimSly.Cyclic

end
