/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Setting
public import Mathlib

/-!
# ES22 §4: events of right-continuous processes are determined by the law

Used by the "same holds for every process with the law of `W`" clauses of ES22 Claim 4.2,
ES22 Claim 4.3. A path `x : ℝ≥0 → ℤ^d` is right-continuous if it is locally constant to the right
(`IsRCPath`; `ℤ^d` is discrete). For such a path, `∃ s ∈ [a, b], P (x s)` holds iff it holds at a
point of the countable set `qSet a b` (the rationals of `[a, b]` and `b`). Hence the probability of
such an event for a process `X` with right-continuous paths depends only on the law of `X` on
`(ℝ≥0 → ℤ^d)` with the product `σ`-algebra.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- A `ℤ^d`-valued path on `ℝ≥0` is right-continuous (locally constant to the right). -/
def IsRCPath (x : ℝ≥0 → Fin d → ℤ) : Prop := ∀ t, ∀ᶠ s in 𝓝[≥] t, x s = x t

/-- The countable set of test times of `[a, b]`: its rationals together with `b`. -/
def qSet (a b : ℝ≥0) : Set ℝ≥0 := {q | a ≤ q ∧ q ≤ b ∧ ∃ r : ℚ, (q : ℝ) = r} ∪ {b}

theorem qSet_countable (a b : ℝ≥0) : (qSet a b).Countable := by
  refine Set.Countable.union ?_ (Set.countable_singleton b)
  refine (Set.countable_range (fun r : ℚ => Real.toNNReal r)).mono ?_
  rintro q ⟨-, -, r, hr⟩
  exact ⟨r, by rw [← NNReal.coe_inj, Real.coe_toNNReal _ (by rw [← hr]; exact q.2), hr]⟩

theorem mem_qSet_Icc {a b q : ℝ≥0} (hab : a ≤ b) (hq : q ∈ qSet a b) : a ≤ q ∧ q ≤ b := by
  rcases hq with ⟨h1, h2, -⟩ | rfl
  · exact ⟨h1, h2⟩
  · exact ⟨hab, le_rfl⟩

/-- A right-continuous path that satisfies `P` somewhere on `[a, b]` satisfies it at a test time. -/
theorem exists_qSet {x : ℝ≥0 → Fin d → ℤ} (hx : IsRCPath x) {a b s : ℝ≥0} (ha : a ≤ s)
    (hb : s ≤ b) : ∃ q ∈ qSet a b, x q = x s := by
  rcases hb.eq_or_lt with rfl | hlt
  · exact ⟨s, Or.inr rfl, rfl⟩
  · obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hx s)
    have hsu : (s : ℝ) < min (u : ℝ) b := lt_min (by exact_mod_cast hu) (by exact_mod_cast hlt)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hsu
    have hr0 : (0 : ℝ) ≤ r := le_trans s.2 hr1.le
    refine ⟨Real.toNNReal r, Or.inl ⟨?_, ?_, r, ?_⟩, ?_⟩
    · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]
      exact (by exact_mod_cast ha : (a : ℝ) ≤ s).trans hr1.le
    · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]
      exact hr2.le.trans (min_le_right _ _)
    · rw [Real.coe_toNNReal _ hr0]
    · have : Real.toNNReal r ∈ Ico s u := by
        refine ⟨?_, ?_⟩
        · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]; exact hr1.le
        · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]
          exact hr2.trans_le (min_le_left _ _)
      exact hsub this

/-- Equivalence of the full event and the countable one, for right-continuous paths. -/
theorem exists_Icc_iff_qSet {x : ℝ≥0 → Fin d → ℤ} (hx : IsRCPath x) {a b : ℝ≥0} (hab : a ≤ b)
    (P : (Fin d → ℤ) → Prop) :
    (∃ s, a ≤ s ∧ s ≤ b ∧ P (x s)) ↔ ∃ q ∈ qSet a b, P (x q) := by
  constructor
  · rintro ⟨s, h1, h2, h3⟩
    obtain ⟨q, hq, hqs⟩ := exists_qSet hx h1 h2
    exact ⟨q, hq, hqs ▸ h3⟩
  · rintro ⟨q, hq, h⟩
    exact ⟨q, (mem_qSet_Icc hab hq).1, (mem_qSet_Icc hab hq).2, h⟩

/-- The cylinder event `∃ q ∈ qSet a b, P (x q)` is measurable for the product `σ`-algebra. -/
theorem measurableSet_cyl (a b : ℝ≥0) (P : (Fin d → ℤ) → Prop) :
    MeasurableSet {x : ℝ≥0 → Fin d → ℤ | ∃ q ∈ qSet a b, P (x q)} := by
  have : {x : ℝ≥0 → Fin d → ℤ | ∃ q ∈ qSet a b, P (x q)} =
      ⋃ q ∈ qSet a b, (fun x : ℝ≥0 → Fin d → ℤ => x q) ⁻¹' {v | P v} := by
    ext x; simp
  rw [this]
  refine MeasurableSet.biUnion (qSet_countable a b) fun q _ => ?_
  exact (measurable_pi_apply q) (Set.to_countable _).measurableSet

/-- **Law transfer.** If `X` and `Y` have the same law on path space, the probability of a
countable-time event is the same for both. -/
theorem prob_cyl_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {Pr : Measure Ω}
    {Pr' : Measure Ω'} {X : Ω' → ℝ≥0 → Fin d → ℤ} {Y : Ω → ℝ≥0 → Fin d → ℤ}
    (hX : AEMeasurable X Pr') (hY : AEMeasurable Y Pr) (hlaw : Pr'.map X = Pr.map Y)
    (a b : ℝ≥0) (P : (Fin d → ℤ) → Prop) :
    Pr' {ω | ∃ q ∈ qSet a b, P (X ω q)} = Pr {ω | ∃ q ∈ qSet a b, P (Y ω q)} := by
  have hc := measurableSet_cyl (d := d) a b P
  have h1 := Measure.map_apply_of_aemeasurable hX hc
  have h2 := Measure.map_apply_of_aemeasurable hY hc
  rw [hlaw] at h1
  exact h1.symm.trans h2

end ElboimSly.Paper

end
