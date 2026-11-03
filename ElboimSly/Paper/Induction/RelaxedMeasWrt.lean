/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IsHeavy
public import ElboimSly.Frozen.Defs.IndDelta
public import ElboimSly.Paper.Induction.RelaxedMeas
public import Mathlib

/-!
# Measurability of relaxed times: relaxed with respect to a path

Measurability of relaxed times (Steps 3, 4, 5), the abstract form.

`measurableSet_isRelaxedTimeWrt`: for a family of lattice paths `w ω` that are right-locally
constant and jointly measurable in `(ω, t)`, and a jointly measurable start `a ω t`, the set
`{(ω, t) | IsRelaxedTimeWrt β (w ω) (a ω t) t}` is measurable. With a fixed start `a` this is the
relative notion along a measurable segment.
-/

@[expose] public section

open MeasureTheory Set

namespace ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]

open scoped Classical in
theorem measurableSet_isRelaxedTimeWrt (w : Ω → ℝ → Fin d → ℤ) (a : Ω → ℝ → ℝ)
    (hw : Measurable fun p : Ω × ℝ => w p.1 p.2) (ha : Measurable fun p : Ω × ℝ => a p.1 p.2)
    (hrc : ∀ ω s, ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), w ω s' = w ω s) :
    MeasurableSet {p : Ω × ℝ | ElboimSly.IsRelaxedTimeWrt β (w p.1) (a p.1 p.2) p.2} := by
  have hb : 0 < β ^ ElboimSly.indDelta d := Real.rpow_pos_of_pos Fact.out _
  set b := β ^ ElboimSly.indDelta d with hbdef
  have hgm : ∀ y : Fin d → ℤ, Measurable fun z : Fin d → ℤ => ‖z - y‖ := fun y =>
    measurable_of_countable _
  -- (R1)
  have R1 : MeasurableSet {p : Ω × ℝ | ∀ r : ℝ, b ≤ r →
      ¬ ElboimSly.IsHeavy (w p.1) (a p.1 p.2) p.2 (w p.1 p.2) r} := by
    have e : {p : Ω × ℝ | ∀ r : ℝ, b ≤ r →
        ¬ ElboimSly.IsHeavy (w p.1) (a p.1 p.2) p.2 (w p.1 p.2) r} =
        ⋂ m : ℕ, {p : Ω × ℝ | b < (m : ℝ) + 1 → ¬ ((max (m : ℝ) b) ^ (5 / 2 : ℝ) ≤
          (((relaxedBox d m).filter fun u =>
            RelaxedVmem (w p.1) (a p.1 p.2) p.2 (w p.1 p.2 + u)).card : ℝ))} := by
      ext p
      simp only [mem_ofPred_eq, mem_iInter]
      have hV : w p.1 '' Icc (a p.1 p.2) p.2 =
          {y | RelaxedVmem (w p.1) (a p.1 p.2) p.2 y} :=
        Set.ext fun y => mem_image_Icc_iff_vmem (w p.1) (hrc p.1) _ _ y
      unfold ElboimSly.IsHeavy ElboimSly.visitedSet
      rw [hV, forall_not_heavy_iff _ _ hb]
      refine forall_congr' fun m => ?_
      rw [ncard_ball_inter]
      rfl
    rw [e]
    refine MeasurableSet.iInter fun m => ?_
    by_cases h : b < (m : ℝ) + 1
    · simp only [h, true_implies]
      have hset : ∀ u : Fin d → ℤ, MeasurableSet
          {p : Ω × ℝ | RelaxedVmem (w p.1) (a p.1 p.2) p.2 (w p.1 p.2 + u)} := fun u =>
        measurableSet_vmem hw ha measurable_snd (hw.add_const u)
      have hcount : Measurable fun p : Ω × ℝ => (((relaxedBox d m).filter fun u =>
            RelaxedVmem (w p.1) (a p.1 p.2) p.2 (w p.1 p.2 + u)).card : ℕ) := by
        have : (fun p : Ω × ℝ => (((relaxedBox d m).filter fun u =>
            RelaxedVmem (w p.1) (a p.1 p.2) p.2 (w p.1 p.2 + u)).card : ℕ)) =
            fun p => ∑ u ∈ relaxedBox d m,
              if RelaxedVmem (w p.1) (a p.1 p.2) p.2 (w p.1 p.2 + u) then 1 else 0 := by
          funext p
          exact Finset.card_filter _ _
        rw [this]
        exact Finset.measurable_sum _ fun u _ =>
          Measurable.ite (hset u) measurable_const measurable_const
      have hcast : Measurable fun p : Ω × ℝ => ((((relaxedBox d m).filter fun u =>
            RelaxedVmem (w p.1) (a p.1 p.2) p.2 (w p.1 p.2 + u)).card : ℕ) : ℝ) :=
        (measurable_from_top (f := fun n : ℕ => (n : ℝ))).comp hcount
      exact (measurableSet_le measurable_const hcast).compl
    · simp [h]
  -- (R2)
  have R2 : MeasurableSet {p : Ω × ℝ | ∀ s : ℝ, a p.1 p.2 ≤ s →
      s ≤ p.2 - β ^ (3 * ElboimSly.indDelta d) → b ≤ ‖w p.1 p.2 - w p.1 s‖} := by
    have e : {p : Ω × ℝ | ∀ s : ℝ, a p.1 p.2 ≤ s →
        s ≤ p.2 - β ^ (3 * ElboimSly.indDelta d) → b ≤ ‖w p.1 p.2 - w p.1 s‖} =
        ⋂ y : Fin d → ℤ, {p : Ω × ℝ | RelaxedVmem (w p.1) (a p.1 p.2)
          (p.2 - β ^ (3 * ElboimSly.indDelta d)) y → b ≤ ‖w p.1 p.2 - y‖} := by
      ext p
      simp only [mem_ofPred_eq, mem_iInter]
      constructor
      · intro h y hy
        obtain ⟨s, ⟨h1, h2⟩, rfl⟩ :=
          (mem_image_Icc_iff_vmem (w p.1) (hrc p.1) _ _ y).2 hy
        exact h s h1 h2
      · intro h s h1 h2
        exact h _ ((mem_image_Icc_iff_vmem (w p.1) (hrc p.1) _ _ _).1 ⟨s, ⟨h1, h2⟩, rfl⟩)
    rw [e]
    refine MeasurableSet.iInter fun y => ?_
    have hP : MeasurableSet {p : Ω × ℝ | RelaxedVmem (w p.1) (a p.1 p.2)
        (p.2 - β ^ (3 * ElboimSly.indDelta d)) y} :=
      measurableSet_vmem hw ha (measurable_snd.sub_const _) measurable_const
    have hQ : MeasurableSet {p : Ω × ℝ | b ≤ ‖w p.1 p.2 - y‖} :=
      measurableSet_le measurable_const ((hgm y).comp hw)
    have : {p : Ω × ℝ | RelaxedVmem (w p.1) (a p.1 p.2)
          (p.2 - β ^ (3 * ElboimSly.indDelta d)) y → b ≤ ‖w p.1 p.2 - y‖} =
        {p : Ω × ℝ | RelaxedVmem (w p.1) (a p.1 p.2)
          (p.2 - β ^ (3 * ElboimSly.indDelta d)) y}ᶜ ∪ {p : Ω × ℝ | b ≤ ‖w p.1 p.2 - y‖} := by
      ext p
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [this]
    exact hP.compl.union hQ
  exact R1.inter R2

end ElboimSly.Paper

end
