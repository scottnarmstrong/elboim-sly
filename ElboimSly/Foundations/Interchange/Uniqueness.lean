/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.Swap
public import ElboimSly.Frozen.Defs.IsForwardTrajectory
public import ElboimSly.Frozen.Defs.IsBackwardTrajectory
public import ElboimSly.Frozen.Defs.IsForwardPath
public import ElboimSly.Frozen.Defs.IsBackwardPath
import Mathlib

/-!
# Uniqueness of trajectories

Existence and uniqueness of trajectories (uniqueness from the initial or terminal value).

Two forward (resp. backward) `ν`-paths with the same value at `0` coincide. The proof looks at the
first time of disagreement and compares the swap rules there; the swap rule determines the
post-jump position, and the pre-jump position is determined by the symmetric swap rule.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- If all points of `B` that are `≥ sInf B` avoid `[sInf B, u0)` with `sInf B < u0`, then `B` is
empty. -/
theorem set_empty_of_gap {B : Set ℝ≥0} (hne : B.Nonempty) (u0 : ℝ≥0) (hlt : sInf B < u0)
    (h : ∀ s ∈ B, u0 ≤ s) : False :=
  absurd (le_csInf hne h) (not_le.mpr hlt)

omit [Fact (0 < β)] in
/-- Two forward paths from the same time with the same initial value coincide. -/
theorem IsForwardPath.eq_of_zero {a : ℝ} {γ γ' : ℝ≥0 → Fin d → ℤ} (h : IsForwardPath ν a γ)
    (h' : IsForwardPath ν a γ') (h0 : γ 0 = γ' 0) : γ = γ' := by
  by_contra hne
  obtain ⟨s0, hs0⟩ := Function.ne_iff.mp hne
  set B : Set ℝ≥0 := {s | γ s ≠ γ' s} with hB
  have hBne : B.Nonempty := ⟨s0, hs0⟩
  set s := sInf B with hs
  have hA : ∀ u, u < s → γ u = γ' u := fun u hu => by
    by_contra hu'
    exact absurd (csInf_le (OrderBot.bddBelow B) (show u ∈ B from hu')) (not_le.mpr hu)
  have hBs : γ s = γ' s := by
    rcases eq_zero_or_pos s with hz | hpos
    · rw [hz]; exact h0
    · obtain ⟨z, hz⟩ := h.2.1 s hpos
      have hz' : IsLeftLimit γ' s z :=
        (hz.and self_mem_nhdsWithin).mono fun u ⟨h1, h2⟩ => (hA u h2).symm.trans h1
      exact SwapRule.unique (h.2.2.2 s hpos z hz) (h'.2.2.2 s hpos z hz')
  obtain ⟨u0, hu0, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp
    ((h.1 s).and (h'.1 s))
  refine set_empty_of_gap hBne u0 hu0 fun u hu => ?_
  by_contra hlt
  have hsu : s ≤ u := csInf_le (OrderBot.bddBelow B) hu
  have := hsub ⟨hsu, not_le.mp hlt⟩
  exact hu ((this.1.trans hBs).trans this.2.symm)

omit [Fact (0 < β)] in
/-- Two backward paths from the same time with the same terminal value coincide. -/
theorem IsBackwardPath.eq_of_zero (hν : Good ν) {b : ℝ} {η η' : ℝ≥0 → Fin d → ℤ}
    (h : IsBackwardPath ν b η) (h' : IsBackwardPath ν b η') (h0 : η 0 = η' 0) : η = η' := by
  by_contra hne
  obtain ⟨s0, hs0⟩ := Function.ne_iff.mp hne
  set B : Set ℝ≥0 := {s | η s ≠ η' s} with hB
  have hBne : B.Nonempty := ⟨s0, hs0⟩
  set s := sInf B with hs
  have hA : ∀ u, u < s → η u = η' u := fun u hu => by
    by_contra hu'
    exact absurd (csInf_le (OrderBot.bddBelow B) (show u ∈ B from hu')) (not_le.mpr hu)
  have hBs : η s = η' s := by
    rcases eq_zero_or_pos s with hz | hpos
    · rw [hz]; exact h0
    · have : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
      have hle : 𝓝[<] s ≤ 𝓝[≤] s := nhdsWithin_mono _ Set.Iio_subset_Iic_self
      obtain ⟨u, ⟨hu1, hu2⟩, hu3⟩ := ((((h.1 s).filter_mono hle).and
        ((h'.1 s).filter_mono hle)).and self_mem_nhdsWithin).exists
      exact hu1.symm.trans ((hA u hu3).trans hu2)
  obtain ⟨z, hz⟩ := h.2.1 s
  obtain ⟨z', hz'⟩ := h'.2.1 s
  have hzz : z = z' := by
    have h1 := SwapRule.symm hν (h.2.2.2 s z hz)
    have h2 := SwapRule.symm hν (h'.2.2.2 s z' hz')
    rw [← hBs] at h2
    exact SwapRule.unique h1 h2
  subst hzz
  obtain ⟨u0, hu0, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hz.and hz')
  refine set_empty_of_gap hBne u0 hu0 fun u hu => ?_
  by_contra hlt
  have hsu : s ≤ u := csInf_le (OrderBot.bddBelow B) hu
  rcases eq_or_lt_of_le hsu with heq | hlt'
  · exact hu (heq ▸ hBs)
  · have := hsub ⟨hlt', not_le.mp hlt⟩
    exact hu (this.1.trans this.2.symm)

omit [Fact (0 < β)] in
/-- Uniqueness of forward trajectories. -/
theorem IsForwardTrajectory.unique {x : Fin d → ℤ} {a : ℝ} {γ γ' : ℝ≥0 → Fin d → ℤ}
    (h : IsForwardTrajectory ν x a γ) (h' : IsForwardTrajectory ν x a γ') : γ = γ' :=
  IsForwardPath.eq_of_zero h.1 h'.1 (h.2.trans h'.2.symm)

omit [Fact (0 < β)] in
/-- Uniqueness of backward trajectories. -/
theorem IsBackwardTrajectory.unique (hν : Good ν) {y : Fin d → ℤ} {b : ℝ}
    {η η' : ℝ≥0 → Fin d → ℤ}
    (h : IsBackwardTrajectory ν y b η) (h' : IsBackwardTrajectory ν y b η') : η = η' :=
  IsBackwardPath.eq_of_zero hν h.1 h'.1 (h.2.trans h'.2.symm)

end ElboimSly.Interchange
