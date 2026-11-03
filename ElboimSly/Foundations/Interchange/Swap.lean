/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.Good
public import ElboimSly.Frozen.Defs.SwapRule
public import ElboimSly.Frozen.Defs.IsLeftLimit
public import ElboimSly.Frozen.Defs.IsRightLimit
import Mathlib

/-!
# The swap rule for good configurations

Time symmetry of the swap rule; ν-paths.

For a good configuration at most one edge rings at a given real time (G2). Hence the swap rule
determines the post-jump position from the pre-jump position and is symmetric in the two
positions.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- Some edge containing `z` rings at the real time `t`. -/
def RingAt (ν : Measure (RingSpace d β)) (z : Fin d → ℤ) (t : ℝ) : Prop :=
  ∃ e : Edge d, e.Mem z ∧ Rings ν e t

omit [Fact (0 < β)] in
/-- At most one edge rings at a given time (G2). -/
theorem edge_unique (hν : Good ν) {e f : Edge d} {t : ℝ} (he : Rings ν e t) (hf : Rings ν f t) :
    e = f := by
  by_contra h
  exact Set.disjoint_left.mp (hν.2.2.1.2 e f h) he hf

omit [Fact (0 < β)] in
/-- The swap rule determines the post-jump position. -/
theorem SwapRule.unique {t : ℝ} {z w w' : Fin d → ℤ} (h : SwapRule ν t z w)
    (h' : SwapRule ν t z w') : w = w' := by
  by_cases hr : ∃ e : Edge d, e.Mem z ∧ Rings ν e t
  · obtain ⟨e, hz, he⟩ := hr
    exact Sym2.congr_right.mp ((h.1 e hz he).symm.trans (h'.1 e hz he))
  · exact (h.2 hr).trans (h'.2 hr).symm

omit [Fact (0 < β)] in
/-- If no edge at `z` rings at `t`, nothing moves. -/
theorem swapRule_self {t : ℝ} {z : Fin d → ℤ} (h : ¬ RingAt ν z t) : SwapRule ν t z z :=
  ⟨fun e hz he => absurd ⟨e, hz, he⟩ h, fun _ => rfl⟩

omit [Fact (0 < β)] in
/-- A ringing edge `{z, w}` makes `z` jump to `w`. -/
theorem swapRule_of_edge (hν : Good ν) {t : ℝ} {z w : Fin d → ℤ} (e : Edge d)
    (he : e.1 = s(z, w)) (hr : Rings ν e t) : SwapRule ν t z w := by
  refine ⟨fun f _ hf => ?_, fun hn => ?_⟩
  · rw [edge_unique hν hf hr]; exact he
  · exact absurd ⟨e, by unfold Edge.Mem; rw [he]; exact Sym2.mem_mk_left _ _, hr⟩ hn

omit [Fact (0 < β)] in
/-- Time symmetry of the swap rule. Time symmetry of the swap rule. -/
theorem SwapRule.symm (hν : Good ν) {t : ℝ} {z w : Fin d → ℤ} (h : SwapRule ν t z w) :
    SwapRule ν t w z := by
  by_cases hzw : w = z
  · subst hzw; exact h
  · have : ∃ e : Edge d, e.Mem z ∧ Rings ν e t := by
      by_contra hn; exact hzw (h.2 hn)
    obtain ⟨e0, hz0, he0⟩ := this
    have h1 := h.1 e0 hz0 he0
    refine ⟨fun e _ he => ?_, fun hn => ?_⟩
    · rw [edge_unique hν he he0, h1, Sym2.eq_swap]
    · exact absurd ⟨e0, by unfold Edge.Mem; rw [h1]; exact Sym2.mem_mk_right _ _, he0⟩ hn

/-- Left limits are unique at positive times. -/
theorem IsLeftLimit.unique {γ : ℝ≥0 → Fin d → ℤ} {s : ℝ≥0} (hs : 0 < s) {z z' : Fin d → ℤ}
    (h : IsLeftLimit γ s z) (h' : IsLeftLimit γ s z') : z = z' := by
  have : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hs⟩
  obtain ⟨u, hu, hu'⟩ := (h.and h').exists
  exact hu.symm.trans hu'

/-- Right limits are unique. -/
theorem IsRightLimit.unique {γ : ℝ≥0 → Fin d → ℤ} {s : ℝ≥0} {z z' : Fin d → ℤ}
    (h : IsRightLimit γ s z) (h' : IsRightLimit γ s z') : z = z' := by
  have : (𝓝[>] s).NeBot := inferInstance
  obtain ⟨u, hu, hu'⟩ := (h.and h').exists
  exact hu.symm.trans hu'

end ElboimSly.Interchange
