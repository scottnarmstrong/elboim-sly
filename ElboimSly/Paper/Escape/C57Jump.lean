/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C57Geom
public import ElboimSly.Foundations.Cyclic.CPathJump
public import ElboimSly.Foundations.Cyclic.CPathCount
public import ElboimSly.Foundations.Cyclic.CPathLeft
public import Mathlib

/-!
# The first exit from `𝒬` in terms of the jumps of the path

The box escQ, the backward walks and zeta_i (`r_i`, `W_i^←(r_i)`).

`ExitJ Q F S p`: the path `p` (starting in `Q`) makes a jump at a time `jt a ≤ S` whose value is in
`F`, and its values `jv b` before are in `Q`.  This says that the first exit time `r_i` of `p` from
`Q` is `jt a ≤ S` and `p(r_i) ∈ F` (`F` disjoint from `Q`); it is a countable condition on the jump
data, hence measurable (`ExitJ` is the event "`r_i ≤ 4^{j-1}`, `W_i^←(r_i) ∈ F_B`").

* `exitJ_of_exit`: from the pointwise description of the exit.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ}

/-- The path makes its `a`-th jump at a time `≤ S`, with value in `F`, after having stayed in `Q`. -/
def ExitJ (Q F : Set (EscV k)) (S : ℝ≥0∞) (p : CPath (EscV k)) : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ p.jt a ≤ S ∧ p.jv a ∈ F ∧ ∀ b < a, p.jv b ∈ Q

theorem jt_mono_le (p : CPath (EscV k)) {b a : ℕ} (h : b ≤ a) : p.jt b ≤ p.jt a := by
  refine le_iInf fun s => ?_
  exact (p.jt_le_iff b s.1).2 (le_trans h s.2)

theorem jt_lt_of_lt (p : CPath (EscV k)) {b a : ℕ} (hba : b < a) (ha : p.jt a < ⊤) :
    p.jt b < p.jt a := by
  obtain ⟨d, rfl⟩ : ∃ d, a = b + 1 + d := ⟨a - b - 1, by omega⟩
  induction d with
  | zero => exact p.jt_lt_succ ha
  | succ d ih =>
    have h1 : p.jt (b + 1 + d) ≤ p.jt (b + 1 + (d + 1)) := jt_mono_le p (by omega)
    exact lt_of_lt_of_le (ih (by omega) (lt_of_le_of_lt h1 ha)) h1

/-- From the pointwise description of the first exit to the jump description. -/
theorem exitJ_of_exit {Q F : Set (EscV k)} (hFQ : Disjoint F Q) (w : CPath (EscV k)) {r S : ℝ≥0}
    (hr : 0 < r) (hrS : r ≤ S) (hin : ∀ s : ℝ≥0, s < r → w.fn s ∈ Q) (hout : w.fn r ∈ F) :
    ExitJ Q F (S : ℝ≥0∞) w := by
  have hne : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
  obtain ⟨s₁, hs₁, hs₁r⟩ := ((w.eventually_left hr).and
    (self_mem_nhdsWithin (a := r) (s := Iio r))).exists
  have hleft : w.left r ∈ Q := by rw [← hs₁]; exact hin s₁ hs₁r
  have hdisc : r ∈ CDisc w.fn := (w.mem_CDisc_iff hr).2 (fun h => by
    have : w.fn r ∈ Q := h ▸ hleft
    exact Set.disjoint_left.1 hFQ hout this)
  set a := w.cnt r with ha
  have hfin : (CDisc w.fn ∩ Iic r).Finite := w.fin r
  have ha1 : 1 ≤ a := by
    have : 0 < a := Set.ncard_pos hfin |>.2 ⟨r, hdisc, le_rfl⟩
    exact this
  have hjtle : w.jt a ≤ (r : ℝ≥0∞) := (w.jt_le_iff a r).2 le_rfl
  have hlt : ∀ s : ℝ≥0, s < r → w.cnt s < a := by
    intro s hs
    have hsub : CDisc w.fn ∩ Iic s ⊂ CDisc w.fn ∩ Iic r := by
      refine ⟨fun x hx => ⟨hx.1, hx.2.trans hs.le⟩, fun hsup => ?_⟩
      have := hsup ⟨hdisc, le_rfl⟩
      exact absurd this.2 (not_le.2 hs)
    exact Set.ncard_lt_ncard hsub hfin
  have hjt : w.jt a = (r : ℝ≥0∞) := by
    refine le_antisymm hjtle ?_
    by_contra hcon
    rw [not_le] at hcon
    have hfin' : w.jt a < ⊤ := lt_of_le_of_lt hjtle ENNReal.coe_lt_top
    set s₀ := (w.jt a).toNNReal with hs₀
    have hs₀eq : (s₀ : ℝ≥0∞) = w.jt a := ENNReal.coe_toNNReal hfin'.ne
    have hs₀r : s₀ < r := by
      rw [← hs₀eq] at hcon; exact_mod_cast hcon
    have := hlt s₀ hs₀r
    have h2 : a ≤ w.cnt s₀ := (w.jt_le_iff a s₀).1 hs₀eq.symm.le
    omega
  refine ⟨a, ha1, ?_, ?_, ?_⟩
  · rw [hjt]; exact_mod_cast hrS
  · show w.fn (w.jt a).toNNReal ∈ F
    rw [hjt, ENNReal.toNNReal_coe]; exact hout
  · intro b hb
    have hlt' : w.jt b < w.jt a := jt_lt_of_lt w hb (by rw [hjt]; exact ENNReal.coe_lt_top)
    rw [hjt] at hlt'
    have hbfin : w.jt b < ⊤ := lt_trans hlt' ENNReal.coe_lt_top
    have hbeq : ((w.jt b).toNNReal : ℝ≥0∞) = w.jt b := ENNReal.coe_toNNReal hbfin.ne
    have hbr : (w.jt b).toNNReal < r := by
      rw [← hbeq] at hlt'; exact_mod_cast hlt'
    exact hin _ hbr

end ElboimSly.Paper.Escape
