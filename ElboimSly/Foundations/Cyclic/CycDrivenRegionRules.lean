/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenRegionBasic
public import Mathlib

/-!
# The driven walk obeys the rules (D1')-(D3')

The driven walk is a driven world-line, paragraph "The rules agree". First, the existence of a
known ring in the class of `r` at `w(r-)` is the same as the condition of (D1).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {ι : I} {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {x : ℝ≥0 → Fin d → ℤ}

/-- An edge between the endpoints of a unit step. -/
def unitEdge (u v : Fin d → ℤ) (h : ∑ i, |u i - v i| = 1) : Edge d :=
  ⟨s(u, v), u, v, rfl, h⟩

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem mem_drvQown {p : CPath (Fin d → ℤ)} {r : ℝ≥0} {e : Edge d} {θ : AddCircle β} :
    ((ι, (e, θ)) : I × RingSpace d β) ∈ drvQown β (regionData d ι) p r ↔
      ∃ r' : ℝ≥0, 0 < r' ∧ r' < r ∧ p.left r' ≠ p.fn r' ∧
        θ = (regionData d ι).clock β r' ∧ e.1 = s(p.left r', p.fn r') := by
  simp [drvQown, regionData, CycData.copy]

omit [MeasurableSpace I] in
/-- A known ring at the clock of `r` containing `w(r-)` exists iff (D1) applies. -/
theorem exists_edge_iff (hx : IsDrivingPath x) (hβ : 0 < β.toNNReal)
    (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β.toNNReal)
    {r : ℝ≥0} (_hr : 0 < r) (hrτ : (r : ℝ≥0∞) ≤ drivenTreg β.toNNReal x) :
    (∃ e : Edge d, Edge.Mem (leftVal (drivenWalk β.toNNReal x) r) e ∧
      ((ι, (e, (regionData d ι).clock β r)) : I × RingSpace d β) ∈
        drvQown β (regionData d ι) (drivenCPath hx hβ) r) ↔
    ∃ k, ForcedAt β.toNNReal (drivenWalk β.toNNReal x) r k := by
  obtain ⟨-, -, -, -, -, b2, -⟩ := drivenWalk_closing hx hβ hi
  have hunit := (drivenWalk_wd_a hx hβ).2.2.2.2.1
  constructor
  · rintro ⟨e, hmem, hq⟩
    rw [mem_drvQown] at hq
    obtain ⟨r', hr'0, hr'r, hne, hclock, he⟩ := hq
    obtain ⟨k, hk1, hshift⟩ := clock_eq_shift (regionData d ι) hr'r hclock.symm
    have hsh := shift_nnreal.1 hshift
    have hsub : r - k * β.toNNReal = r' := by rw [hsh]; simp
    have hdisc : r' ∈ CDisc (drivenWalk β.toNNReal x) :=
      ((drivenCPath hx hβ).mem_CDisc_iff hr'0).2 hne
    rw [drivenCPath_left hx hβ hr'0] at he
    have hmem' : leftVal (drivenWalk β.toNNReal x) r ∈ e.1 := hmem
    rw [he, Sym2.mem_iff] at hmem'
    rcases hmem' with h | h
    · exact absurd h.symm (b2 r r' k hr'0 hk1 hsh hrτ ∘ Eq.symm)
    · refine ⟨k, ⟨hk1, ?_⟩, ?_, ?_⟩
      · rw [hsh]; exact le_add_self
      · rw [hsub]; exact hdisc
      · rw [hsub]; exact h.symm
  · rintro ⟨k, ⟨hk1, hkr⟩, hdisc, heq⟩
    set r' := r - k * β.toNNReal with hr'
    have hr'0 : 0 < r' := hdisc.1
    have hr'r : r' < r := delayIdx_lt β.toNNReal hβ ⟨hk1, hkr⟩
    have hne : leftVal (drivenWalk β.toNNReal x) r' ≠ drivenWalk β.toNNReal x r' := by
      intro h
      exact hdisc.2 (by
        have := (drivenCPath hx hβ).eventually_left hr'0
        have e1 : (drivenCPath hx hβ).left r' = drivenWalk β.toNNReal x r' := by
          rw [drivenCPath_left hx hβ hr'0]; exact h
        exact this.mono fun u hu => hu.trans e1)
    have hstep := hunit r' hdisc
    have hadj : ∑ i, |leftVal (drivenWalk β.toNNReal x) r' i - drivenWalk β.toNNReal x r' i| = 1 := by
      rw [← hstep]
      exact Finset.sum_congr rfl fun i _ => by simp [abs_sub_comm]
    refine ⟨unitEdge _ _ hadj, ?_, ?_⟩
    · show _ ∈ s(_, _)
      rw [Sym2.mem_iff]; right; exact heq.symm
    · rw [mem_drvQown]
      refine ⟨r', hr'0, hr'r, ?_, ?_, ?_⟩
      · rw [drivenCPath_left hx hβ hr'0]; exact hne
      · symm
        apply clock_eq_of_shift (k := k)
        rw [shift_nnreal]
        rw [hr']; exact (tsub_add_cancel_of_le hkr).symm
      · rw [drivenCPath_left hx hβ hr'0]; rfl

end ElboimSly.Cyclic

end
