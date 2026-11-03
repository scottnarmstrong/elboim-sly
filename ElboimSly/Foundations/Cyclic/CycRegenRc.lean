/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenPiece
public import ElboimSly.Foundations.Cyclic.CycHitThit
public import Mathlib

/-!
# Right-local constancy of the regenerated walk

ES22 Lemma 2.1 (e), proof ("both sides are right-continuous and
`ℤᵈ`-valued"). The cyclic walk is right-locally constant (`cycWalk_const_near`), hence so is the
regenerated walk (`regenWalk_const_near`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

theorem cycWalk_const_near (hν : Good ν) {r : ℝ} (hr : 0 ≤ r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, r ≤ s → s < r + ε →
      ElboimSly.cycWalk ν 0 0 s = ElboimSly.cycWalk ν 0 0 r := by
  have hev := (fwdTrajFn_spec hν (0 : Fin d → ℤ) 0).1.1 r.toNNReal
  obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
  refine ⟨(u' : ℝ) - r, ?_, fun s hrs hs => ?_⟩
  · have : r < (u' : ℝ) := by
      have := (Real.toNNReal_lt_iff_lt_coe hr).1 hu'
      exact this
    linarith
  · have hs0 : 0 ≤ s := hr.trans hrs
    rw [cycWalk_of_nonneg hν 0 0 hs0, cycWalk_of_nonneg hν 0 0 hr]
    have hmem : (0 + s - 0).toNNReal ∈ Ico r.toNNReal u' := by
      refine ⟨?_, ?_⟩
      · simpa using Real.toNNReal_le_toNNReal hrs
      · rw [zero_add, sub_zero]
        exact (Real.toNNReal_lt_iff_lt_coe hs0).2 (by linarith)
    have := hsub hmem
    simp only [mem_ofPred_eq] at this
    unfold fwdTraj fwdReal
    simpa only [zero_add, sub_zero] using this

theorem regenWalk_const_near {ν : ℕ → Measure (RingSpace d β)} (hg : ∀ j, Good (ν j)) {t : ℝ}
    (ht : 0 ≤ t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, t ≤ s → s < t + ε →
      ElboimSly.regenWalk ν s = ElboimSly.regenWalk ν t := by
  set k := ElboimSly.regenCount ν t with hk
  have hkfin : ElboimSly.regenSigma ν k < ⊤ := regenSigma_count_lt_top ν ht
  set a := ElboimSly.regenStart ν t with ha
  have ha' : a = (ElboimSly.regenSigma ν k).toReal := rfl
  have hu0 : 0 ≤ t - a := sub_nonneg.2 (regenStart_le ν ht)
  have hlt := ofReal_sub_regenStart_lt ν ht
  rw [← hk] at hlt
  obtain ⟨ε₀, hε₀, hc⟩ := cycWalk_const_near (hg k) hu0
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hlt
  have hur : t - a < r := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hu0).1 hr1
  refine ⟨min ε₀ (r - (t - a)), lt_min hε₀ (by linarith), fun s hts hsε => ?_⟩
  have hs1 : s - a < t - a + ε₀ := by
    have := (lt_min_iff.1 (show s - t < min ε₀ (r - (t - a)) by linarith)).1
    linarith
  have hs2 : s - a < r := by
    have := (lt_min_iff.1 (show s - t < min ε₀ (r - (t - a)) by linarith)).2
    linarith
  have hs0 : 0 ≤ s - a := by linarith
  have h1 := regenWalk_piece hg k hkfin hs0 ((ENNReal.ofReal_le_ofReal hs2.le).trans hr2.le)
  rw [← ha'] at h1
  rw [show a + (s - a) = s by ring] at h1
  rw [h1]
  unfold ElboimSly.regenWalk
  rw [← hk, ← ha]
  exact hc (s - a) (by linarith) hs1

end ElboimSly.Cyclic

end
