/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.RelaxedClosed
public import ElboimSly.Foundations.Cyclic.CPathJump
public import Mathlib

/-!
# First relaxed times: reduction to jump times

First relaxed times are relaxed and are stopping times (c), pathwise part.  For a path `p` with finitely many jumps,
`prev ≤ lo` and a deadline `s`: the set `S ∩ [lo, s]` is non-empty iff `lo ∈ S` (and `lo ≤ s`),
or some jump time `ς_k ∈ (lo, s]` lies in `S`.  This is the countable reduction of the proof of
part (c) (using the initial-segment property (b)).
-/

@[expose] public section

open Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

variable {d : ℕ}

/-- The real-line extension of a path on `ℝ≥0`. -/
def cpathReal (p : CPath (Fin d → ℤ)) : ℝ → Fin d → ℤ := fun r => p.fn r.toNNReal

lemma cpathReal_const (p : CPath (Fin d → ℤ)) (s : ℝ≥0) :
    ∀ u ∈ Icc ((p.jt (p.cnt s)).toReal) (s : ℝ),
      cpathReal p u = cpathReal p (p.jt (p.cnt s)).toReal := by
  intro u hu
  have hle : p.jt (p.cnt s) ≤ (s : ℝ≥0∞) := (p.jt_le_iff _ _).mpr le_rfl
  have hfin : p.jt (p.cnt s) < ⊤ := hle.trans_lt ENNReal.coe_lt_top
  set J := (p.jt (p.cnt s)).toNNReal with hJ
  have hJe : (p.jt (p.cnt s)).toReal = (J : ℝ) := rfl
  rw [hJe] at hu ⊢
  have hu0 : 0 ≤ u := (NNReal.coe_nonneg J).trans hu.1
  have hUs : u.toNNReal ≤ s := Real.toNNReal_le_iff_le_coe.2 hu.2
  have hJU : J ≤ u.toNNReal := Real.le_toNNReal_iff_coe_le hu0 |>.2 hu.1
  have h1 : p.jt (p.cnt s) ≤ ((u.toNNReal : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_toNNReal hfin.ne]; exact_mod_cast hJU
  have hk1 : p.cnt s ≤ p.cnt u.toNNReal := (p.jt_le_iff _ _).1 h1
  have hk2 := p.cnt_mono hUs
  have hk : p.cnt u.toNNReal = p.cnt s := le_antisymm hk2 hk1
  unfold cpathReal
  rw [Real.toNNReal_coe, p.fn_eq_jv u.toNNReal, hk]
  rfl

/-- Reduction of `∃ s' ∈ S ∩ [lo, s]` to `lo` and the jump times. -/
theorem exists_relaxed_iff_jumps {β : ℝ} (p : CPath (Fin d → ℤ)) {prev lo : ℝ} (hpl : prev ≤ lo)
    (hlo : 0 ≤ lo) (s : ℝ≥0) :
    (∃ s' ∈ relaxedSet β (cpathReal p) prev, lo ≤ s' ∧ s' ≤ s) ↔
      (lo ≤ s ∧ ElboimSly.IsRelaxedTimeWrt β (cpathReal p) prev lo) ∨
      ∃ k : ℕ, lo < (p.jt k).toReal ∧ p.jt k ≤ (s : ℝ≥0∞) ∧
        ElboimSly.IsRelaxedTimeWrt β (cpathReal p) prev (p.jt k).toReal := by
  constructor
  · rintro ⟨s', hs', hls', hss'⟩
    have hs'0 : 0 ≤ s' := hlo.trans hls'
    set s'' : ℝ≥0 := s'.toNNReal with hs''
    have hs'c : (s'' : ℝ) = s' := Real.coe_toNNReal _ hs'0
    set k := p.cnt s'' with hk
    have hle : p.jt k ≤ (s'' : ℝ≥0∞) := (p.jt_le_iff _ _).mpr le_rfl
    have hfin : p.jt k < ⊤ := hle.trans_lt ENNReal.coe_lt_top
    have hes' : (p.jt k).toReal ≤ s' := by
      rw [← hs'c]
      exact (ENNReal.toReal_le_toReal hfin.ne ENNReal.coe_ne_top).2 hle
    have hconst := cpathReal_const p s''
    rw [hs'c] at hconst
    have he0 : 0 ≤ (p.jt k).toReal := ENNReal.toReal_nonneg
    rcases lt_or_ge lo (p.jt k).toReal with hlt | hge
    · right
      refine ⟨k, hlt, ?_, ?_⟩
      · have : p.jt k ≤ (s'' : ℝ≥0∞) := hle
        refine this.trans ?_
        exact_mod_cast (Real.toNNReal_le_iff_le_coe.2 hss')
      · have := mem_relaxedSet_of_le (a := prev) (e := (p.jt k).toReal) hconst hs' le_rfl
          (hpl.trans hlt.le) hes'
        exact this.2
    · left
      have := mem_relaxedSet_of_le (a := prev) (e := (p.jt k).toReal) hconst hs' hge hpl hls'
      exact ⟨by exact_mod_cast (hls'.trans hss'), this.2⟩
  · rintro (⟨hls, hrel⟩ | ⟨k, hlt, hks, hrel⟩)
    · exact ⟨lo, ⟨hpl, hrel⟩, le_rfl, hls⟩
    · have hfin : p.jt k < ⊤ := hks.trans_lt ENNReal.coe_lt_top
      refine ⟨(p.jt k).toReal, ⟨hpl.trans hlt.le, hrel⟩, hlt.le, ?_⟩
      exact (ENNReal.toReal_le_toReal hfin.ne ENNReal.coe_ne_top).2 hks

end ElboimSly.Paper
