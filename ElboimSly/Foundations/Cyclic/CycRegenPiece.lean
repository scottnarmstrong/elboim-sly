/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Concentration.GeometricDet
public import ElboimSly.Foundations.Cyclic.CycClosing
public import ElboimSly.Foundations.Cyclic.CycWalkTraj
public import Mathlib

/-!
# The regenerated walk on a piece, and shifting the sequence of pieces

ES22 Lemma 2.1 (proof of (a), (c), (d)): on `[σ_k, σ_{k+1}]` the regenerated
walk is the cyclic walk of piece `k` (`regenWalk_piece`), the current piece at time `t` is
`regenCount ν t` (`regenSigma_count`), and removing the first `k` pieces shifts the walk by
`σ_k` (`regenWalk_shift`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] (ν : ℕ → Measure (RingSpace d β))

theorem regenSigma_count {t : ℝ} (ht : 0 ≤ t) :
    ElboimSly.regenSigma ν (ElboimSly.regenCount ν t) ≤ ENNReal.ofReal t ∧
      ENNReal.ofReal t < ElboimSly.regenSigma ν (ElboimSly.regenCount ν t + 1) := by
  refine ⟨(le_regenCount_iff ν ht _).1 le_rfl, ?_⟩
  by_contra h
  exact absurd ((le_regenCount_iff ν ht _).2 (not_lt.1 h)) (by omega)

omit [Fact (0 < β)] in
theorem regenStart_nonneg (t : ℝ) : 0 ≤ ElboimSly.regenStart ν t := ENNReal.toReal_nonneg

theorem regenStart_le {t : ℝ} (ht : 0 ≤ t) : ElboimSly.regenStart ν t ≤ t := by
  unfold ElboimSly.regenStart
  exact ENNReal.toReal_le_of_le_ofReal ht (regenSigma_count ν ht).1

theorem regenSigma_count_lt_top {t : ℝ} (ht : 0 ≤ t) :
    ElboimSly.regenSigma ν (ElboimSly.regenCount ν t) < ⊤ :=
  lt_of_le_of_lt (regenSigma_count ν ht).1 ENNReal.ofReal_lt_top

/-- The time `t` lies strictly inside its current piece: `t - α(t) < t_reg^{(k+1)}`. -/
theorem ofReal_sub_regenStart_lt {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (t - ElboimSly.regenStart ν t) <
      ElboimSly.cycTreg (ν (ElboimSly.regenCount ν t)) := by
  obtain ⟨h1, h2⟩ := regenSigma_count ν ht
  set k := ElboimSly.regenCount ν t
  have hfin := regenSigma_count_lt_top ν ht
  have hσ : ENNReal.ofReal (ElboimSly.regenStart ν t) = ElboimSly.regenSigma ν k :=
    ENNReal.ofReal_toReal hfin.ne
  rw [regenSigma_succ, ← hσ] at h2
  have hle := regenStart_le ν ht
  rw [ENNReal.ofReal_sub _ (regenStart_nonneg ν t)]
  refine ENNReal.sub_lt_of_lt_add (ENNReal.ofReal_le_ofReal hle) ?_
  rwa [add_comm]

variable {ν}

/-- On `[σ_k, σ_{k+1}]` the regenerated walk is the cyclic walk of piece `k`. -/
theorem regenWalk_piece (hg : ∀ j, Good (ν j)) (k : ℕ)
    (hk : ElboimSly.regenSigma ν k < ⊤) {u : ℝ} (hu : 0 ≤ u)
    (hu' : ENNReal.ofReal u ≤ ElboimSly.cycTreg (ν k)) :
    ElboimSly.regenWalk ν ((ElboimSly.regenSigma ν k).toReal + u) =
      ElboimSly.cycWalk (ν k) 0 0 u := by
  have hβ : 0 < β := Fact.out
  set a := (ElboimSly.regenSigma ν k).toReal with ha
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hσ : ENNReal.ofReal a = ElboimSly.regenSigma ν k := ENNReal.ofReal_toReal hk.ne
  have hau : 0 ≤ a + u := by linarith
  rcases hu'.lt_or_eq with hlt | heq
  · have hc : ElboimSly.regenCount ν (a + u) = k := by
      refine regenCount_eq ν hau ?_ ?_
      · rw [ENNReal.ofReal_add ha0 hu, hσ]; exact le_self_add
      · rw [regenSigma_succ, ENNReal.ofReal_add ha0 hu, hσ]
        exact ENNReal.add_lt_add_left hk.ne hlt
    unfold ElboimSly.regenWalk ElboimSly.regenStart
    rw [hc, ← ha]
    congr 1; ring
  · have hfin : ElboimSly.cycTreg (ν k) < ⊤ := heq ▸ ENNReal.ofReal_lt_top
    have hu_eq : u = (ElboimSly.cycTreg (ν k)).toReal := by
      rw [← heq, ENNReal.toReal_ofReal hu]
    have hs1 : ElboimSly.regenSigma ν (k + 1) = ENNReal.ofReal (a + u) := by
      rw [regenSigma_succ, ENNReal.ofReal_add ha0 hu, hσ, heq]
    have hc : ElboimSly.regenCount ν (a + u) = k + 1 := by
      refine regenCount_eq ν hau hs1.le ?_
      rw [regenSigma_succ, hs1]
      refine ENNReal.lt_add_right ENNReal.ofReal_ne_top ?_
      exact (lt_of_lt_of_le (by simpa using hβ) (regPlan_tau_ge (ν (k + 1)))).ne'
    have hst : ElboimSly.regenStart ν (a + u) = a + u := by
      unfold ElboimSly.regenStart
      rw [hc, hs1, ENNReal.toReal_ofReal hau]
    unfold ElboimSly.regenWalk
    rw [hc, hst, sub_self, cycWalk_zero (hg (k + 1)), hu_eq]
    have := cycWalk_add_treg (hg k) hfin 0
    rw [zero_add, cycWalk_zero (hg k)] at this
    exact this.symm

end ElboimSly.Cyclic

end
