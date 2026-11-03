/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.PiecesClosing
public import ElboimSly.Foundations.Cyclic.CycRegenEnv
public import ElboimSly.Frozen.Defs.IsRelaxedTime
public import ElboimSly.Frozen.Defs.RegenCount
public import ElboimSly.Frozen.Defs.RegenStart

/-!
# The regenerated walk in terms of its pieces

The pieces are cyclic paths (b) (supplement).

Piece `k` (ES22's piece `k + 1`) uses the environment `ν k`; `σ_k = regenSigma ν k`.

* `regen_piece`: for `s ∈ [σ_k, σ_{k+1})`, `𝔑_s = k`, `α(s) = σ_k`, `W(s) = W^{ν k}(s - σ_k)`,
  and `s` is relaxed iff `s - σ_k ∈ 𝒯(W^{ν k})`.
* `regen_piece_end`: `W(σ_{k+1}) = 0 = W^{ν k}(t_reg)`.
* `isRelaxedTimeWrt_shift`: relaxedness depends only on the path on `[a, t]`, up to translation.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : ℕ → Measure (RingSpace d β)}

omit [Fact (0 < β)] in
theorem regenSigma_succ (ν : ℕ → Measure (RingSpace d β)) (k : ℕ) :
    regenSigma ν (k + 1) = regenSigma ν k + cycTreg (ν k) := by
  unfold regenSigma
  rw [Finset.sum_range_succ]

omit [Fact (0 < β)] in
theorem regenSigma_mono (ν : ℕ → Measure (RingSpace d β)) : Monotone (regenSigma ν) :=
  monotone_nat_of_le_succ fun k => by rw [regenSigma_succ]; exact le_self_add

theorem regenSigma_lt_succ {k : ℕ} (hk : regenSigma ν k < ⊤) :
    regenSigma ν k < regenSigma ν (k + 1) := by
  rw [regenSigma_succ]
  have h : (ENNReal.ofReal β) ≤ cycTreg (ν k) := by
    have := regPlan_tau_ge (ν k)
    simpa [ENNReal.ofReal, Real.toNNReal] using this
  have hβ : 0 < β := Fact.out
  exact ENNReal.lt_add_right hk.ne ((ENNReal.ofReal_pos.2 hβ).trans_le h).ne'

omit [Fact (0 < β)] in
theorem regenCount_eq {k : ℕ} {s : ℝ} (h1 : regenSigma ν k ≤ ENNReal.ofReal s)
    (h2 : ENNReal.ofReal s < regenSigma ν (k + 1)) : regenCount ν s = k := by
  unfold regenCount
  refine IsGreatest.csSup_eq ⟨h1, fun i hi => ?_⟩
  by_contra hc
  push Not at hc
  exact absurd (lt_of_lt_of_le h2 ((regenSigma_mono ν (by omega : k + 1 ≤ i)).trans hi))
    (lt_irrefl _)

omit [Fact (0 < β)] in
/-- The pieces are cyclic paths (b). -/
theorem regen_piece {k : ℕ} {s : ℝ} (h1 : regenSigma ν k ≤ ENNReal.ofReal s)
    (h2 : ENNReal.ofReal s < regenSigma ν (k + 1)) :
    regenCount ν s = k ∧ regenStart ν s = (regenSigma ν k).toReal ∧
      regenWalk ν s = cycWalk (ν k) 0 0 (s - (regenSigma ν k).toReal) := by
  have hc := regenCount_eq h1 h2
  have hs : regenStart ν s = (regenSigma ν k).toReal := by
    unfold regenStart; rw [hc]
  refine ⟨hc, hs, ?_⟩
  unfold regenWalk; rw [hc, hs]

omit [Fact (0 < β)] in
/-- The pieces are cyclic paths (b): the walk at `σ_k + u` for `u` below the closing time. -/
theorem regenWalk_add_sigma {k : ℕ} (hk : regenSigma ν k < ⊤) {u : ℝ} (hu : 0 ≤ u)
    (hut : ENNReal.ofReal u < cycTreg (ν k)) :
    regenWalk ν ((regenSigma ν k).toReal + u) = cycWalk (ν k) 0 0 u := by
  have hσ : ENNReal.ofReal ((regenSigma ν k).toReal) = regenSigma ν k :=
    ENNReal.ofReal_toReal hk.ne
  have hadd : ENNReal.ofReal ((regenSigma ν k).toReal + u) = regenSigma ν k + ENNReal.ofReal u := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hu, hσ]
  obtain ⟨_, _, h3⟩ := regen_piece (ν := ν) (k := k) (s := (regenSigma ν k).toReal + u)
    (by rw [hadd]; exact le_self_add)
    (by rw [hadd, regenSigma_succ]; exact ENNReal.add_lt_add_left hk.ne hut)
  rw [h3]; congr 1; ring

/-- The pieces are cyclic paths (b): at the closing time both sides are `0`. -/
theorem regenWalk_add_sigma_treg (hν : ∀ k, Good (ν k)) {k : ℕ} (hk : regenSigma ν (k + 1) < ⊤) :
    regenWalk ν (regenSigma ν (k + 1)).toReal = 0 ∧
      cycWalk (ν k) 0 0 (cycTreg (ν k)).toReal = 0 := by
  have hk0 : regenSigma ν k < ⊤ := lt_of_le_of_lt (regenSigma_mono ν (Nat.le_succ k)) hk
  have htr : cycTreg (ν k) < ⊤ := by
    rw [regenSigma_succ] at hk
    exact lt_of_le_of_lt le_add_self hk
  obtain ⟨n, hn, h0, he⟩ := exists_cycTreg_eq htr
  have hβ : 0 < β := Fact.out
  have hz : cycWalk (ν k) 0 0 (cycTreg (ν k)).toReal = 0 := by
    rw [he, ENNReal.toReal_ofReal (by positivity)]; exact h0
  refine ⟨?_, hz⟩
  have hσ : ENNReal.ofReal ((regenSigma ν (k + 1)).toReal) = regenSigma ν (k + 1) :=
    ENNReal.ofReal_toReal hk.ne
  obtain ⟨_, _, h3⟩ := regen_piece (ν := ν) (k := k + 1) (s := (regenSigma ν (k + 1)).toReal)
    (by rw [hσ]) (by rw [hσ]; exact regenSigma_lt_succ hk)
  rw [h3, sub_self]
  exact cycWalk_zero (hν (k + 1)) 0 0

/-- Relaxedness of `t` with respect to `w|[a,t]` depends only on `u ↦ w(a + u)`, `u ∈ [0, t - a]`. -/
theorem isRelaxedTimeWrt_shift {w w' : ℝ → Fin d → ℤ} {a t : ℝ} (hat : a ≤ t)
    (h : ∀ u : ℝ, 0 ≤ u → u ≤ t - a → w (a + u) = w' u) :
    IsRelaxedTimeWrt β w a t ↔ IsRelaxedTimeWrt β w' 0 (t - a) := by
  have hvis : visitedSet w a t = visitedSet w' 0 (t - a) := by
    ext v
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s - a, ⟨by linarith [hs.1], by linarith [hs.2]⟩, by
        rw [← h (s - a) (by linarith [hs.1]) (by linarith [hs.2])]; congr 1; ring⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨a + u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, h u hu.1 hu.2⟩
  have ht : w t = w' (t - a) := by
    have := h (t - a) (by linarith) le_rfl
    rwa [show a + (t - a) = t by ring] at this
  unfold IsRelaxedTimeWrt IsHeavy
  rw [hvis, ht]
  refine and_congr Iff.rfl ?_
  have hp : 0 ≤ β ^ (3 * indDelta d) := Real.rpow_nonneg (Fact.out : 0 < β).le _
  constructor
  · intro H u hu0 hu
    have := H (a + u) (by linarith) (by linarith)
    rwa [h u hu0 (by linarith)] at this
  · intro H s hs0 hs
    have := H (s - a) (by linarith) (by linarith)
    rwa [← h (s - a) (by linarith) (by linarith), show a + (s - a) = s by ring] at this

end ElboimSly.Paper
