/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.PiecesRegen

/-!
# The pieces are cyclic paths

The pieces are cyclic paths (supplement).

For environments `ν k` that are all good (an almost sure property of the Poisson environments):

* `es6_pieces_a`: piece `k` is a cyclic path with the no-return property and closing time
  `t_reg(ν k)`;
* `es6_pieces_b`: for `s ∈ [σ_k, σ_{k+1})`, `α(s) = σ_k`, `W(s) = W^{ν k}(s - σ_k)`, and
  `s ∈ 𝒯` iff `s - σ_k ∈ 𝒯(W^{ν k})`; also `W(σ_k + u) = W^{ν k}(u)` for `u ≤ t_reg`;
* `es6_pieces_c`: restart at cyclic integer times.

The statement about measurability of the `σ_i` and pieces as functions of the path of `W` belongs
to the measurability results on the regenerated walk (the constructions of the regenerated walk) and is not repeated
here.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : ℕ → Measure (RingSpace d β)}

/-- The pieces are cyclic paths (a). -/
theorem es6_pieces_a (hν : ∀ k, Good (ν k)) (k : ℕ) :
    IsCyclicPath (fun s : ℝ => cycWalk (ν k) 0 0 s) ∧
      HasNoReturn β (fun s : ℝ => cycWalk (ν k) 0 0 s) ∧
      cycClosingTime β (fun s : ℝ => cycWalk (ν k) 0 0 s) = cycTreg (ν k) :=
  ⟨isCyclicPath_cycWalk (hν k), hasNoReturn_cycWalk (hν k), cycClosingTime_cycWalk _⟩

/-- The pieces are cyclic paths (b): `W(σ_k + u) = W^{ν k}(u)` for `u ∈ [0, t_reg]`. -/
theorem es6_pieces_b_walk (hν : ∀ k, Good (ν k)) {k : ℕ} (hk : regenSigma ν k < ⊤) {u : ℝ}
    (hu : 0 ≤ u) (hut : ENNReal.ofReal u ≤ cycTreg (ν k)) :
    regenWalk ν ((regenSigma ν k).toReal + u) = cycWalk (ν k) 0 0 u := by
  rcases hut.lt_or_eq with hlt | heq
  · exact regenWalk_add_sigma hk hu hlt
  · have htr : cycTreg (ν k) < ⊤ := heq ▸ ENNReal.ofReal_lt_top
    have hk1 : regenSigma ν (k + 1) < ⊤ := by
      rw [regenSigma_succ]; exact ENNReal.add_lt_top.2 ⟨hk, htr⟩
    have hu' : u = (cycTreg (ν k)).toReal := by
      rw [← heq, ENNReal.toReal_ofReal hu]
    obtain ⟨h1, h2⟩ := regenWalk_add_sigma_treg hν hk1
    rw [hu', h2]
    rw [regenSigma_succ, ENNReal.toReal_add hk.ne htr.ne] at h1
    exact h1

/-- The pieces are cyclic paths (b): for `s ∈ [σ_k, σ_{k+1})`, `α(s) = σ_k`, and `s` is relaxed iff
`s - σ_k` is relaxed for piece `k`. -/
theorem es6_pieces_b_relaxed (_hν : ∀ k, Good (ν k)) {k : ℕ} (hk : regenSigma ν k < ⊤) {s : ℝ}
    (hs0 : 0 ≤ s) (h1 : regenSigma ν k ≤ ENNReal.ofReal s)
    (h2 : ENNReal.ofReal s < regenSigma ν (k + 1)) :
    regenStart ν s = (regenSigma ν k).toReal ∧
      (IsRelaxedTime ν s ↔
        IsRelaxedTimeWrt β (fun x : ℝ => cycWalk (ν k) 0 0 x) 0 (s - (regenSigma ν k).toReal)) := by
  obtain ⟨_, hstart, _⟩ := regen_piece h1 h2
  refine ⟨hstart, ?_⟩
  have hσ : ENNReal.ofReal ((regenSigma ν k).toReal) = regenSigma ν k :=
    ENNReal.ofReal_toReal hk.ne
  have has : (regenSigma ν k).toReal ≤ s := by
    have := ENNReal.ofReal_le_ofReal_iff hs0 |>.1 (hσ ▸ h1)
    exact this
  unfold IsRelaxedTime
  rw [hstart]
  refine isRelaxedTimeWrt_shift has fun u hu hus => ?_
  refine regenWalk_add_sigma hk hu ?_
  have hadd : ENNReal.ofReal ((regenSigma ν k).toReal + u) ≤ ENNReal.ofReal s :=
    ENNReal.ofReal_le_ofReal (by linarith)
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hu, hσ] at hadd
  have := lt_of_le_of_lt hadd h2
  rw [regenSigma_succ] at this
  exact (ENNReal.add_lt_add_iff_left hk.ne).1 this

/-- The pieces are cyclic paths (c): restart of piece `k` at cyclic integer times. -/
theorem es6_pieces_c (hν : ∀ k, Good (ν k)) (k : ℕ) {x : ℝ} (hx : x ∈ cycIntTimes β) {u : ℝ}
    (hu : 0 ≤ u) :
    cycWalk (ν k) 0 0 (x + u) =
      cycWalk (ν k) (cycWalk (ν k) 0 0 x) (cycIntPhase β x) u :=
  cycWalk_restart_cycIntTimes (hν k) hx.1 hu

end ElboimSly.Paper
