/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Pieces
public import ElboimSly.Paper.Heavy.GoodLocalLoc
public import ElboimSly.Paper.Roots.RegenCopies
public import ElboimSly.Paper.Induction.RelaxedMeasRegen
public import Mathlib

/-!
# The first piece of the regenerated walk and the cyclic walk of the first copy

Probability that a block is bad, proof for (GB1) and (GB2), using the pieces are cyclic paths and
Closing (b).

For good copies `ν k` and a time `t ≥ 0`:
* `cycClosesBy_zero_iff`: `W_{0,0}^{ν 0}` closes by `t` iff `t_reg ≤ t`;
* `relaxedSet_regen_eq`: if `t < t_reg`, relaxed times of the regenerated walk in `[0, t]` are those
  of the first piece, relative to start `0`;
* `exists_regenWalk_of_cycWalk`: a large value of the first cyclic walk on `[0, t]` yields a large
  value of the regenerated walk on `[0, t]`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem cycClosesBy_zero_iff {ν : Measure (RingSpace d β)} {t : ℝ} (ht : 0 ≤ t) :
    cycClosesBy ν 0 0 t ↔ cycTreg ν ≤ ENNReal.ofReal t := by
  have hβ : 0 < β := Fact.out
  constructor
  · rintro ⟨m, hm1, hm2, h0⟩
    exact (cycTreg_le hm1 h0).trans (ENNReal.ofReal_le_ofReal hm2)
  · intro h
    have hlt : cycTreg ν < ⊤ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
    obtain ⟨n, hn, h0, he⟩ := exists_cycTreg_eq hlt
    rw [he, ENNReal.ofReal_le_ofReal_iff ht] at h
    exact ⟨n, hn, h, h0⟩

theorem relaxedSet_regen_eq {ν : ℕ → Measure (RingSpace d β)} (hν : ∀ k, Good (ν k)) {t : ℝ}
    (ht : ENNReal.ofReal t < cycTreg (ν 0)) :
    {s : ℝ | s ∈ Icc 0 t ∧ IsRelaxedTime ν s} =
      {s : ℝ | s ∈ Icc 0 t ∧ IsRelaxedTimeWrt β (fun r => cycWalk (ν 0) 0 0 r) 0 s} := by
  ext s
  simp only [mem_ofPred_eq]
  refine and_congr_right fun hs => ?_
  have h1 : regenSigma ν 0 ≤ ENNReal.ofReal s := by rw [Roots.regenSigma_zero]; exact zero_le
  have h2 : ENNReal.ofReal s < regenSigma ν (0 + 1) := by
    rw [zero_add, Roots.regenSigma_one]
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hs.2) ht
  have := (es6_pieces_b_relaxed hν (k := 0) (by rw [Roots.regenSigma_zero]; exact ENNReal.zero_lt_top)
    hs.1 h1 h2).2
  simpa [Roots.regenSigma_zero] using this

theorem exists_cycWalk_eq_le_treg {ν : Measure (RingSpace d β)} (hν : Good ν) {s : ℝ}
    (hs : 0 ≤ s) : ∃ s' ∈ Icc 0 s, ENNReal.ofReal s' ≤ cycTreg ν ∧
      cycWalk ν 0 0 s = cycWalk ν 0 0 s' := by
  by_cases htop : cycTreg ν = ⊤
  · exact ⟨s, ⟨hs, le_rfl⟩, by simp [htop], rfl⟩
  have hlt : cycTreg ν < ⊤ := lt_top_iff_ne_top.2 htop
  set T := (cycTreg ν).toReal with hT
  have hTpos : 0 < T := by
    have := Roots.ofReal_le_cycTreg ν
    have hβ : 0 < β := Fact.out
    have h2 : ENNReal.ofReal β ≤ cycTreg ν := this
    have := ENNReal.toReal_mono htop h2
    rw [ENNReal.toReal_ofReal hβ.le] at this
    linarith
  have key : ∀ m : ℕ, ∀ s : ℝ, 0 ≤ s → s < ((m : ℝ) + 1) * T → ∃ s' ∈ Icc 0 s,
      ENNReal.ofReal s' ≤ cycTreg ν ∧ cycWalk ν 0 0 s = cycWalk ν 0 0 s' := by
    intro m
    induction m with
    | zero =>
      intro s hs0 hs
      refine ⟨s, ⟨hs0, le_rfl⟩, ?_, rfl⟩
      rw [← ENNReal.ofReal_toReal htop]
      exact ENNReal.ofReal_le_ofReal (by simpa using hs.le)
    | succ m ih =>
      intro s hs0 hs
      by_cases hsT : s < T
      · refine ⟨s, ⟨hs0, le_rfl⟩, ?_, rfl⟩
        rw [← ENNReal.ofReal_toReal htop]
        exact ENNReal.ofReal_le_ofReal hsT.le
      · push Not at hsT
        obtain ⟨s', hs', h1, h2⟩ := ih (s - T) (by linarith) (by push_cast at hs; linarith)
        refine ⟨s', ⟨hs'.1, by linarith [hs'.2]⟩, h1, ?_⟩
        rw [← h2, ← cycWalk_add_treg hν hlt (s - T)]
        congr 1; ring
  obtain ⟨m, hm⟩ := exists_nat_gt (s / T)
  exact key m s hs (by rw [div_lt_iff₀ hTpos] at hm; nlinarith)

theorem exists_regenWalk_of_cycWalk {ν : ℕ → Measure (RingSpace d β)} (hν : ∀ k, Good (ν k))
    {t R : ℝ} {s : ℝ} (hs : s ∈ Icc 0 t) (hR : R < ‖cycWalk (ν 0) 0 0 s‖) :
    ∃ s' ∈ Icc (0 : ℝ) t, R < ‖regenWalk ν s'‖ := by
  obtain ⟨s', hs', hle, he⟩ := exists_cycWalk_eq_le_treg (hν 0) hs.1
  refine ⟨s', ⟨hs'.1, hs'.2.trans hs.2⟩, ?_⟩
  have := es6_pieces_b_walk hν (k := 0) (by rw [Roots.regenSigma_zero]; exact ENNReal.zero_lt_top)
    hs'.1 hle
  rw [Roots.regenSigma_zero] at this
  simp only [ENNReal.toReal_zero, zero_add] at this
  rw [this, ← he]; exact hR

end ElboimSly.Paper.Heavy
