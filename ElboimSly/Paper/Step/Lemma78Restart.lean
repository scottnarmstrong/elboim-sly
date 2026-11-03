/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.PiecesClosing
public import ElboimSly.Paper.Heavy.BadTransfer
public import ElboimSly.Paper.Step.Lemma78Setting2
public import Mathlib

/-!
# Restart of `W_{y,q}` at a time `x` with `q + x` an integer cyclic time

Restriction, restart, periodicity (b, c), as used in discovered bad blocks for two walks (ii): for `y ∈ ℤ^d`, `q ∈ ℝ`,
`x, u ≥ 0`, `W_{y,q}(x + u) = W_{W_{y,q}(x), q(q + x)}(u)` with `q(t) = t - β ⌊t/β⌋`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Heavy ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- Restart at a time `x ≥ 0` of the walk `W_{y,q}`, with the phase of `q + x`. -/
theorem cycWalk_restart_phase (hν : Good ν) (y : Fin d → ℤ) (q : ℝ) {x : ℝ} (hx : 0 ≤ x) {u : ℝ}
    (hu : 0 ≤ u) :
    cycWalk ν y q (x + u) = cycWalk ν (cycWalk ν y q x) (cycIntPhase β (q + x)) u := by
  set ℓ : ℤ := ⌊(q + x) / β⌋ with hℓ
  have hq : cycIntPhase β (q + x) = q + x - ℓ * β := by
    unfold cycIntPhase; rw [hℓ]; ring
  rw [cycWalk_of_nonneg hν y q (by linarith), cycWalk_of_nonneg hν y q hx,
    cycWalk_of_nonneg hν _ _ hu]
  have h1 := fwdTraj_restart hν y (a := q) (c := q + x) (by linarith) (t := q + (x + u))
    (by linarith)
  rw [h1]
  have h2 := fwdTraj_add_zsmul hν (fwdTraj hν y q (q + x)) (cycIntPhase β (q + x)) ℓ
    (t := cycIntPhase β (q + x) + u) (by linarith)
  rw [hq] at h2 ⊢
  have e1 : q + x - ℓ * β + ℓ * β = q + x := by ring
  have e2 : q + x - ℓ * β + u + ℓ * β = q + (x + u) := by ring
  rw [e1, e2] at h2
  exact h2

/-- `W_{y,q}` closing from the restart data at `x` gives `SegClosed` for `W_{y,q}`. -/
theorem segClosed_of_cycClosesBy_phase (hν : Good ν) (y : Fin d → ℤ) (q : ℝ) {x : ℝ} (hx : 0 ≤ x)
    {tk : ℝ} (h : cycClosesBy ν (cycWalk ν y q x) (cycIntPhase β (q + x)) tk) :
    SegClosed β tk (fun s : ℝ => cycWalk ν y q s) x := by
  obtain ⟨k, hk1, hk2, hk3⟩ := h
  have hβ : 0 < β := Fact.out
  refine ⟨k * β, by positivity, hk2, ⟨k, by simp⟩, ?_⟩
  show cycWalk ν y q (x + k * β) = cycWalk ν y q x
  rw [cycWalk_restart_phase hν y q hx (by positivity)]
  exact hk3

/-- Discovered bad blocks for two walks (ii): a cross-bad block is not good for `ν` (failure of (GB3) at
`(W₁ a, W₂ b, q(a), q(q + b))`). -/
theorem not_heavyBlockGood_of_crossBad (hν : Good ν) {t₀ : ℝ} {n : ℕ} {ι : Fin d → ℤ} {t q T : ℝ}
    {u : Fin d → ℤ}
    (hbad : Step78CrossBad d β t₀ n q T (fun s : ℝ => cycWalk ν 0 0 s)
      (fun s : ℝ => cycWalk ν u q s) ι t) :
    ¬ HeavyBlockGood d β t₀ n ν ι := by
  intro hgood
  unfold Step78CrossBad at hbad
  unfold HeavyBlockGood at hgood
  dsimp only at hbad hgood
  obtain ⟨a, ha, b, hb, -, -, h1, h2, h3, h4, h5, h6⟩ := hbad
  obtain ⟨q₁, hq₁, hq₁0, hq₁β⟩ := cycIntPhase_mem ha
  obtain ⟨q₂, hq₂, hq₂0, hq₂β⟩ := cycIntPhase_mem hb.2
  have hb0 : 0 ≤ b := hb.1
  have hΩ : cycOmega ν (cycWalk ν 0 0 a) (cycWalk ν u q b) q₁ q₂ (heavyTkPrime d t₀ n) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s₁, s₂, hs₁, hs₂, ⟨m, hm⟩, hw⟩
      apply h5
      refine ⟨s₁, hs₁, s₂, hs₂, ?_, ?_⟩
      · show cycWalk ν 0 0 (a + s₁) = cycWalk ν u q (b + s₂)
        rw [restart_eq hν ha hs₁.1, cycWalk_restart_phase hν u q hb0 hs₂.1, hq₁, hq₂]; exact hw
      · refine ⟨⌊a / β⌋ - ⌊(q + b) / β⌋ + m, ?_⟩
        have e1 : a = β * ⌊a / β⌋ + q₁ := by rw [← hq₁]; unfold cycIntPhase; ring
        have e2 : q + b = β * ⌊(q + b) / β⌋ + q₂ := by rw [← hq₂]; unfold cycIntPhase; ring
        push_cast
        nlinarith
    · intro hc
      apply h3
      rw [← hq₁] at hc
      exact segClosed_of_cycClosesBy hν ha hc
    · intro hc
      apply h4
      rw [← hq₂] at hc
      exact segClosed_of_cycClosesBy_phase hν u q hb0 hc
  have := (hgood _ h1 _ h2 q₁ q₂ hq₁0 hq₁β hq₂0 hq₂β).2.2 hΩ
  apply absurd this (not_lt.2 (le_of_le_of_eq h6 ?_))
  congr 1
  ext s₂
  simp only [step78CrossProx, mem_ofPred_eq]
  refine and_congr_right fun hs₂ => exists_congr fun s₁ => and_congr_right fun hs₁ => ?_
  rw [restart_eq hν ha hs₁.1, cycWalk_restart_phase hν u q hb0 hs₂.1, hq₁, hq₂]

end ElboimSly.Paper.Step

end
