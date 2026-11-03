/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.GoodBlocks
public import ElboimSly.Paper.Heavy.Pieces
public import ElboimSly.Paper.Heavy.PiecesRegen
public import ElboimSly.Paper.Heavy.Lambda

/-!
# Discovered bad blocks are bad

Discovered bad blocks are bad (ES22 §6).

For a good environment `ν` and the first piece `w = W^ν` (`fun s => cycWalk ν 0 0 s`): if the block
`ℬ_k(ι)` is bad by time `t` for `w` (`BadByTime`), then it is not good for `ν`
(`not_heavyBlockGood_of_badByTime`).  The witnesses are those of `BadByTime`: they satisfy
`w x ∈ N(B, 2^{k+2})` and `x ≤ t` by the definition of `BadByTime`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

theorem cycIntPhase_mem {x : ℝ} (hx : x ∈ cycIntTimes β) :
    ∃ q : ℤ, cycIntPhase β x = q ∧ (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ β := by
  have hβ : 0 < β := Fact.out
  obtain ⟨-, m, hm⟩ := hx
  refine ⟨m, hm, ?_, ?_⟩
  · rw [← hm]
    have : (⌊x / β⌋ : ℝ) ≤ x / β := Int.floor_le _
    rw [le_div_iff₀ hβ] at this
    nlinarith
  · rw [← hm]
    have : x / β < ⌊x / β⌋ + 1 := Int.lt_floor_add_one _
    rw [div_lt_iff₀ hβ] at this
    nlinarith

theorem restart_eq (hν : Good ν) {x : ℝ} (hx : x ∈ cycIntTimes β) {u : ℝ} (hu : 0 ≤ u) :
    cycWalk ν 0 0 (x + u) = cycWalk ν (cycWalk ν 0 0 x) (cycIntPhase β x) u :=
  es6_pieces_c (ν := fun _ => ν) (fun _ => hν) 0 hx hu

theorem segClosed_of_cycClosesBy (hν : Good ν) {x : ℝ} (hx : x ∈ cycIntTimes β) {tk : ℝ}
    (h : cycClosesBy ν (cycWalk ν 0 0 x) (cycIntPhase β x) tk) :
    SegClosed β tk (fun s : ℝ => cycWalk ν 0 0 s) x := by
  obtain ⟨k, hk1, hk2, hk3⟩ := h
  have hβ : 0 < β := Fact.out
  refine ⟨k * β, by positivity, hk2, ⟨k, by simp⟩, ?_⟩
  show cycWalk ν 0 0 (x + k * β) = cycWalk ν 0 0 x
  rw [restart_eq hν hx (by positivity)]
  exact hk3

theorem relaxed_volume_eq (hν : Good ν) {x : ℝ} (hx : x ∈ cycIntTimes β) {tk : ℝ} :
    {u : ℝ | u ∈ Icc 0 tk ∧ IsRelaxedTimeWrt β (fun s : ℝ => cycWalk ν 0 0 s) x (x + u)} =
      {s : ℝ | s ∈ Icc 0 tk ∧
        IsRelaxedTimeWrt β (fun r => cycWalk ν (cycWalk ν 0 0 x) (cycIntPhase β x) r) 0 s} := by
  ext u
  simp only [mem_ofPred_eq]
  refine and_congr_right fun hu => ?_
  have := isRelaxedTimeWrt_shift (β := β) (w := fun s : ℝ => cycWalk ν 0 0 s)
    (w' := fun r => cycWalk ν (cycWalk ν 0 0 x) (cycIntPhase β x) r) (a := x) (t := x + u)
    (by linarith [hu.1]) (fun v hv _ => restart_eq hν hx hv)
  rw [this]
  simp

/-- Discovered bad blocks are bad: a block that is bad by time `t` for the first piece is not
good for the environment. -/
theorem not_heavyBlockGood_of_badByTime (hν : Good ν) {t₀ : ℝ} {n : ℕ} {ι : Fin d → ℤ} {t : ℝ}
    (hbad : BadByTime d β t₀ n (fun s : ℝ => cycWalk ν 0 0 s) ι t) :
    ¬ HeavyBlockGood d β t₀ n ν ι := by
  intro hgood
  unfold BadByTime at hbad
  unfold HeavyBlockGood at hgood
  dsimp only at hbad hgood
  rcases hbad with ⟨x, hx, h1, -, h3, h4⟩ | ⟨x, hx, -, h1, u, hu, h3⟩ |
    ⟨x₁, hx₁, x₂, hx₂, h1, h2, -, -, h5, h6, h7, h8⟩
  · -- (V1)
    obtain ⟨q, hq, hq0, hqβ⟩ := cycIntPhase_mem hx
    have := (hgood _ h1 _ h1 q q hq0 hqβ hq0 hqβ).1
    rw [← hq] at this
    rcases this with hc | hr
    · exact h3 (segClosed_of_cycClosesBy hν hx hc)
    · apply h4
      unfold SegRelaxed
      rwa [relaxed_volume_eq hν hx]
  · -- (V2)
    obtain ⟨q, hq, hq0, hqβ⟩ := cycIntPhase_mem hx
    have := (hgood _ h1 _ h1 q q hq0 hqβ hq0 hqβ).2.1 u ⟨hu.1, hu.2.trans (min_le_left _ _)⟩
    rw [← hq, ← restart_eq hν hx hu.1] at this
    exact absurd h3 (not_lt.2 this)
  · -- (V3)
    obtain ⟨q₁, hq₁, hq₁0, hq₁β⟩ := cycIntPhase_mem hx₁
    obtain ⟨q₂, hq₂, hq₂0, hq₂β⟩ := cycIntPhase_mem hx₂
    have hΩ : cycOmega ν (cycWalk ν 0 0 x₁) (cycWalk ν 0 0 x₂) q₁ q₂ (heavyTkPrime d t₀ n) := by
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨s₁, s₂, hs₁, hs₂, ⟨m, hm⟩, hw⟩
        apply h5
        refine ⟨s₁, s₂, hs₁, hs₂, ?_, ?_⟩
        · show cycWalk ν 0 0 (x₁ + s₁) = cycWalk ν 0 0 (x₂ + s₂)
          rw [restart_eq hν hx₁ hs₁.1, restart_eq hν hx₂ hs₂.1, hq₁, hq₂]; exact hw
        · refine ⟨⌊x₁ / β⌋ - ⌊x₂ / β⌋ + m, ?_⟩
          have e1 : x₁ = β * ⌊x₁ / β⌋ + q₁ := by rw [← hq₁]; unfold cycIntPhase; ring
          have e2 : x₂ = β * ⌊x₂ / β⌋ + q₂ := by rw [← hq₂]; unfold cycIntPhase; ring
          push_cast
          nlinarith
      · intro hc
        apply h6
        rw [← hq₁] at hc
        exact segClosed_of_cycClosesBy hν hx₁ hc
      · intro hc
        apply h7
        rw [← hq₂] at hc
        exact segClosed_of_cycClosesBy hν hx₂ hc
    have := (hgood _ h1 _ h2 q₁ q₂ hq₁0 hq₁β hq₂0 hq₂β).2.2 hΩ
    apply absurd this (not_lt.2 (le_of_le_of_eq h8 ?_))
    congr 1
    ext s₂
    simp only [proxSet, mem_ofPred_eq]
    refine and_congr_right fun hs₂ => exists_congr fun s₁ => and_congr_right fun hs₁ => ?_
    rw [restart_eq hν hx₁ hs₁.1, restart_eq hν hx₂ hs₂.1, hq₁, hq₂]

end ElboimSly.Paper.Heavy
