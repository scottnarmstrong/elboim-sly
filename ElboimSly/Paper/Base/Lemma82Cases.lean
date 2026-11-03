/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.Lemma82Far
public import ElboimSly.Paper.Base.Lemma82Splice
public import ElboimSly.Frozen.Defs.CycMerges
public import ElboimSly.Frozen.Defs.CycClosesBy
public import ElboimSly.Frozen.Defs.CycOmega
public import Mathlib

/-!
# Lemma 8.2: the reductions of Cases A and C

ES22 Lemma 8.2, "Case A" and "Case C".

For a good environment, `pairSet` is the set `𝔓_n` of the written proof.  In Case A (`q ≤ t'`) the
second walk is a time-shifted walk from the random point `v = η_{u₂,q₁+q}(q₁)` started at time
`q₁`; in Case C (`q ≥ β - t'`) the first walk is a time-shifted walk started from
`w = η_{u₁,q₁+q}(q₁+q)`... at the later time, so the roles of the walks are exchanged.  In both
cases, on the non-merging event and on the far-point event, either the set `𝔓_n` is empty or
it is contained, up to a translation, in the contact set of a pair of walks from a common time,
whose starting points differ and are at distance `< 4ⁿ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper.Base

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The set `𝔓_n = {s₂ ∈ [0,t'] : ∃ s₁ ∈ [0,t'], ‖W₁(s₁) - W₂(s₂)‖ ≤ ρ}`. -/
def lemPairSet (ν : Measure (RingSpace d β)) (u₁ u₂ : Fin d → ℤ) (q₁ q₂ t' ρ : ℝ) : Set ℝ :=
  {s₂ | s₂ ∈ Icc 0 t' ∧ ∃ s₁ ∈ Icc (0 : ℝ) t',
    ‖ElboimSly.cycWalk ν u₁ q₁ s₁ - ElboimSly.cycWalk ν u₂ q₂ s₂‖ ≤ ρ}

theorem cycWalk_eq_trajProc_real {ν : Measure (RingSpace d β)} (hν : Good ν) (u : Fin d → ℤ)
    (q : ℝ) {s : ℝ} (hs : 0 ≤ s) : ElboimSly.cycWalk ν u q s = trajProc ν u q s.toNNReal := by
  rw [← cycWalk_eq_trajProc hν, Real.coe_toNNReal _ hs]

theorem toNNReal_le_of_le {s t : ℝ} (h : s ≤ t) : s.toNNReal ≤ t.toNNReal :=
  Real.toNNReal_le_toNNReal h

/-- **Case A**: `q ≤ t'`. -/
theorem caseA_exists {ν : Measure (RingSpace d β)} (hν : Good ν) {n : ℕ} {u₁ u₂ : Fin d → ℤ}
    {q q₁ q₂ t' m : ℝ} (hm : 0 < m) (hq0 : 0 ≤ q) (hqt : q ≤ t') {k : ℤ}
    (hq₂ : q₂ = q₁ + q + k * β) (hmerge : ¬ cycMerges ν u₁ u₂ q₁ q₂ t')
    (hfar : farGood ν u₁ q₁ n (2 * t').toNNReal)
    (hvol : ENNReal.ofReal m ≤ volume (lemPairSet ν u₁ u₂ q₁ q₂ t' ((19 / 10 : ℝ) ^ n))) :
    ∃ b : Fin d → ℤ, b ≠ u₁ ∧ ‖b - u₁‖ < (4 : ℝ) ^ n ∧
      ENNReal.ofReal m ≤ volume (cycContactSet ν u₁ b q₁ (2 * t') ((19 / 10 : ℝ) ^ n)) := by
  have ht'0 : 0 ≤ t' := hq0.trans hqt
  set v := cycWalk ν u₂ (q₁ + q) (q₁ - (q₁ + q)) with hv
  have hW2 : ∀ s : ℝ, 0 ≤ s → cycWalk ν u₂ q₂ s = cycWalk ν v q₁ (q + s) := by
    intro s hs
    rw [hq₂, cycWalk_add_zsmul hν u₂ (q₁ + q) k hs]
    have := cycWalk_splice hν u₂ (c := q₁) (c' := q₁ + q) (by linarith) hs
    rw [show q₁ + q - q₁ + s = q + s by ring] at this
    exact this.symm
  have hne : v ≠ u₁ := by
    intro hvu
    apply hmerge
    refine ⟨q, 0, ⟨hq0, hqt⟩, ⟨le_rfl, ht'0⟩, ⟨-k, ?_⟩, ?_⟩
    · rw [hq₂]; push_cast; try ring
    · rw [hW2 0 le_rfl, add_zero, ← hvu]
  by_cases hfarv : (4 : ℝ) ^ n ≤ ‖v - u₁‖
  · exfalso
    have hempty : lemPairSet ν u₁ u₂ q₁ q₂ t' ((19 / 10 : ℝ) ^ n) = ∅ := by
      refine eq_empty_of_forall_notMem fun s₂ ⟨⟨hs20, hs2t⟩, s₁, ⟨hs10, hs1t⟩, h⟩ => ?_
      have h1 := hfar (v - u₁) hfarv s₁.toNNReal (q + s₂).toNNReal
        (toNNReal_le_of_le (show s₁ ≤ 2 * t' by linarith))
        (toNNReal_le_of_le (show q + s₂ ≤ 2 * t' by linarith))
      rw [add_sub_cancel, norm_sub_rev] at h1
      rw [hW2 s₂ hs20, cycWalk_eq_trajProc_real hν u₁ q₁ hs10,
        cycWalk_eq_trajProc_real hν v q₁ (by linarith : 0 ≤ q + s₂)] at h
      have h2 : (1.9 : ℝ) ^ n = (19 / 10 : ℝ) ^ n := by norm_num
      rw [h2] at h1
      exact absurd h (not_le.2 h1)
    rw [hempty, measure_empty] at hvol
    exact absurd hvol (not_le.2 (ENNReal.ofReal_pos.2 hm))
  · refine ⟨v, hne, not_le.1 hfarv, hvol.trans ?_⟩
    calc volume (lemPairSet ν u₁ u₂ q₁ q₂ t' ((19 / 10 : ℝ) ^ n))
        ≤ volume ((fun x : ℝ => x + q) ⁻¹' cycContactSet ν u₁ v q₁ (2 * t') ((19 / 10 : ℝ) ^ n)) := by
          refine measure_mono ?_
          rintro s₂ ⟨⟨hs20, hs2t⟩, s₁, ⟨hs10, hs1t⟩, h⟩
          refine ⟨⟨by linarith, by linarith⟩, s₁, ⟨hs10, by linarith⟩, ?_⟩
          rw [hW2 s₂ hs20] at h
          show ‖cycWalk ν v q₁ (s₂ + q) - cycWalk ν u₁ q₁ s₁‖ ≤ (19 / 10 : ℝ) ^ n
          rw [add_comm s₂ q, norm_sub_rev]
          exact h
      _ = volume (cycContactSet ν u₁ v q₁ (2 * t') ((19 / 10 : ℝ) ^ n)) :=
          measure_preimage_add_right volume q _

/-- **Case C**: `q ≥ β - t'`; the roles of the two walks are exchanged. -/
theorem caseC_exists {ν : Measure (RingSpace d β)} (hν : Good ν) {n : ℕ} {u₁ u₂ : Fin d → ℤ}
    {q q₁ q₂ t' m : ℝ} (hm : 0 < m) (hq1 : β - t' ≤ q) (hq2 : q < β) {k : ℤ}
    (hq₂ : q₂ = q₁ + q + k * β) (hmerge : ¬ cycMerges ν u₁ u₂ q₁ q₂ t')
    (hfar : farGood ν u₂ (q₁ + q) n (2 * t').toNNReal)
    (hvol : ENNReal.ofReal m ≤ volume (lemPairSet ν u₁ u₂ q₁ q₂ t' ((19 / 10 : ℝ) ^ n))) :
    ∃ a : Fin d → ℤ, a ≠ u₂ ∧ ‖a - u₂‖ < (4 : ℝ) ^ n ∧
      ENNReal.ofReal m ≤ volume (cycContactSet ν a u₂ (q₁ + q) (2 * t') ((19 / 10 : ℝ) ^ n)) := by
  have hβ : 0 < β := Fact.out
  set q' : ℝ := β - q with hq'
  have hq'0 : 0 < q' := by rw [hq']; linarith
  have hq't : q' ≤ t' := by rw [hq']; linarith
  have ht'0 : 0 ≤ t' := hq'0.le.trans hq't
  set w := cycWalk ν u₁ (q₁ + q + q') (q₁ + q - (q₁ + q + q')) with hw
  have hW2 : ∀ s : ℝ, 0 ≤ s → cycWalk ν u₂ q₂ s = cycWalk ν u₂ (q₁ + q) s := by
    intro s hs
    rw [hq₂, cycWalk_add_zsmul hν u₂ (q₁ + q) k hs]
  have hW1 : ∀ s : ℝ, 0 ≤ s → cycWalk ν u₁ q₁ s = cycWalk ν w (q₁ + q) (q' + s) := by
    intro s hs
    have e1 := cycWalk_add_zsmul hν u₁ (q₁ + q + q') (-1) hs
    have e2 : q₁ + q + q' + ((-1 : ℤ) : ℝ) * β = q₁ := by rw [hq']; push_cast; ring
    rw [e2] at e1
    rw [e1]
    have := cycWalk_splice hν u₁ (c := q₁ + q) (c' := q₁ + q + q') (by linarith) hs
    rw [show q₁ + q + q' - (q₁ + q) + s = q' + s by ring] at this
    exact this.symm
  have hne : w ≠ u₂ := by
    intro hwu
    apply hmerge
    refine ⟨0, q', ⟨le_rfl, ht'0⟩, ⟨hq'0.le, hq't⟩, ⟨-1 - k, ?_⟩, ?_⟩
    · rw [hq₂, hq']; push_cast; ring
    · rw [hW2 q' hq'0.le, hW1 0 le_rfl, add_zero, hwu]
  by_cases hfarv : (4 : ℝ) ^ n ≤ ‖w - u₂‖
  · exfalso
    have hempty : lemPairSet ν u₁ u₂ q₁ q₂ t' ((19 / 10 : ℝ) ^ n) = ∅ := by
      refine eq_empty_of_forall_notMem fun s₂ ⟨⟨hs20, hs2t⟩, s₁, ⟨hs10, hs1t⟩, h⟩ => ?_
      have h1 := hfar (w - u₂) hfarv s₂.toNNReal (q' + s₁).toNNReal
        (toNNReal_le_of_le (show s₂ ≤ 2 * t' by linarith))
        (toNNReal_le_of_le (show q' + s₁ ≤ 2 * t' by linarith))
      rw [add_sub_cancel] at h1
      rw [hW2 s₂ hs20, hW1 s₁ hs10, cycWalk_eq_trajProc_real hν w _ (by linarith : 0 ≤ q' + s₁),
        cycWalk_eq_trajProc_real hν u₂ _ hs20] at h
      have h2 : (1.9 : ℝ) ^ n = (19 / 10 : ℝ) ^ n := by norm_num
      rw [h2] at h1
      exact absurd h (not_le.2 h1)
    rw [hempty, measure_empty] at hvol
    exact absurd hvol (not_le.2 (ENNReal.ofReal_pos.2 hm))
  · refine ⟨w, hne, not_le.1 hfarv, hvol.trans (measure_mono ?_)⟩
    rintro s₂ ⟨⟨hs20, hs2t⟩, s₁, ⟨hs10, hs1t⟩, h⟩
    refine ⟨⟨hs20, by linarith⟩, q' + s₁, ⟨by linarith, by linarith⟩, ?_⟩
    rw [hW2 s₂ hs20, hW1 s₁ hs10, norm_sub_rev] at h
    exact h

end ElboimSly.Paper

end
