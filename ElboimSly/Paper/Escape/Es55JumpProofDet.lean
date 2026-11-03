/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenRc
public import ElboimSly.Foundations.Cyclic.CycClosing
public import ElboimSly.Foundations.Concentration.GeometricDet
public import Mathlib

/-!
# The regenerated walk does not jump at a time at which no environment rings

ES22 Lemma 5.5, Step 1 (a jump of the regenerated walk at `t` needs a ring atom at the
cyclic time `[t]`, since regeneration times lie in `βℤ`).

Deterministic part: if no edge of any environment `ν m` rings at the cyclic time `[t]`, `t > 0`,
then `regenWalk ν` is left-constant at `t`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- Left-constancy of the cyclic walk at a time where no edge rings. -/
theorem cycWalk_left_const (hν : Good ν) {s : ℝ} (hs : 0 < s) (hno : ∀ e, ¬ Rings ν e s) :
    ∃ l : ℝ, 0 ≤ l ∧ l < s ∧ ∀ r : ℝ, l < r → r < s →
      ElboimSly.cycWalk ν 0 0 r = ElboimSly.cycWalk ν 0 0 s := by
  have hsp := fwdTrajFn_spec hν (0 : Fin d → ℤ) 0
  have hW : ∀ r : ℝ, 0 ≤ r → ElboimSly.cycWalk ν 0 0 r = fwdTrajFn hν 0 0 r.toNNReal := by
    intro r hr
    rw [cycWalk_of_nonneg hν 0 0 hr]
    simp [fwdTraj, fwdReal]
  have hs' : 0 < s.toNNReal := Real.toNNReal_pos.2 hs
  obtain ⟨z, hz⟩ := hsp.1.2.1 s.toNNReal hs'
  have hsw := hsp.1.2.2.2 s.toNNReal hs' z hz
  have hrg : ((0 : ℝ) + (s.toNNReal : ℝ)) = s := by simp [hs.le]
  have hgz : fwdTrajFn hν 0 0 s.toNNReal = z := by
    refine (hsw.2 ?_)
    rintro ⟨e, -, he⟩
    rw [hrg] at he
    exact hno e he
  obtain ⟨l', hl', hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hs').1 hz
  have hl'R : (l' : ℝ) < s := by
    have : l' < s.toNNReal := hl'
    exact (Real.lt_toNNReal_iff_coe_lt).1 this
  refine ⟨l', l'.2, hl'R, fun r hlr hrs => ?_⟩
  have hr0 : 0 ≤ r := le_trans l'.2 hlr.le
  rw [hW r hr0, hW s hs.le, hgz]
  refine hsub ⟨?_, ?_⟩
  · exact (Real.lt_toNNReal_iff_coe_lt).2 hlr
  · exact (Real.toNNReal_lt_toNNReal_iff hs).2 hrs

variable {ν : ℕ → Measure (RingSpace d β)}

theorem regenSigma_finite_mul (k : ℕ) (h : ElboimSly.regenSigma ν k < ⊤) :
    ∃ i : ℕ, (ElboimSly.regenSigma ν k).toReal = i * β := by
  induction k with
  | zero => exact ⟨0, by simp [regenSigma_zero]⟩
  | succ j ih =>
    rw [regenSigma_succ] at h
    obtain ⟨h1, h2⟩ := ENNReal.add_lt_top.1 h
    obtain ⟨i, hi⟩ := ih h1
    obtain ⟨n, -, -, hn⟩ := exists_cycTreg_eq h2
    refine ⟨i + n, ?_⟩
    rw [regenSigma_succ, ENNReal.toReal_add h1.ne h2.ne, hi, hn,
      ENNReal.toReal_ofReal (by have : 0 < β := Fact.out; positivity)]
    push_cast; ring

/-- Left-constancy of the regenerated walk at `σ_j + u` from that of the cyclic walk of piece `j`. -/
theorem regenWalk_left_const_piece (hg : ∀ j, Good (ν j)) (j : ℕ)
    (hj : ElboimSly.regenSigma ν j < ⊤) {u : ℝ} (hu : 0 < u)
    (hu' : ENNReal.ofReal u ≤ ElboimSly.cycTreg (ν j))
    (hc : ∃ l : ℝ, 0 ≤ l ∧ l < u ∧ ∀ r : ℝ, l < r → r < u →
      ElboimSly.cycWalk (ν j) 0 0 r = ElboimSly.cycWalk (ν j) 0 0 u) :
    ∃ l : ℝ, 0 ≤ l ∧ l < (ElboimSly.regenSigma ν j).toReal + u ∧
      ∀ s : ℝ, l < s → s < (ElboimSly.regenSigma ν j).toReal + u →
        ElboimSly.regenWalk ν s = ElboimSly.regenWalk ν ((ElboimSly.regenSigma ν j).toReal + u) := by
  obtain ⟨l, hl0, hlu, hl⟩ := hc
  set a := (ElboimSly.regenSigma ν j).toReal with ha
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  refine ⟨a + l, by linarith, by linarith, fun s hs1 hs2 => ?_⟩
  have e1 := regenWalk_piece hg j hj (u := s - a) (by linarith)
    (le_trans (ENNReal.ofReal_le_ofReal (by linarith : s - a ≤ u)) hu')
  have e2 := regenWalk_piece hg j hj hu.le hu'
  rw [← ha] at e1 e2
  rw [show a + (s - a) = s by ring] at e1
  rw [e1, e2]
  exact hl _ (by linarith) (by linarith)

/-- **Deterministic no-jump.** If no edge of any environment rings at the cyclic time `[t]`, the
regenerated walk is left-constant at `t > 0`. -/
theorem regenWalk_left_const (hg : ∀ j, Good (ν j)) {t : ℝ} (ht : 0 < t)
    (hno : ∀ m e, ¬ Rings (ν m) e t) :
    ∃ l : ℝ, 0 ≤ l ∧ l < t ∧ ∀ s : ℝ, l < s → s < t →
      ElboimSly.regenWalk ν s = ElboimSly.regenWalk ν t := by
  have ht0 : 0 ≤ t := ht.le
  set k := ElboimSly.regenCount ν t with hk
  have hkfin := regenSigma_count_lt_top ν ht0
  rw [← hk] at hkfin
  have hlt := ofReal_sub_regenStart_lt ν ht0
  rw [← hk] at hlt
  obtain ⟨i, hi⟩ := regenSigma_finite_mul k hkfin
  have ha : ElboimSly.regenStart ν t = i * β := hi
  have hle := regenStart_le ν ht0
  rw [ha] at hle hlt
  rcases hle.lt_or_eq with hlt' | heq
  · -- t strictly inside the piece
    have hs : 0 < t - i * β := by linarith
    have hnr : ∀ e, ¬ Rings (ν k) e (t - i * β) := by
      intro e he
      have := (rings_add_zsmul (ν := ν k) e t (-(i : ℤ))).1 (by
        convert he using 2; push_cast; ring)
      exact hno k e this
    have hc := cycWalk_left_const (hg k) hs hnr
    have := regenWalk_left_const_piece hg k hkfin hs hlt.le hc
    rw [show (ElboimSly.regenSigma ν k).toReal + (t - i * β) = t by rw [hi]; ring] at this
    exact this
  · -- t is a regeneration time `σ_k`, `k ≥ 1`
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, regenSigma_zero] at hi
      have : (i : ℝ) * β = 0 := by rw [← hi]; simp
      linarith
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    rw [hj] at hkfin hi
    rw [regenSigma_succ] at hkfin
    obtain ⟨h1, h2⟩ := ENNReal.add_lt_top.1 hkfin
    obtain ⟨n, hn1, -, hn⟩ := exists_cycTreg_eq h2
    obtain ⟨i', hi'⟩ := regenSigma_finite_mul j h1
    have hβ : 0 < β := Fact.out
    have hu : (ElboimSly.cycTreg (ν j)).toReal = n * β := by
      rw [hn, ENNReal.toReal_ofReal (by positivity)]
    have hu0 : 0 < (ElboimSly.cycTreg (ν j)).toReal := by
      rw [hu]; have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      positivity
    have htt : t = (ElboimSly.regenSigma ν j).toReal + (ElboimSly.cycTreg (ν j)).toReal := by
      have : t = i * β := by linarith
      rw [this, ← hi, Nat.succ_eq_add_one, regenSigma_succ, ENNReal.toReal_add h1.ne h2.ne]
    have hnr : ∀ e, ¬ Rings (ν j) e (ElboimSly.cycTreg (ν j)).toReal := by
      intro e he
      have := (rings_add_zsmul (ν := ν j) e t (-(i' + 0 : ℤ) )).1 (by
        convert he using 2
        rw [htt, hu, hi']; push_cast; ring)
      exact hno j e this
    have hc := cycWalk_left_const (hg j) hu0 hnr
    have := regenWalk_left_const_piece hg j h1 hu0
      (by rw [ENNReal.ofReal_toReal h2.ne]) hc
    rw [← htt] at this
    exact this

end ElboimSly.Paper.Escape
