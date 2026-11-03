/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenPiece
public import Mathlib

/-!
# Shifting the sequence of pieces of the regenerated walk

ES22 Lemma 2.1 (c), "Case `L = 0`": removing the first `k` pieces of the
regenerated walk shifts it by `σ_k` (`regenWalk_shift`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] (ν : ℕ → Measure (RingSpace d β))

omit [Fact (0 < β)] in
theorem regenSigma_shift (k i : ℕ) :
    ElboimSly.regenSigma ν (k + i) =
      ElboimSly.regenSigma ν k + ElboimSly.regenSigma (fun j => ν (k + j)) i := by
  unfold ElboimSly.regenSigma
  rw [Finset.sum_range_add]

theorem regenCount_shift (k : ℕ) (hk : ElboimSly.regenSigma ν k < ⊤) {s : ℝ} (hs : 0 ≤ s) :
    ElboimSly.regenCount ν ((ElboimSly.regenSigma ν k).toReal + s) =
      k + ElboimSly.regenCount (fun j => ν (k + j)) s := by
  set a := (ElboimSly.regenSigma ν k).toReal with ha
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hσ : ENNReal.ofReal a = ElboimSly.regenSigma ν k := ENNReal.ofReal_toReal hk.ne
  have hau : 0 ≤ a + s := by linarith
  set ν' : ℕ → Measure (RingSpace d β) := fun j => ν (k + j) with hν'
  set c' := ElboimSly.regenCount ν' s with hc'
  -- the characterisation `σ_{k+i} ≤ a + s ↔ σ'_i ≤ s`
  have key : ∀ i, ElboimSly.regenSigma ν (k + i) ≤ ENNReal.ofReal (a + s) ↔
      ElboimSly.regenSigma ν' i ≤ ENNReal.ofReal s := by
    intro i
    rw [regenSigma_shift, ENNReal.ofReal_add ha0 hs, hσ]
    exact ENNReal.add_le_add_iff_left hk.ne
  apply le_antisymm
  · -- `count ≤ k + c'`
    set m := ElboimSly.regenCount ν (a + s) with hm
    have hmle : ElboimSly.regenSigma ν m ≤ ENNReal.ofReal (a + s) :=
      (le_regenCount_iff ν hau m).1 le_rfl
    have hkm : k ≤ m := by
      refine (le_regenCount_iff ν hau k).2 ?_
      rw [← hσ]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_le hkm
    rw [hi] at hmle ⊢
    have := (key i).1 hmle
    have : i ≤ c' := (le_regenCount_iff ν' hs i).2 this
    omega
  · -- `k + c' ≤ count`
    refine (le_regenCount_iff ν hau _).2 ((key c').2 ?_)
    exact (le_regenCount_iff ν' hs c').1 le_rfl

/-- Removing the first `k` pieces of the regenerated walk shifts it by `σ_k`. -/
theorem regenWalk_shift (k : ℕ) (hk : ElboimSly.regenSigma ν k < ⊤) {s : ℝ} (hs : 0 ≤ s) :
    ElboimSly.regenWalk (fun j => ν (k + j)) s =
      ElboimSly.regenWalk ν ((ElboimSly.regenSigma ν k).toReal + s) := by
  set a := (ElboimSly.regenSigma ν k).toReal with ha
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  set ν' : ℕ → Measure (RingSpace d β) := fun j => ν (k + j) with hν'
  set c' := ElboimSly.regenCount ν' s with hc'
  have hcount := regenCount_shift ν k hk hs
  have hle : ElboimSly.regenSigma ν' c' ≤ ENNReal.ofReal s :=
    (le_regenCount_iff ν' hs c').1 le_rfl
  have hlt : ElboimSly.regenSigma ν' c' < ⊤ := hle.trans_lt ENNReal.ofReal_lt_top
  have hst : ElboimSly.regenStart ν (a + s) = a + ElboimSly.regenStart ν' s := by
    unfold ElboimSly.regenStart
    rw [hcount, regenSigma_shift, ENNReal.toReal_add hk.ne hlt.ne]
  unfold ElboimSly.regenWalk
  rw [hcount, hst]
  congr 1
  ring

end ElboimSly.Cyclic

end
