/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.RegenWalk
public import ElboimSly.Frozen.Defs.RegenCount
public import ElboimSly.Foundations.Cyclic.CycRegenEnv
public import Mathlib

/-!
# Deterministic part of the geometric domination of regenerations

Geometric domination of regenerations. Properties of the regeneration times `σ_i = regenSigma ν i` and
counts `𝔑_t = regenCount ν t` of regenerated cyclic walk (`{𝔑_t ≥ k} = {σ_k ≤ t}`), and the pigeonhole step
of (b): if `∑_{j<k} τ_j ≤ t`, then at least `k - ⌊t/T⌋` of the `τ_j` are `≤ T`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] (ν : ℕ → Measure (RingSpace d β))

omit [Fact (0 < β)] in
theorem regenSigma_zero : ElboimSly.regenSigma ν 0 = 0 := by simp [ElboimSly.regenSigma]

omit [Fact (0 < β)] in
theorem regenSigma_succ (i : ℕ) :
    ElboimSly.regenSigma ν (i + 1) = ElboimSly.regenSigma ν i + ElboimSly.cycTreg (ν i) := by
  simp [ElboimSly.regenSigma, Finset.sum_range_succ]

omit [Fact (0 < β)] in
theorem regenSigma_mono : Monotone (ElboimSly.regenSigma ν) :=
  monotone_nat_of_le_succ fun i => by rw [regenSigma_succ]; exact le_self_add

theorem regenSigma_ge (i : ℕ) : (i : ℝ≥0∞) * ENNReal.ofReal β ≤ ElboimSly.regenSigma ν i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [regenSigma_succ, Nat.cast_succ, add_mul, one_mul]
    exact add_le_add ih (regPlan_tau_ge (ν i))

theorem bddAbove_regenSigma_le {t : ℝ} (ht : 0 ≤ t) :
    BddAbove {i : ℕ | ElboimSly.regenSigma ν i ≤ ENNReal.ofReal t} := by
  have hβ : 0 < β := Fact.out
  refine ⟨⌈t / β⌉₊, fun i hi => ?_⟩
  have h1 := (regenSigma_ge ν i).trans hi
  have h2 : ((i : ℝ) * β) ≤ t := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_le_ofReal_iff ht] at h1
    exact h1
  have h3 : (i : ℝ) ≤ t / β := by rw [le_div_iff₀ hβ]; exact h2
  exact_mod_cast h3.trans (Nat.le_ceil _)

/-- `{𝔑_t ≥ k} = {σ_k ≤ t}`. -/
theorem le_regenCount_iff {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    k ≤ ElboimSly.regenCount ν t ↔ ElboimSly.regenSigma ν k ≤ ENNReal.ofReal t := by
  have hne : {i : ℕ | ElboimSly.regenSigma ν i ≤ ENNReal.ofReal t}.Nonempty :=
    ⟨0, by simp [regenSigma_zero]⟩
  have hb := bddAbove_regenSigma_le ν ht
  constructor
  · intro h
    have hm := Nat.sSup_mem hne hb
    exact (regenSigma_mono ν h).trans hm
  · intro h
    exact le_csSup hb h

theorem regenCount_eq {t : ℝ} (ht : 0 ≤ t) {m : ℕ}
    (h1 : ElboimSly.regenSigma ν m ≤ ENNReal.ofReal t)
    (h2 : ENNReal.ofReal t < ElboimSly.regenSigma ν (m + 1)) : ElboimSly.regenCount ν t = m := by
  refine le_antisymm ?_ ((le_regenCount_iff ν ht m).2 h1)
  by_contra h
  exact absurd ((le_regenCount_iff ν ht (m + 1)).1 (not_le.1 h)) (not_le.2 h2)

/-- Pigeonhole step: if `∑_{j<k} τ_j ≤ t` then all but at most `⌊t/T⌋` of the `τ_j` are `≤ T`. -/
theorem exists_subset_short (τ : ℕ → ℝ≥0∞) {k : ℕ} {t T : ℝ} (hT : 0 < T) (_ht : 0 ≤ t)
    (hs : ∑ j ∈ Finset.range k, τ j ≤ ENNReal.ofReal t) (hak : ⌊t / T⌋₊ ≤ k) :
    ∃ J ∈ Finset.powersetCard (k - ⌊t / T⌋₊) (Finset.range k), ∀ j ∈ J, τ j ≤ ENNReal.ofReal T := by
  classical
  set Λ := (Finset.range k).filter (fun j => ENNReal.ofReal T < τ j) with hΛ
  have hcard : Λ.card ≤ ⌊t / T⌋₊ := by
    rcases Λ.eq_empty_or_nonempty with he | hne
    · rw [he]; simp
    · apply Nat.le_floor
      have h1 : ∑ _j ∈ Λ, ENNReal.ofReal T < ∑ j ∈ Λ, τ j :=
        ENNReal.sum_lt_sum_of_nonempty hne fun j hj => (Finset.mem_filter.1 hj).2
      have h2 : ∑ j ∈ Λ, τ j ≤ ∑ j ∈ Finset.range k, τ j :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      rw [Finset.sum_const, nsmul_eq_mul] at h1
      have h3 := h1.trans_le (h2.trans hs)
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at h3
      rw [le_div_iff₀ hT]
      exact h3.le
  have hcc : (Finset.range k \ Λ).card = k - Λ.card := by
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_range]
  obtain ⟨J, hJ, hJc⟩ := Finset.exists_subset_card_eq
    (s := Finset.range k \ Λ) (n := k - ⌊t / T⌋₊) (by rw [hcc]; omega)
  refine ⟨J, Finset.mem_powersetCard.2 ⟨hJ.trans Finset.sdiff_subset, hJc⟩, fun j hj => ?_⟩
  have := Finset.mem_sdiff.1 (hJ hj)
  by_contra hcon
  exact this.2 (Finset.mem_filter.2 ⟨this.1, not_le.1 hcon⟩)

end ElboimSly.Cyclic

end
