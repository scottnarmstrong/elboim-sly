/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.EscapeSets
public import ElboimSly.Foundations.SRW.KernelOneD
public import Mathlib

/-!
# Monotone upward paths

The event that `N⁺(r) = k` and `N⁻(r) = 0`: the walk increases from `0` to `k` by unit steps.
Used for the small-`L` case of confined point-to-point lower bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

/-- Paths in `[0, k]` on `[0, r]` that end at `k`. -/
def gamUp (k : ℕ) (r : ℝ≥0) : Set (PathSpace 1) :=
  evalForall {v | v 0 = k} {v | 0 ≤ v 0 ∧ v 0 ≤ k} r

theorem prob_gamUp_canonical {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (Dir 1 × ℝ)} (hN : IsPoissonPointProcess N (clockIntensity (Dir 1)) P)
    (k : ℕ) (r : ℝ≥0) :
    po r k * po r 0 ≤ P.real {ω | canonical 1 N ω ∈ gamUp k r} := by
  have := hN.isProbabilityMeasure
  set A := cntN N r ((0 : Fin 1), true) with hA
  set B := cntN N r ((0 : Fin 1), false) with hB
  have hind : IndepFun A B P := (iIndepFun_cntN hN r).indepFun (by simp)
  have hAm := measurable_cntN hN r ((0 : Fin 1), true)
  have hBm := measurable_cntN hN r ((0 : Fin 1), false)
  have hsub : {ω | A ω = k} ∩ {ω | B ω = 0} ≤ᵐ[P] {ω | canonical 1 N ω ∈ gamUp k r} := by
    filter_upwards [ae_good hN] with ω hg h
    obtain ⟨h1, h2⟩ := h
    simp only [mem_ofPred_eq, hA, hB, cntN] at h1 h2
    have hcn : ∀ (v : Dir 1) (t : ℝ) (n : ℕ), natOf (cnt (N ω) v t) = n →
        cnt (N ω) v t = n := by
      intro v t n hn
      obtain ⟨m, hm⟩ := good_cnt hg v t
      rw [hm] at hn ⊢
      simp only [natOf, ENNReal.toReal_natCast, Nat.floor_natCast] at hn
      rw [hn]
    have hmono : ∀ (v : Dir 1) (s : ℝ≥0), s ≤ r → cnt (N ω) v s ≤ cnt (N ω) v r := by
      intro v s hs
      unfold cnt
      refine measure_mono (prod_mono subset_rfl (Ioc_subset_Ioc_right ?_))
      exact_mod_cast hs
    have hz : cnt (N ω) ((0 : Fin 1), false) r = 0 := by
      have := hcn _ _ 0 h2
      simpa using this
    have hk : cnt (N ω) ((0 : Fin 1), true) r = k := hcn _ _ k h1
    show canonical 1 N ω ∈ evalForall _ _ r
    refine ⟨?_, fun s hs => ?_⟩
    · show (canonical 1 N ω r) 0 = k
      show walk 1 (N ω) (r : ℝ) 0 = k
      rw [walk_apply hg]
      rw [h1, h2]; simp
    · show 0 ≤ (canonical 1 N ω s) 0 ∧ (canonical 1 N ω s) 0 ≤ k
      show 0 ≤ walk 1 (N ω) (s : ℝ) 0 ∧ walk 1 (N ω) (s : ℝ) 0 ≤ k
      rw [walk_apply hg]
      have hf : cnt (N ω) ((0 : Fin 1), false) s = 0 := by
        have := hmono ((0 : Fin 1), false) s hs
        rw [hz] at this
        exact le_antisymm this bot_le
      have ht : cnt (N ω) ((0 : Fin 1), true) s ≤ k := by
        have := hmono ((0 : Fin 1), true) s hs
        rwa [hk] at this
      obtain ⟨m, hm⟩ := good_cnt hg ((0 : Fin 1), true) s
      rw [hm] at ht ⊢
      have hmk : m ≤ k := by exact_mod_cast ht
      rw [hf]
      simp only [natOf, ENNReal.toReal_natCast, Nat.floor_natCast, ENNReal.toReal_zero,
        Nat.floor_zero]
      constructor <;> push_cast <;> omega
  have hprod : P.real ({ω | A ω = k} ∩ {ω | B ω = 0}) =
      P.real {ω | A ω = k} * P.real {ω | B ω = 0} := by
    have := (indepFun_iff_measure_inter_preimage_eq_mul.1 hind) {k} {0}
      (measurableSet_singleton k) (measurableSet_singleton 0)
    simp only [measureReal_def]
    rw [← ENNReal.toReal_mul]
    exact congrArg ENNReal.toReal this
  have hpo : ∀ (v : Dir 1) (n : ℕ), P.real {ω | cntN N r v ω = n} = po r n := by
    intro v n
    have h := map_cntN hN (t := r) r.2 v
    have : P {ω | cntN N r v ω = n} = poissonMeasure ((r : ℝ).toNNReal) {n} := by
      rw [← h, Measure.map_apply (measurable_cntN hN r v) (measurableSet_singleton n)]
      rfl
    rw [measureReal_def, this, poissonMeasure_singleton]
    unfold po
    simp
    try positivity
  have hAv := hpo ((0 : Fin 1), true) k
  have hBv := hpo ((0 : Fin 1), false) 0
  rw [← hA] at hAv
  rw [← hB] at hBv
  have hle : P.real ({ω | A ω = k} ∩ {ω | B ω = 0}) ≤
      P.real {ω | canonical 1 N ω ∈ gamUp k r} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  rw [hprod, hAv, hBv] at hle
  exact hle

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace 1}

theorem isRegSet_gamUp (k : ℕ) (r : ℝ≥0) : IsRegSet (gamUp k r) := isRegSet_evalForall _ _ _

theorem IsSRW.prob_gamUp (hY : IsSRW P Y) (k : ℕ) (r : ℝ≥0) :
    po r k * po r 0 ≤ P.real {ω | Y ω ∈ gamUp k r} := by
  obtain ⟨Ω', mΩ', P', N, hP, hN, -⟩ := exists_isPoissonPointProcess_clockIntensity (Dir 1)
  have hZ := canonical_isSRW hN
  have h := hY.prob_regSet_eq hZ (isRegSet_gamUp k r)
  have := prob_gamUp_canonical hN k r
  simp only [measureReal_def]
  have e : P {ω | Y ω ∈ gamUp k r} = P' {ω | canonical 1 N ω ∈ gamUp k r} := h
  rw [e]
  exact this

end SRW
end ElboimSly
