/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.MarkovChain
public import ElboimSly.Foundations.SRW.Push
public import ElboimSly.Foundations.SRW.FixedCounts
public import Mathlib

/-!
# The events of escape from the boundary

Regular sets of paths, their measurable versions, and the probability of each window event.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- Paths with `β r ∈ K₁` and `β s ∈ K₂` for all `s ≤ r`. -/
def evalForall (K₁ K₂ : Set (Fin d → ℤ)) (r : ℝ≥0) : Set (PathSpace d) :=
  {β | β r ∈ K₁ ∧ ∀ s : ℝ≥0, s ≤ r → β s ∈ K₂}

theorem isRegSet_evalForall (K₁ K₂ : Set (Fin d → ℤ)) (r : ℝ≥0) :
    IsRegSet (evalForall K₁ K₂ r) := by
  have h1 := isVersion_eval (E := Unit) (d := d) (α := fun _ => r)
    (K := {p : Unit × (Fin d → ℤ) | p.2 ∈ K₁}) measurable_const (MeasurableSet.of_discrete)
  have h2 := isVersion_forall_Icc (E := Unit) (d := d) (α := fun _ => 0) (β := fun _ => r)
    (K := {p : Unit × (Fin d → ℤ) | p.2 ∈ K₂}) measurable_const measurable_const
    (MeasurableSet.of_discrete)
  generalize {p : Unit × PathSpace d | (p.1, ev r p.2) ∈ {p : Unit × (Fin d → ℤ) | p.2 ∈ K₁}} = A1
    at h1
  generalize ({p : Unit × PathSpace d | r < 0} ∪
      ({p | (p.1, ev r p.2) ∈ {p : Unit × (Fin d → ℤ) | p.2 ∈ K₂}} ∩
        ⋂ r' : ℚ, ({p | ¬ (0 ≤ ratNN r' ∧ ratNN r' < r)} ∪
          {p | (p.1, p.2 (ratNN r')) ∈ {p : Unit × (Fin d → ℤ) | p.2 ∈ K₂}}))) = A2 at h2
  refine ⟨(Prod.mk () ⁻¹' A1) ∩ (Prod.mk () ⁻¹' A2), ?_, fun γ hγ => ?_⟩
  · exact ((measurable_prodMk_left) h1.1).inter ((measurable_prodMk_left) h2.1)
  · have a := h1.2 () γ hγ
    have b := h2.2 () γ hγ
    have c : (∀ s : ℝ≥0, s ≤ r → γ s ∈ K₂) ↔ ∀ s : ℝ≥0, 0 ≤ s → s ≤ r → γ s ∈ K₂ :=
      ⟨fun h s _ hs => h s hs, fun h s hs => h s (by positivity) hs⟩
    exact (and_congr Iff.rfl c).trans (and_congr a b)

/-- The first event: reach `72` at time `1`, monotone-like bounds `0 ≤ β ≤ 72` before. -/
def gam0 : Set (PathSpace 1) :=
  evalForall {v | v 0 = 72} {v | 0 ≤ v 0 ∧ v 0 ≤ 72} 1

/-- A window event. -/
def gamWin (ρ : ℝ≥0) : Set (PathSpace 1) :=
  evalForall {v | √(ρ : ℝ) / 2 ≤ (v 0 : ℝ)} {v | |(v 0 : ℝ)| < 9 * √(ρ : ℝ)} ρ

theorem IsSRW.prob_gamWin {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace 1}
    (hY : IsSRW P Y) {ρ : ℝ≥0} (hρ : 16 ≤ (ρ : ℝ)) :
    1 / 1100 ≤ P.real {ω | Y ω ∈ gamWin ρ} := hY.push hρ

/-- Probability of the first event for the canonical walk. -/
theorem prob_gam0_canonical {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (Dir 1 × ℝ)} (hN : IsPoissonPointProcess N (clockIntensity (Dir 1)) P) :
    Real.exp (-2) / (72 : ℕ).factorial ≤ P.real {ω | canonical 1 N ω ∈ gam0} := by
  have := hN.isProbabilityMeasure
  set A := cntN N 1 ((0 : Fin 1), true) with hA
  set B := cntN N 1 ((0 : Fin 1), false) with hB
  have hind : IndepFun A B P := (iIndepFun_cntN hN 1).indepFun (by simp)
  have hAm := measurable_cntN hN 1 ((0 : Fin 1), true)
  have hBm := measurable_cntN hN 1 ((0 : Fin 1), false)
  have hsub : {ω | A ω = 72} ∩ {ω | B ω = 0} ≤ᵐ[P] {ω | canonical 1 N ω ∈ gam0} := by
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
    have hmono : ∀ (v : Dir 1) (s : ℝ≥0), s ≤ 1 → cnt (N ω) v s ≤ cnt (N ω) v 1 := by
      intro v s hs
      unfold cnt
      refine measure_mono (prod_mono subset_rfl (Ioc_subset_Ioc_right ?_))
      exact_mod_cast hs
    have hz : cnt (N ω) ((0 : Fin 1), false) 1 = 0 := by
      have := hcn _ _ 0 h2
      simpa using this
    have h72 : cnt (N ω) ((0 : Fin 1), true) 1 = 72 := by
      have := hcn _ _ 72 h1
      simpa using this
    show canonical 1 N ω ∈ evalForall _ _ 1
    refine ⟨?_, fun s hs => ?_⟩
    · show (canonical 1 N ω 1) 0 = 72
      show walk 1 (N ω) ((1 : ℝ≥0) : ℝ) 0 = 72
      rw [walk_apply hg]
      simp only [NNReal.coe_one]
      rw [h1, h2]; simp
    · show 0 ≤ (canonical 1 N ω s) 0 ∧ (canonical 1 N ω s) 0 ≤ 72
      show 0 ≤ walk 1 (N ω) (s : ℝ) 0 ∧ walk 1 (N ω) (s : ℝ) 0 ≤ 72
      rw [walk_apply hg]
      have hf : cnt (N ω) ((0 : Fin 1), false) s = 0 := by
        have := hmono ((0 : Fin 1), false) s hs
        rw [hz] at this
        exact le_antisymm this bot_le
      have ht : cnt (N ω) ((0 : Fin 1), true) s ≤ 72 := by
        have := hmono ((0 : Fin 1), true) s hs
        rwa [h72] at this
      obtain ⟨m, hm⟩ := good_cnt hg ((0 : Fin 1), true) s
      rw [hm] at ht ⊢
      have hm72 : m ≤ 72 := by exact_mod_cast ht
      rw [hf]
      simp only [natOf, ENNReal.toReal_natCast, Nat.floor_natCast, ENNReal.toReal_zero,
        Nat.floor_zero]
      constructor <;> push_cast <;> omega
  have hmeasA : MeasurableSet {ω | A ω = 72} := hAm (measurableSet_singleton 72)
  have hmeasB : MeasurableSet {ω | B ω = 0} := hBm (measurableSet_singleton 0)
  have hprod : P.real ({ω | A ω = 72} ∩ {ω | B ω = 0}) =
      P.real {ω | A ω = 72} * P.real {ω | B ω = 0} := by
    have := (indepFun_iff_measure_inter_preimage_eq_mul.1 hind) {72} {0}
      (measurableSet_singleton 72) (measurableSet_singleton 0)
    simp only [measureReal_def]
    rw [← ENNReal.toReal_mul]
    exact congrArg ENNReal.toReal this
  have hpo : ∀ (v : Dir 1) (n : ℕ), P.real {ω | cntN N 1 v ω = n} = po 1 n := by
    intro v n
    have h := map_cntN hN (t := 1) zero_le_one v
    have : P {ω | cntN N 1 v ω = n} = poissonMeasure ((1 : ℝ).toNNReal) {n} := by
      rw [← h, Measure.map_apply (measurable_cntN hN 1 v) (measurableSet_singleton n)]
      rfl
    rw [measureReal_def, this, poissonMeasure_singleton]
    unfold po
    simp
    try positivity
  have hAv := hpo ((0 : Fin 1), true) 72
  have hBv := hpo ((0 : Fin 1), false) 0
  rw [← hA] at hAv
  rw [← hB] at hBv
  have hle : P.real ({ω | A ω = 72} ∩ {ω | B ω = 0}) ≤ P.real {ω | canonical 1 N ω ∈ gam0} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  refine le_trans ?_ hle
  rw [hprod, hAv, hBv]
  unfold po
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, mul_one, one_pow]
  have e2 : Real.exp (-1) * Real.exp (-1) = Real.exp (-2) := by
    rw [← Real.exp_add]; norm_num
  have e : Real.exp (-1) / ((Nat.factorial 72 : ℕ) : ℝ) * Real.exp (-1) =
      Real.exp (-2) / ((Nat.factorial 72 : ℕ) : ℝ) := by
    rw [← e2]; ring
  exact le_of_eq e.symm

end SRW
end ElboimSly
