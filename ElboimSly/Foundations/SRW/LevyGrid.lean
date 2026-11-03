/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.LevyStep
public import ElboimSly.Foundations.SRW.Eval
public import ElboimSly.Foundations.SRW.Dyadic
public import ElboimSly.Foundations.SRW.Iid
public import Mathlib

/-!
# Lévy's maximal inequality on a finite grid

L'evy's maximal inequality, the finite-grid statements ("One-sided", "Two-sided").
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical

namespace ElboimSly
namespace SRW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem measurableSet_eval1 (τ : ℝ≥0) (S : Set ℤ) :
    MeasurableSet {γ : PathSpace 1 | γ τ 0 ∈ S} :=
  ((measurable_pi_apply (0 : Fin 1)).comp (measurable_pi_apply τ))
    (Set.to_countable S).measurableSet

theorem one_le_two_mul_of_half {p : ℝ} (h : 1 / 2 ≤ p) {μ : Measure Ω} {A : Set Ω}
    [IsFiniteMeasure μ] (hp : μ.real A = p) : 1 ≤ 2 * μ A := by
  have h1 : (1 : ℝ) ≤ 2 * μ.real A := by rw [hp]; linarith
  have h2 : (1 : ℝ≥0∞) ≤ 2 * μ A := by
    have : ENNReal.ofReal 1 ≤ ENNReal.ofReal (2 * μ.real A) := ENNReal.ofReal_le_ofReal h1
    rw [ENNReal.ofReal_mul (by norm_num), Measure.real, ENNReal.ofReal_toReal
      (measure_ne_top _ _)] at this
    simpa using this
  exact h2

/-- Finite-grid Lévy inequality, one-sided. -/
theorem IsSRW.levy_grid {Y : Ω → PathSpace 1} (hY : IsSRW P Y) {T : ℝ≥0} (F : Finset ℝ≥0)
    (hF : ∀ σ ∈ F, σ ≤ T) (lam : ℝ) :
    P {ω | ∃ σ ∈ F, lam ≤ (Y ω σ 0 : ℝ)} ≤ 2 * P {ω | lam ≤ (Y ω T 0 : ℝ)} := by
  have := hY.isProbabilityMeasure
  let B : ℝ≥0 → Set (PathSpace 1) := fun τ =>
    {γ | lam ≤ (γ τ 0 : ℝ) ∧ ∀ σ ∈ F, σ < τ → (γ σ 0 : ℝ) < lam}
  have hB : ∀ τ, MeasurableSet (B τ) := by
    intro τ
    have h1 : MeasurableSet {γ : PathSpace 1 | lam ≤ (γ τ 0 : ℝ)} :=
      measurableSet_le measurable_const
        ((Measurable.of_discrete (f := fun n : ℤ => (n : ℝ))).comp
          ((measurable_pi_apply (0 : Fin 1)).comp (measurable_pi_apply τ)))
    have h2 : MeasurableSet {γ : PathSpace 1 | ∀ σ ∈ F, σ < τ → (γ σ 0 : ℝ) < lam} := by
      have : {γ : PathSpace 1 | ∀ σ ∈ F, σ < τ → (γ σ 0 : ℝ) < lam} =
          ⋂ σ ∈ F, {γ : PathSpace 1 | σ < τ → (γ σ 0 : ℝ) < lam} := by
        ext γ; simp
      rw [this]
      refine Finset.measurableSet_biInter F fun σ _ => ?_
      by_cases h : σ < τ
      · simp only [h, true_implies]
        exact measurableSet_lt
          ((Measurable.of_discrete (f := fun n : ℤ => (n : ℝ))).comp
            ((measurable_pi_apply (0 : Fin 1)).comp (measurable_pi_apply σ))) measurable_const
      · simp [h]
    exact h1.inter h2
  have hstop : ∀ τ γ, γ ∈ B τ ↔ stopPath τ γ ∈ B τ := by
    intro τ γ
    simp only [B, mem_ofPred_eq, stopPath, min_self]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun σ hσ hlt => by rw [min_eq_left hlt.le]; exact h2 σ hσ hlt⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun σ hσ hlt => by have := h2 σ hσ hlt; rwa [min_eq_left hlt.le] at this⟩
  have hdisj : (↑F : Set ℝ≥0).PairwiseDisjoint B := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    intro γ h1 h2
    simp only [B, mem_ofPred_eq] at h1 h2
    rcases lt_or_gt_of_ne hab with h | h
    · have := h2.2 a ha h; linarith [h1.1]
    · have := h1.2 b hb h; linarith [h2.1]
  have key := hY.levy_step (T := T) F (fun i => i) hF B hB hstop hdisj (fun _ => {x : ℤ | 0 ≤ x})
    (fun τ hτ => by
      have hh := (hY.half_le (T - τ)).1
      refine one_le_two_mul_of_half hh (by rfl) |> fun h => ?_
      simpa using h)
    {x : ℤ | lam ≤ (x : ℝ)} (by
      intro τ _ γ hγ x hx
      simp only [mem_ofPred_eq] at hx ⊢
      have : (0 : ℝ) ≤ x := by exact_mod_cast hx
      push_cast
      linarith [hγ.1])
  have hset : Y ⁻¹' (⋃ i ∈ F, B i) = {ω | ∃ σ ∈ F, lam ≤ (Y ω σ 0 : ℝ)} := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, h, _⟩; exact ⟨i, hi, h⟩
    · rintro ⟨σ, hσ, hs⟩
      have hne : (F.filter fun σ => lam ≤ (Y ω σ 0 : ℝ)).Nonempty := ⟨σ, by simp [hσ, hs]⟩
      set m := (F.filter fun σ => lam ≤ (Y ω σ 0 : ℝ)).min' hne
      have hm := Finset.min'_mem _ hne
      rw [Finset.mem_filter] at hm
      refine ⟨m, hm.1, hm.2, fun σ' hσ' hlt => ?_⟩
      by_contra hcon
      push Not at hcon
      have : m ≤ σ' := Finset.min'_le _ _ (by simp [hσ', hcon])
      exact absurd hlt (not_lt.2 this)
  rw [hset] at key
  simpa using key

/-- Finite-grid Lévy inequality, two-sided. -/
theorem IsSRW.levy_grid_abs {Y : Ω → PathSpace 1} (hY : IsSRW P Y) {T : ℝ≥0} (F : Finset ℝ≥0)
    (hF : ∀ σ ∈ F, σ ≤ T) (lam : ℝ) :
    P {ω | ∃ σ ∈ F, lam ≤ |(Y ω σ 0 : ℝ)|} ≤ 2 * P {ω | lam ≤ |(Y ω T 0 : ℝ)|} := by
  have := hY.isProbabilityMeasure
  by_cases hl : lam ≤ 0
  · have h1 : {ω | lam ≤ |(Y ω T 0 : ℝ)|} = univ := by
      ext ω; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact hl.trans (abs_nonneg _)
    have := hY.isProbabilityMeasure
    rw [h1]
    calc P {ω | ∃ σ ∈ F, lam ≤ |(Y ω σ 0 : ℝ)|} ≤ 1 := prob_le_one
      _ ≤ 2 * P univ := by simp
  push Not at hl
  let B : ℝ≥0 × Bool → Set (PathSpace 1) := fun p =>
    {γ | lam ≤ |(γ p.1 0 : ℝ)| ∧ (∀ σ ∈ F, σ < p.1 → |(γ σ 0 : ℝ)| < lam) ∧
      (0 ≤ γ p.1 0 ↔ p.2 = true)}
  have hmeasabs : ∀ σ : ℝ≥0, Measurable fun γ : PathSpace 1 => |(γ σ 0 : ℝ)| := fun σ =>
    ((Measurable.of_discrete (f := fun n : ℤ => |(n : ℝ)|)).comp
      ((measurable_pi_apply (0 : Fin 1)).comp (measurable_pi_apply σ)))
  have hB : ∀ p, MeasurableSet (B p) := by
    intro p
    have h1 : MeasurableSet {γ : PathSpace 1 | lam ≤ |(γ p.1 0 : ℝ)|} :=
      measurableSet_le measurable_const (hmeasabs _)
    have h2 : MeasurableSet {γ : PathSpace 1 | ∀ σ ∈ F, σ < p.1 → |(γ σ 0 : ℝ)| < lam} := by
      have : {γ : PathSpace 1 | ∀ σ ∈ F, σ < p.1 → |(γ σ 0 : ℝ)| < lam} =
          ⋂ σ ∈ F, {γ : PathSpace 1 | σ < p.1 → |(γ σ 0 : ℝ)| < lam} := by
        ext γ; simp
      rw [this]
      refine Finset.measurableSet_biInter F fun σ _ => ?_
      by_cases h : σ < p.1
      · simp only [h, true_implies]
        exact measurableSet_lt (hmeasabs σ) measurable_const
      · simp [h]
    have h3 : MeasurableSet {γ : PathSpace 1 | 0 ≤ γ p.1 0 ↔ p.2 = true} := by
      by_cases hb : p.2 = true
      · convert measurableSet_eval1 p.1 (Ici 0) using 1
        ext γ; simp [hb]
      · convert (measurableSet_eval1 p.1 (Ici 0)).compl using 1
        ext γ; simp [hb]
    exact h1.inter (h2.inter h3)
  have hstop : ∀ p γ, γ ∈ B p ↔ stopPath p.1 γ ∈ B p := by
    intro p γ
    simp only [B, mem_ofPred_eq, stopPath, min_self]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun σ hσ hlt => by rw [min_eq_left hlt.le]; exact h2 σ hσ hlt, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun σ hσ hlt => by have := h2 σ hσ hlt; rwa [min_eq_left hlt.le] at this, h3⟩
  have hdisj : (↑(F ×ˢ (Finset.univ : Finset Bool)) : Set (ℝ≥0 × Bool)).PairwiseDisjoint B := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    intro γ h1 h2
    simp only [Finset.coe_product, Finset.coe_univ, mem_prod, Finset.mem_coe, mem_univ,
      and_true] at ha hb
    simp only [B, mem_ofPred_eq] at h1 h2
    rcases lt_trichotomy a.1 b.1 with h | h | h
    · have := h2.2.1 a.1 ha h; linarith [h1.1]
    · have e1 := h1.2.2
      have e2 := h2.2.2
      rw [← h] at e2
      have : a.2 = b.2 := Bool.eq_iff_iff.2 (e1.symm.trans e2)
      exact hab (Prod.ext h this)
    · have := h1.2.1 b.1 hb h; linarith [h2.1]
  have key := hY.levy_step (T := T) (F ×ˢ (Finset.univ : Finset Bool)) Prod.fst
    (fun i hi => hF _ (Finset.mem_product.1 hi).1) B hB hstop hdisj
    (fun p => if p.2 = true then {x : ℤ | 0 ≤ x} else {x : ℤ | x ≤ 0})
    (fun p hp => by
      have hh := hY.half_le (T - p.1)
      by_cases hb : p.2 = true
      · simp only [hb, ite_true]
        exact one_le_two_mul_of_half hh.1 (by rfl)
      · simp only [hb]
        exact one_le_two_mul_of_half hh.2 (by rfl))
    {x : ℤ | lam ≤ |(x : ℝ)|}
    (by
      intro p _ γ hγ x hx
      obtain ⟨h1, _, h3⟩ := hγ
      simp only [mem_ofPred_eq]
      by_cases hb : p.2 = true
      · simp only [hb, ite_true, mem_ofPred_eq] at hx
        have hp : 0 ≤ γ p.1 0 := h3.2 hb
        have hp' : (0 : ℝ) ≤ γ p.1 0 := by exact_mod_cast hp
        have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
        rw [abs_of_nonneg hp'] at h1
        push_cast
        rw [abs_of_nonneg (by linarith)]
        linarith
      · simp only [hb] at hx
        have hp : ¬ 0 ≤ γ p.1 0 := fun h => hb (h3.1 h)
        have hp' : (γ p.1 0 : ℝ) < 0 := by exact_mod_cast not_le.1 hp
        have hx' : (x : ℝ) ≤ 0 := by exact_mod_cast hx
        rw [abs_of_neg hp'] at h1
        push_cast
        rw [abs_of_nonpos (by linarith)]
        linarith)
  have hset : Y ⁻¹' (⋃ i ∈ F ×ˢ (Finset.univ : Finset Bool), B i) =
      {ω | ∃ σ ∈ F, lam ≤ |(Y ω σ 0 : ℝ)|} := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, h, _⟩; exact ⟨i.1, (Finset.mem_product.1 hi).1, h⟩
    · rintro ⟨σ, hσ, hs⟩
      have hne : (F.filter fun σ => lam ≤ |(Y ω σ 0 : ℝ)|).Nonempty :=
        ⟨σ, by simp [hσ, hs]⟩
      set m := (F.filter fun σ => lam ≤ |(Y ω σ 0 : ℝ)|).min' hne
      have hm := Finset.min'_mem _ hne
      rw [Finset.mem_filter] at hm
      refine ⟨(m, decide (0 ≤ Y ω m 0)), Finset.mem_product.2 ⟨hm.1, Finset.mem_univ _⟩,
        hm.2, fun σ' hσ' hlt => ?_, by simp⟩
      by_contra hcon
      push Not at hcon
      have : m ≤ σ' := Finset.min'_le _ _ (by simp [hσ', hcon])
      exact absurd hlt (not_lt.2 this)
  rw [hset] at key
  exact key

end SRW
end ElboimSly
