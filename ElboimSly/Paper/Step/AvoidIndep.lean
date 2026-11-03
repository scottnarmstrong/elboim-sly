/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.AvoidSetting
public import Mathlib

/-!
# Independence and law of the regenerated walk after a stopping time

ES22 Lemma 4.1 (independence).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω}

theorem stepAvoid_strong_markov {β : ℝ} [Fact (0 < β)] (hY : IsSRW P Y)
    (hYp : ∀ ω, Y ω ∈ StepPath d) (hF : IsAdmissible P Y F) (a : ℝ≥0) {S : Ω → WithTop ℝ≥0}
    (hS : IsStoppingTime (stepShiftFilt hF a) S) {A : Set Ω}
    (hA : MeasurableSet[hS.measurableSpace] A) {Γ : Set (PathSpace d)} (hΓ : MeasurableSet Γ) :
    P ({ω | S ω < ⊤} ∩ (A ∩ stepXat β a Y S ⁻¹' Γ)) =
      P (A ∩ {ω | S ω < ⊤}) * P {ω | stepReg β (Y ω) ∈ Γ} := by
  have hR := isStoppingTime_stepShiftStop hF a hS
  have := stepReg_strong_markov (β := β) hY hYp hF hR (measurableSet_stepShiftStop hF a hS hA) hΓ
  have e1 : {ω | stepShiftStop a S ω < ⊤} = {ω | S ω < ⊤} := by
    ext ω; exact stepShiftStop_lt_top_iff a S ω
  rw [e1] at this
  rw [← this]
  congr 1
  ext ω
  simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, stepXat]
  tauto

variable [P_prob : IsProbabilityMeasure P]

theorem measurableSet_finS {S : Ω → WithTop ℝ≥0} {f : Filtration ℝ≥0 mΩ}
    (hS : IsStoppingTime f S) : MeasurableSet {ω | S ω < ⊤} := by
  have : {ω | S ω < ⊤} = {ω | S ω = ⊤}ᶜ := by
    ext ω; simp [lt_top_iff_ne_top]
  rw [this]
  exact hS.measurableSet_top.compl

/-- Independence of `X_S` and `𝒢_S` under `P(· | S < ∞)`. -/
theorem stepAvoid_indep {β : ℝ} [Fact (0 < β)] (hY : IsSRW P Y)
    (hYp : ∀ ω, Y ω ∈ StepPath d) (hF : IsAdmissible P Y F) (a : ℝ≥0) {S : Ω → WithTop ℝ≥0}
    (hS : IsStoppingTime (stepShiftFilt hF a) S) (hne : P {ω | S ω < ⊤} ≠ 0) :
    Indep hS.measurableSpace (MeasurableSpace.comap (stepXat β a Y S) inferInstance)
      (P[|{ω | S ω < ⊤}]) := by
  have hfin := measurableSet_finS hS
  have hne' : P {ω | S ω < ⊤} ≠ ⊤ := measure_ne_top _ _
  rw [Indep_iff]
  intro t₁ t₂ h₁ h₂
  obtain ⟨Γ, hΓ, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 h₂
  have e1 := stepAvoid_strong_markov (β := β) hY hYp hF a hS h₁ hΓ
  have e2 := stepAvoid_strong_markov (β := β) hY hYp hF a hS (A := univ) MeasurableSet.univ hΓ
  simp only [univ_inter] at e2
  have e3 : P ({ω | S ω < ⊤} ∩ t₁) = P (t₁ ∩ {ω | S ω < ⊤}) := by rw [inter_comm]
  rw [cond_apply hfin, cond_apply hfin, cond_apply hfin, e1, e2, e3]
  have hinv : (P {ω | S ω < ⊤})⁻¹ * P {ω | S ω < ⊤} = 1 := ENNReal.inv_mul_cancel hne hne'
  rw [← mul_assoc (P {ω | S ω < ⊤})⁻¹ (P {ω | S ω < ⊤}), hinv, one_mul, mul_assoc]

/-- The law of `X_S` under `P(· | S < ∞)` is the law of `W_reg^Y`. -/
theorem stepAvoid_prob {β : ℝ} [Fact (0 < β)] (hY : IsSRW P Y)
    (hYp : ∀ ω, Y ω ∈ StepPath d) (hF : IsAdmissible P Y F) (a : ℝ≥0) {S : Ω → WithTop ℝ≥0}
    (hS : IsStoppingTime (stepShiftFilt hF a) S) (hne : P {ω | S ω < ⊤} ≠ 0)
    {Γ : Set (PathSpace d)} (hΓ : MeasurableSet Γ) :
    (P[|{ω | S ω < ⊤}]) (stepXat β a Y S ⁻¹' Γ) = P {ω | stepReg β (Y ω) ∈ Γ} := by
  have hfin := measurableSet_finS hS
  have hne' : P {ω | S ω < ⊤} ≠ ⊤ := measure_ne_top _ _
  have e2 := stepAvoid_strong_markov (β := β) hY hYp hF a hS (A := univ) MeasurableSet.univ hΓ
  simp only [univ_inter] at e2
  rw [cond_apply hfin, e2, ← mul_assoc, ENNReal.inv_mul_cancel hne hne', one_mul]

end ElboimSly.Paper.Step
