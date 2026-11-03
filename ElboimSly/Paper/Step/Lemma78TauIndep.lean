/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78TauHist
public import ElboimSly.Paper.Step.Lemma78TauSurr
public import ElboimSly.Foundations.Cyclic.CycRegenCoupleDef
public import ElboimSly.Foundations.Cyclic.CycContRegen
public import ElboimSly.Foundations.Cyclic.CycRegenEnvAe
public import Mathlib

/-!
# The surrogate for `W'_i` is independent of `ℱ⁺_{ζ_i}`

W_2 after zeta_i, given ℱ^+_zeta_i; One excursion succeeds with probability at least frac12. For a `(ℱ⁺_t)`-stopping time `Z`, the
surrogate `Wsur = planSurr … (t'_n + Z) δ` of `W'` (measurable, right-continuous, a.s. equal to `W'`)
is independent of `ℱ⁺_Z` under `P(· | t'_n + Z < ∞)` and has there the law of the regenerated
walk (`step78_surr_indep_law`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0)
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS Unit d β)} {N'' : Ω → Measure (ℕ × RingSpace d β)}
  (hN : IsPoissonPointProcess N (cycIntensity Unit d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity Unit d β) Pr)
  (hN'' : IsPoissonPointProcess N'' ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)
  (hI3 : Indep (MeasurableSpace.comap N'' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ MeasurableSpace.comap N' inferInstance ⊔
      cycNull Pr) Pr)

theorem step78Plan_K_pos : 0 < (step78Plan d β u q Tn).K := by
  show 0 < 2
  norm_num

include hN hN' hN'' hI1 hI2 hI3 in
/-- The coupling identity of w_2 after zeta_i, given ℱ^+_zeta_i for the surrogate. -/
theorem step78_surr_couple (h𝒢 : 𝒢₀ ≤ mΩ) {Z : Ω → WithTop ℝ≥0}
    (hZ : IsStoppingTime (step78Filt u q Tn 𝒢₀ hN h𝒢) Z) {A : Set Ω}
    (hA : MeasurableSet[(step78_isStoppingTime_T u q Tn 𝒢₀ hN h𝒢 hZ).measurableSpace] A)
    {Γ : Set (ℝ≥0 → Fin d → ℤ)} (hΓ : MeasurableSet Γ) :
    Pr (A ∩ {ω | step78T Tn Z ω ≠ ⊤} ∩ {ω | planSurr (step78Plan d β u q Tn) N N' N''
        (step78T Tn Z) (step78Delta N u q Z) ω ∈ Γ}) =
      Pr (A ∩ {ω | step78T Tn Z ω ≠ ⊤}) *
        Pr {ω | (fun t : ℝ≥0 => ElboimSly.regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ)) ∈
          Γ} := by
  rw [← (step78_couple_of_shifted u q Tn 𝒢₀ hN hN' hN'' hI1 hI2 hI3 h𝒢 hZ).1 hA hΓ]
  refine measure_congr (Filter.EventuallyEqSet.inter (Filter.EventuallyEq.refl _ _) ?_)
  filter_upwards [planSurr_ae_eq (step78Plan d β u q Tn) 𝒢₀ hN hN' hI1 hI2 (N'' := N'')
    (T := step78T Tn Z) (step78Delta N u q Z)] with ω h
  show (planSurr (step78Plan d β u q Tn) N N' N'' (step78T Tn Z) (step78Delta N u q Z) ω ∈ Γ) =
    (contGlue β.toNNReal (planFirst (step78Plan d β u q Tn) N N' (step78T Tn Z)
      (step78Delta N u q Z) ω) (contSeq N'' ω) ∈ Γ)
  rw [h]

include hN hN' hN'' hI1 hI2 hI3 in
/-- Under `P(· | t'_n + Z < ∞)`, the surrogate is independent of `ℱ⁺_Z` and has the law of the
regenerated walk. -/
theorem step78_surr_indep_law (h𝒢 : 𝒢₀ ≤ mΩ) {Z : Ω → WithTop ℝ≥0}
    (hZ : IsStoppingTime (step78Filt u q Tn 𝒢₀ hN h𝒢) Z)
    (hne : Pr {ω | step78T Tn Z ω ≠ ⊤} ≠ 0) :
    Indep hZ.measurableSpace (MeasurableSpace.comap (planSurr (step78Plan d β u q Tn) N N' N''
      (step78T Tn Z) (step78Delta N u q Z)) inferInstance) (Pr[|{ω | step78T Tn Z ω ≠ ⊤}]) ∧
    (Pr[|{ω | step78T Tn Z ω ≠ ⊤}]).map (planSurr (step78Plan d β u q Tn) N N' N''
      (step78T Tn Z) (step78Delta N u q Z)) =
      Pr.map (fun ω (t : ℝ≥0) => ElboimSly.regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ)) := by
  have := hN.isProbabilityMeasure
  set E : Set Ω := {ω | step78T Tn Z ω ≠ ⊤} with hE
  have hT := step78_isStoppingTime_T u q Tn 𝒢₀ hN h𝒢 hZ
  have hEm : MeasurableSet E := hT.measurableSpace_le _ (measurableSet_ne_top hT)
  have hEfin : Pr E ≠ ⊤ := measure_ne_top _ _
  have : IsProbabilityMeasure (Pr[|E]) := cond_isProbabilityMeasure hne
  set W := planSurr (step78Plan d β u q Tn) N N' N'' (step78T Tn Z) (step78Delta N u q Z) with hW
  have hWm : Measurable W := measurable_planSurr (step78Plan d β u q Tn) 𝒢₀ hN hN' hI1 hI2
    (step78Plan_K_pos u q Tn) h𝒢 hT (step78_measurable_delta u q Tn 𝒢₀ hN h𝒢 hT) hN''
  have hcpl := fun {A : Set Ω}
      (hA : MeasurableSet[hT.measurableSpace] A) {Γ : Set (ℝ≥0 → Fin d → ℤ)}
      (hΓ : MeasurableSet Γ) => step78_surr_couple u q Tn 𝒢₀ hN hN' hN'' hI1 hI2 hI3 h𝒢 hZ hA hΓ
  have hq : ∀ {Γ : Set (ℝ≥0 → Fin d → ℤ)}, MeasurableSet Γ →
      (Pr[|E]) (W ⁻¹' Γ) = Pr {ω | (fun t : ℝ≥0 => ElboimSly.regenWalk
        (fun k => cycSlice k (N'' ω)) (t : ℝ)) ∈ Γ} := by
    intro Γ hΓ
    have h1 := hcpl (A := univ) (@MeasurableSet.univ _ hT.measurableSpace) hΓ
    rw [univ_inter] at h1
    have h1' : Pr (E ∩ W ⁻¹' Γ) = Pr E * Pr {ω | (fun t : ℝ≥0 => ElboimSly.regenWalk
        (fun k => cycSlice k (N'' ω)) (t : ℝ)) ∈ Γ} := h1
    rw [cond_apply hEm, h1', ← mul_assoc, ENNReal.inv_mul_cancel hne hEfin, one_mul]
  refine ⟨?_, ?_⟩
  · refine (Indep_iff _ _ _).2 fun t1 t2 h1 h2 => ?_
    obtain ⟨Γ, hΓ, rfl⟩ := h2
    have h1T : MeasurableSet[hT.measurableSpace] t1 := step78_ms_le u q Tn 𝒢₀ hN h𝒢 hZ _ h1
    have h2' := hcpl h1T hΓ
    have h2'' : Pr (E ∩ (t1 ∩ W ⁻¹' Γ)) = Pr (E ∩ t1) * Pr {ω | (fun t : ℝ≥0 =>
        ElboimSly.regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ)) ∈ Γ} := by
      have e : E ∩ (t1 ∩ W ⁻¹' Γ) = t1 ∩ E ∩ W ⁻¹' Γ := by
        ext ω; simp only [mem_inter_iff, mem_preimage]; tauto
      rw [e, inter_comm E t1]
      exact h2'
    rw [hq hΓ, cond_apply hEm, cond_apply hEm, h2'', inter_comm E t1]
    ring
  · ext Γ hΓ
    have hRm : AEMeasurable (fun ω (t : ℝ≥0) =>
        ElboimSly.regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ)) Pr := by
      refine ((measurable_regW (d := d) (β := β)).comp hN''.measurable).aemeasurable.congr ?_
      filter_upwards [ae_cycGood hN''] with ω hω
      funext t
      exact (regenWalk_eq_contGlue (ν := fun k => cycSlice k (N'' ω)) hω t).symm
    rw [Measure.map_apply hWm hΓ, hq hΓ, Measure.map_apply_of_aemeasurable hRm hΓ]
    rfl

end ElboimSly.Paper.Step

end
