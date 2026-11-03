/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.FreezeLower
public import ElboimSly.Foundations.Cyclic.CycPlanCouplingRegenLaw
public import Mathlib

/-!
# Freezing for the regenerated continuation of the plan coupling

The plan coupling, form used in S5 (c) and independence tools (e), as used in ES22 Lemma 5.5 and
ES22 Claim 5.7.

`regenY`: the regenerated walk `Y' - x` of part (c) (a glue of the recentred path and the walks of
`N''`).  `plan_regen_freeze`: if `Z` is `ℱ_T`-measurable, `A ∈ ℱ_T`, and for each `ω ∈ A` the
regenerated walk lies in the slice `{y | (Z ω, y) ∈ S}` with probability at least `q`, then
`P(A ∩ {(Z, Y' - x) ∈ S}) ≥ q P(A)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β)
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS I d β)} {N'' : Ω → Measure (ℕ × RingSpace d β)}
  (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr)
  (hN'' : IsPoissonPointProcess N'' ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)
  (hI3 : Indep (MeasurableSpace.comap N'' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ MeasurableSpace.comap N' inferInstance ⊔
      cycNull Pr) Pr)

/-- The regenerated continuation of the recentred path (part (c) of the plan coupling, minus the
start): the glue of the recentred path `P' - x` with the walks of the copies of `N''`. -/
noncomputable def regenY (P : CycPlan I d β) (N N' : Ω → Measure (CycS I d β))
    (N'' : Ω → Measure (ℕ × RingSpace d β)) (T : Ω → WithTop ℝ≥0) (δ : Ω → CycData I d)
    (ω : Ω) : ℝ≥0 → Fin d → ℤ :=
  contGlue β.toNNReal (planFirst P N N' T δ ω) (contSeq N'' ω)

/-- The regenerated walk of the copies of `N''`. -/
noncomputable def regenW (N'' : Ω → Measure (ℕ × RingSpace d β)) (ω : Ω) : ℝ≥0 → Fin d → ℤ :=
  fun t => ElboimSly.regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ)

include hN hN' hN'' hI1 hI2 hI3 in
/-- **Freezing for the regenerated continuation.** -/
theorem plan_regen_freeze (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    (hfin : ∀ ω, T ω ≠ ⊤) {δ : Ω → CycData I d} (hδ : Measurable[hT.measurableSpace] δ)
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ} (hZ : Measurable[hT.measurableSpace] Z)
    {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A)
    {S : Set (ζ × (ℝ≥0 → Fin d → ℤ))} (hS : MeasurableSet S) {q : ℝ≥0∞}
    (hq : ∀ ω ∈ A, q ≤ Pr {ω' | (Z ω, regenW N'' ω') ∈ S}) :
    q * Pr A ≤ Pr (A ∩ {ω | (Z ω, regenY P N N' N'' T δ ω) ∈ S}) := by
  have := hN.isProbabilityMeasure
  have hlaw : ∀ {A' : Set Ω}, MeasurableSet[hT.measurableSpace] A' →
      ∀ Γ : Set (ℝ≥0 → Fin d → ℤ), MeasurableSet Γ →
      Pr (A' ∩ regenY P N N' N'' T δ ⁻¹' Γ) = Pr A' * Pr {ω | regenW N'' ω ∈ Γ} := by
    intro A' hA' Γ hΓ
    have := cyc_plan_coupling_regen_law P 𝒢₀ hN hN' hN'' hI1 hI2 hI3 hK h𝒢 hT hδ hA' hΓ
    have e : {ω | T ω ≠ ⊤} = univ := by ext ω; simp [hfin ω]
    rw [e, inter_univ] at this
    exact this
  have hY : AEMeasurable (regenY P N N' N'' T δ) Pr := by
    have h1 := aemeasurable_planFirst P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT hδ
    have h2 : Measurable (contSeq N'') := measurable_pi_iff.2 fun k => measurable_walkSlice hN'' k
    have h3 := (measurable_contGlue_pair (d := d) β.toNNReal).comp_aemeasurable
      (h1.prodMk h2.aemeasurable)
    exact h3
  have h0 : ∀ Γ : Set (ℝ≥0 → Fin d → ℤ), MeasurableSet Γ →
      Pr (regenY P N N' N'' T δ ⁻¹' Γ) = Pr {ω | regenW N'' ω ∈ Γ} := by
    intro Γ hΓ
    have := hlaw (A' := univ) (@MeasurableSet.univ _ hT.measurableSpace) Γ hΓ
    rwa [univ_inter, measure_univ, one_mul] at this
  refine freezeLowerAe hT.measurableSpace Pr hT.measurableSpace_le hZ hY ?_ hA hS ?_
  · intro A' hA' Γ hΓ
    rw [hlaw hA' Γ hΓ, h0 Γ hΓ]
  · intro ω hω
    have hsec : MeasurableSet {y | (Z ω, y) ∈ S} := measurable_prodMk_left hS
    rw [Measure.map_apply_of_aemeasurable hY hsec]
    have := h0 _ hsec
    exact (hq ω hω).trans_eq this.symm

end ElboimSly.Paper.Escape
