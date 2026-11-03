/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycPlanCoupling
public import ElboimSly.Foundations.Cyclic.CycPlanCouplingRegenLaw
public import Mathlib

/-!
# The plan coupling, form used in §5

The plan coupling, form used in S5.  A bundle of the Foundations results
`cyc_multi_exploration_a` (fresh environment `Ñ_T`), `cyc_plan_coupling` (a), (b),
`cyc_plan_coupling_agree` (c), and the regenerated continuation `cyc_plan_coupling_regen_agree`,
`cyc_plan_coupling_regen_law` (d).

Statement differences with the written proof: the copy set `I` is general (the lemma is used with
`I = ℤ_{≥1}`), and the regenerated continuation is stated with the extra Poisson process `N''` of
Plan-level coupling after a stopping time (d) (independent of `(𝒢₀, N, N')`) supplying the pieces after the first,
rather than with the copies `k ≥ 2` of `Ñ_T`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

universe u'

namespace ElboimSly.Paper

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

include hN hN' hN'' hI1 hI2 hI3 in
/-- **the plan coupling, form used in S5.** -/
theorem es5_plan_coupling (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    {δ : Ω → CycData I d} (hδ : Measurable[hT.measurableSpace] δ) :
    -- (a) `Ñ_T` is a fresh environment
    ((∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A →
      ∀ {F : Set (Measure (CycS I d β))}, MeasurableSet F →
        Pr (A ∩ {ω | T ω ≠ ⊤} ∩
            {ω | tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω ∈ F}) =
          Pr (A ∩ {ω | T ω ≠ ⊤}) * (Pr.map N) F) ∧
    (Pr {ω | T ω ≠ ⊤} = 1 → ∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A →
      ∀ {F : Set (Measure (CycS I d β))}, MeasurableSet F →
        Pr (A ∩ {ω | tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω ∈ F}) =
          Pr A * (Pr.map N) F)) ∧
    -- (a) conditional law of the fresh path
    ((∀ {F : Ω × (ℝ≥0 → Fin d → ℤ) → ℝ≥0∞},
      Measurable[hT.measurableSpace.prod inferInstance] F →
      Measurable[hT.measurableSpace]
        (fun ω => ∫⁻ ν, F (ω, envWalk ν (δ ω)) ∂(Pr.map N))) ∧
    (∀ {F : Ω × (ℝ≥0 → Fin d → ℤ) → ℝ≥0∞},
      Measurable[hT.measurableSpace.prod inferInstance] F →
      ∫⁻ ω in {ω | T ω ≠ ⊤}, F (ω, envWalk
          (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) (δ ω)) ∂Pr =
        ∫⁻ ω in {ω | T ω ≠ ⊤}, ∫⁻ ν, F (ω, envWalk ν (δ ω)) ∂(Pr.map N) ∂Pr)) ∧
    -- (a) the recentred path is fresh
    (∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A → ∀ {Γ : Set (ℝ≥0 → Fin d → ℤ)},
      MeasurableSet Γ → ∀ {Ω' : Type u'} [MeasurableSpace Ω'] {Pr' : Measure Ω'}
        {M : Ω' → Measure (RingSpace d β)},
        IsPoissonPointProcess M (ringIntensity d β) Pr' →
      Pr (A ∩ {ω | T ω ≠ ⊤} ∩ {ω | (fun s : ℝ≥0 =>
          envWalk (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) (δ ω) s -
            (δ ω).start) ∈ Γ}) =
        Pr (A ∩ {ω | T ω ≠ ⊤}) * Pr' {ω' | walkMap (M ω') ∈ Γ}) ∧
    -- (b) agreement up to a discrepancy
    (∀ᵐ ω ∂Pr, T ω ≠ ⊤ → ∀ r : ℝ≥0,
      (Disjoint (CycEntry.region β
          ((δ ω, (envPath (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) (δ ω)).cut r) :
            CycEntry I d)) (cycDiscrepancy P N N' T ω) ∨
        Disjoint (CycEntry.region β
          ((δ ω, (envPath (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) (δ ω)).cut r) :
            CycEntry I d)) (cycRegionStop P (cycNgood N) T ω)) →
      ∀ s : ℝ≥0, s ≤ r →
        envWalk (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) (δ ω) s =
          envWalk (N ω) (δ ω) s) ∧
    -- (c) the regenerated continuation: agreement and freshness
    ((∀ (ω : Ω) {r : ℝ≥0},
      (r : ℝ≥0∞) ≤ pathTreg β.toNNReal (planFirst P N N' T δ ω) →
      contGlue β.toNNReal (planFirst P N N' T δ ω) (contSeq N'' ω) r =
        planFirst P N N' T δ ω r) ∧
    (∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A → ∀ {Γ : Set (ℝ≥0 → Fin d → ℤ)},
      MeasurableSet Γ →
      Pr (A ∩ {ω | T ω ≠ ⊤} ∩
          {ω | contGlue β.toNNReal (planFirst P N N' T δ ω) (contSeq N'' ω) ∈ Γ}) =
        Pr (A ∩ {ω | T ω ≠ ⊤}) *
          Pr {ω | (fun t : ℝ≥0 => ElboimSly.regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ)) ∈ Γ})) := by
  have h1 := cyc_multi_exploration_a P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT
  have h2 := cyc_plan_coupling.{u'} P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT hδ
  have h3 := cyc_plan_coupling_agree P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT δ
  refine ⟨⟨h1.2.2.2.2.2.1, h1.2.2.2.2.2.2.1⟩, ⟨h2.1, h2.2.1⟩, h2.2.2, h3,
    fun ω r hr => cyc_plan_coupling_regen_agree P (N'' := N'') T δ ω hr, ?_⟩
  intro A hA Γ hΓ
  exact cyc_plan_coupling_regen_law P 𝒢₀ hN hN' hN'' hI1 hI2 hI3 hK h𝒢 hT hδ hA hΓ

end ElboimSly.Paper
