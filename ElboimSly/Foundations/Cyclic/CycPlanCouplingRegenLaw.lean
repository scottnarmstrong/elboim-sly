/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycPlanCouplingRegen
public import Mathlib

/-!
# Plan-level coupling after a stopping time (d): the law of the regenerated continuation

Plan-level coupling after a stopping time (d), last claim. Under `Q = P(· | T < ∞)` the pair
`(P' - u, N'')` is independent of `ℱ_T` with law `Law(W) ⊗ Law(N'')`
(`cyc_plan_coupling_cont_rect` and `Measure.prod_eq`), and the glue `G` of the pieces is
measurable (`measurable_contGlue_at`) and, applied to the pieces of a `PPP(# ⊗ μ_β)`, gives its
regenerated walk (`regenWalk_eq_contGlue`, `law_head_tail`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

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

theorem measurable_contGlue_pair (b : ℝ≥0) :
    Measurable fun x : (ℝ≥0 → Fin d → ℤ) × (ℕ → ℝ≥0 → Fin d → ℤ) => contGlue b x.1 x.2 :=
  measurable_pi_iff.2 fun t => measurable_contGlue_at t

/-- **plan-level coupling after a stopping time (d)**, agreement: `W'(r) = P'(r) - u` for `r ∈ [0, treg(P' - u)]`
(for every `ω`). -/
theorem cyc_plan_coupling_regen_agree (T : Ω → WithTop ℝ≥0) (δ : Ω → CycData I d) (ω : Ω) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) ≤ pathTreg β.toNNReal (planFirst P N N' T δ ω)) :
    contGlue β.toNNReal (planFirst P N N' T δ ω) (contSeq N'' ω) r = planFirst P N N' T δ ω r :=
  contGlue_agree (Real.toNNReal_pos.2 Fact.out) _ _ (fun k => contSeq_zero_apply _ k) hr

include hN hN' hN'' hI1 hI2 hI3 in
/-- **plan-level coupling after a stopping time (d)**, the joint law: the pair (recentred path, walks of `N''`) has,
on `A ∩ {T < ∞}`, the product of the law of the cyclic walk and the law of the walks of `N''`. -/
theorem cyc_plan_coupling_cont_joint (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    {δ : Ω → CycData I d} (hδ : Measurable[hT.measurableSpace] δ)
    {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A)
    {B : Set ((ℝ≥0 → Fin d → ℤ) × (ℕ → ℝ≥0 → Fin d → ℤ))} (hB : MeasurableSet B) :
    Pr (A ∩ {ω | T ω ≠ ⊤} ∩ {ω | (planFirst P N N' T δ ω, contSeq N'' ω) ∈ B}) =
      Pr (A ∩ {ω | T ω ≠ ⊤}) *
        ((Pr.map fun ω => walkMap (cycSlice 0 (N'' ω))).prod
          (Pr.map (contSeq N''))) B := by
  have := hN.isProbabilityMeasure
  have hE := (cyc_multi_exploration_a P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT).1
  have hSm : MeasurableSet (A ∩ {ω | T ω ≠ ⊤}) := hT.measurableSpace_le _ (hA.inter hE)
  have hYae := aemeasurable_planFirst P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT hδ
  have hZm : Measurable (contSeq N'') :=
    measurable_pi_iff.2 fun k => measurable_walkSlice hN'' k
  have hLW : Measurable fun ω => walkMap (cycSlice 0 (N'' ω)) := measurable_walkSlice hN'' 0
  have hpair : AEMeasurable (fun ω => (planFirst P N N' T δ ω, contSeq N'' ω)) Pr :=
    hYae.prodMk hZm.aemeasurable
  set S := A ∩ {ω | T ω ≠ ⊤} with hS
  set ρ := (Pr.restrict S).map (fun ω => (planFirst P N N' T δ ω, contSeq N'' ω)) with hρ
  have hrect : ∀ Γ1 Γ2, MeasurableSet Γ1 → MeasurableSet Γ2 →
      ρ (Γ1 ×ˢ Γ2) = (Pr S • Pr.map fun ω => walkMap (cycSlice 0 (N'' ω))) Γ1 *
        (Pr.map (contSeq N'')) Γ2 := by
    intro Γ1 Γ2 h1 h2
    rw [hρ, Measure.map_apply_of_aemeasurable (hpair.mono_measure Measure.restrict_le_self)
      (h1.prod h2), Measure.restrict_apply' hSm, Measure.smul_apply, Measure.map_apply hLW h1,
      Measure.map_apply hZm h2, smul_eq_mul]
    have := cyc_plan_coupling_cont_rect P 𝒢₀ hN hN' hN'' hI1 hI2 hI3 hK h𝒢 hT hδ hA h1 h2
    have e : (fun ω => (planFirst P N N' T δ ω, contSeq N'' ω)) ⁻¹' (Γ1 ×ˢ Γ2) ∩ S =
        A ∩ {ω | T ω ≠ ⊤} ∩ {ω | planFirst P N N' T δ ω ∈ Γ1} ∩ {ω | contSeq N'' ω ∈ Γ2} := by
      ext ω; simp only [mem_inter_iff, mem_preimage, mem_prod, hS, mem_ofPred_eq]; tauto
    rw [e]
    exact this
  have hprod : ((Pr S • Pr.map fun ω => walkMap (cycSlice 0 (N'' ω))).prod
      (Pr.map (contSeq N''))) = ρ := by
    have : IsFiniteMeasure (Pr S • Pr.map fun ω => walkMap (cycSlice 0 (N'' ω))) :=
      Measure.smul_finite _ (measure_ne_top Pr S)
    exact Measure.prod_eq hrect
  have e : {ω | (planFirst P N N' T δ ω, contSeq N'' ω) ∈ B} =
      (fun ω => (planFirst P N N' T δ ω, contSeq N'' ω)) ⁻¹' B := rfl
  rw [e, inter_comm, ← Measure.restrict_apply' hSm,
    ← Measure.map_apply_of_aemeasurable (hpair.mono_measure Measure.restrict_le_self) hB,
    ← hρ, ← hprod, Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul]

include hN hN' hN'' hI1 hI2 hI3 in
/-- **plan-level coupling after a stopping time (d)**: the regenerated continuation `W'` of the recentred path is
fresh: `P(A ∩ {T < ∞} ∩ {W' ∈ Γ}) = P(A ∩ {T < ∞}) P(W_reg ∈ Γ)`, with `W_reg` the regenerated
walk of the copies of `N''`. -/
theorem cyc_plan_coupling_regen_law (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    {δ : Ω → CycData I d} (hδ : Measurable[hT.measurableSpace] δ)
    {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A) {Γ : Set (ℝ≥0 → Fin d → ℤ)}
    (hΓ : MeasurableSet Γ) :
    Pr (A ∩ {ω | T ω ≠ ⊤} ∩ {ω | contGlue β.toNNReal (planFirst P N N' T δ ω) (contSeq N'' ω) ∈ Γ}) =
      Pr (A ∩ {ω | T ω ≠ ⊤}) *
        Pr {ω | (fun t : ℝ≥0 => ElboimSly.regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ)) ∈ Γ} := by
  have := hN.isProbabilityMeasure
  have hB : MeasurableSet ((fun x : (ℝ≥0 → Fin d → ℤ) × (ℕ → ℝ≥0 → Fin d → ℤ) =>
      contGlue β.toNNReal x.1 x.2) ⁻¹' Γ) := measurable_contGlue_pair _ hΓ
  have h1 := cyc_plan_coupling_cont_joint P 𝒢₀ hN hN' hN'' hI1 hI2 hI3 hK h𝒢 hT hδ hA hB
  have hm : ∀ k, Measurable fun ω => walkMap (cycSlice k (N'' ω)) := measurable_walkSlice hN''
  have hht : Measurable fun ω => (walkMap (cycSlice 0 (N'' ω)),
      fun k => walkMap (cycSlice (k + 1) (N'' ω))) :=
    (hm 0).prodMk (measurable_pi_iff.2 fun k => hm (k + 1))
  have h2 : (Pr.map fun ω => walkMap (cycSlice 0 (N'' ω))).prod (Pr.map (contSeq N'')) =
      Pr.map (fun ω => (walkMap (cycSlice 0 (N'' ω)),
        fun k => walkMap (cycSlice (k + 1) (N'' ω)))) := (law_head_tail hN'').symm
  rw [h2, Measure.map_apply hht hB] at h1
  refine h1.trans ?_
  congr 1
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [ae_cycGood hN''] with ω hω
  simp only [mem_preimage]
  have := regenWalk_eq_contGlue (ν := fun k => cycSlice k (N'' ω)) hω
  have e : (fun t : ℝ≥0 => ElboimSly.regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ)) =
      contGlue β.toNNReal (walkMap (cycSlice 0 (N'' ω))) (fun k => walkMap (cycSlice (k + 1) (N'' ω))) :=
    funext this
  rw [e]

end ElboimSly.Cyclic

end
