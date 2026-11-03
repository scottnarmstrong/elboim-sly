/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycPlanCouplingFilt
public import ElboimSly.Foundations.Cyclic.CycContRegen
public import Mathlib

/-!
# Plan-level coupling after a stopping time (d): the recentred path and an independent environment

Plan-level coupling after a stopping time (d), proof. For `N''` independent of `σ(𝒢₀,N,N') ∨ 𝒩`, under
`Q = P(· | T < ∞)` the pair (recentred path `P' - u`, sequence of walks of `N''`) is independent of
`ℱ_T`, with the product law (`cyc_plan_coupling_cont_rect`, on rectangles). It is obtained from
Plan-level coupling after a stopping time (b) applied with `𝒢₀ ∨ σ(N'')` in place of `𝒢₀`.
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

/-- The enlarged `σ`-algebra `𝒢₀ ∨ σ(N'')`. -/
@[instance_reducible] def contG {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) {S : Type*} [MeasurableSpace S]
    (N'' : Ω → S) : MeasurableSpace Ω :=
  𝒢₀ ⊔ MeasurableSpace.comap N'' inferInstance

include hN hN' hN'' hI1 hI2 hI3 in
/-- **plan-level coupling after a stopping time (d)**, rectangles: for `A ∈ ℱ_T`, `{T < ∞} ∩ A`, the recentred path
`P' - u` and the sequence of walks of `N''` are independent with the laws of the cyclic walk and of
the sequence of walks of `N''`. -/
theorem cyc_plan_coupling_cont_rect (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    {δ : Ω → CycData I d} (hδ : Measurable[hT.measurableSpace] δ)
    {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A)
    {Γ1 : Set (ℝ≥0 → Fin d → ℤ)} {Γ2 : Set (ℕ → ℝ≥0 → Fin d → ℤ)}
    (hΓ1 : MeasurableSet Γ1) (hΓ2 : MeasurableSet Γ2) :
    Pr (A ∩ {ω | T ω ≠ ⊤} ∩ {ω | (fun s : ℝ≥0 =>
          envWalk (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) (δ ω) s -
            (δ ω).start) ∈ Γ1} ∩ {ω | (fun k => walkMap (cycSlice k (N'' ω))) ∈ Γ2}) =
      Pr (A ∩ {ω | T ω ≠ ⊤}) * Pr {ω | walkMap (cycSlice 0 (N'' ω)) ∈ Γ1} *
        Pr {ω | (fun k => walkMap (cycSlice k (N'' ω))) ∈ Γ2} := by
  have := hN.isProbabilityMeasure
  have h𝒢₁ : contG 𝒢₀ N'' ≤ mΩ := sup_le h𝒢 hN''.measurable.comap_le
  have hZm : Measurable fun ω k => walkMap (cycSlice k (N'' ω)) :=
    measurable_pi_iff.2 fun k => measurable_walkSlice hN'' k
  -- the enlarged data
  have hI1' : Indep (contG 𝒢₀ N'') (MeasurableSpace.comap N inferInstance) Pr := cycNg_indep1 𝒢₀ h𝒢 hN.measurable hN'.measurable hN''.measurable hI1 hI3
  have hI2' : Indep (MeasurableSpace.comap N' inferInstance) (contG 𝒢₀ N'' ⊔ MeasurableSpace.comap N inferInstance) Pr := cycNg_indep2 𝒢₀ h𝒢 hN.measurable hN'.measurable hN''.measurable hI2 hI3
  have hT' : IsStoppingTime (cycMultiFilt P (contG 𝒢₀ N'') hN.measurable h𝒢₁ Pr) T := fun i =>
    cycMultiFilt_mono_gen P 𝒢₀ (contG 𝒢₀ N'') hN.measurable h𝒢 h𝒢₁ le_sup_left i _ (hT i)
  have hmono : ∀ i, cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr i ≤
      cycMultiFilt P (contG 𝒢₀ N'') hN.measurable h𝒢₁ Pr i :=
    fun i => cycMultiFilt_mono_gen P 𝒢₀ (contG 𝒢₀ N'') hN.measurable h𝒢 h𝒢₁ le_sup_left i
  have hle : hT.measurableSpace ≤ hT'.measurableSpace := fun B hB =>
    measurableSet_stopping_mono hmono hT hT' hB
  have hδ' : Measurable[hT'.measurableSpace] δ := hδ.mono hle le_rfl
  obtain ⟨-, -, hb⟩ := cyc_plan_coupling P (contG 𝒢₀ N'') hN hN' hI1' hI2' hK h𝒢₁ hT' hδ'
  -- the set `A' = A ∩ {Z ∈ Γ2}` lies in the enlarged stopping σ-algebra
  have hZ2 : MeasurableSet[(contG 𝒢₀ N'')] {ω | (fun k => walkMap (cycSlice k (N'' ω))) ∈ Γ2} := by
    have : MeasurableSet[MeasurableSpace.comap N'' inferInstance]
        {ω | (fun k => walkMap (cycSlice k (N'' ω))) ∈ Γ2} := by
      have hg : Measurable fun ν : Measure (ℕ × RingSpace d β) =>
          fun k => walkMap (cycSlice k ν) :=
        measurable_pi_iff.2 fun k => measurable_walkMap.comp (measurable_cycSlice k)
      exact ⟨_, hg hΓ2, rfl⟩
    exact le_sup_right (a := 𝒢₀) (b := MeasurableSpace.comap N'' inferInstance) _ this
  have hZ2' : MeasurableSet[hT'.measurableSpace]
      {ω | (fun k => walkMap (cycSlice k (N'' ω))) ∈ Γ2} :=
    measurableSet_stopping_of_gen hT' (fun i => le_cycMultiFilt_gen P (contG 𝒢₀ N'') hN.measurable h𝒢₁ i) hZ2
  have hA' : MeasurableSet[hT'.measurableSpace]
      (A ∩ {ω | (fun k => walkMap (cycSlice k (N'' ω))) ∈ Γ2}) := (hle _ hA).inter hZ2'
  have hbA := hb hA' hΓ1 (M := fun ω => cycSlice 0 (N'' ω))
    (isPoissonPointProcess_slice hN'' 0)
  -- independence of `N''` and the stopping `σ`-algebra
  have hE := (cyc_multi_exploration_a P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT).1
  have hAE : MeasurableSet[hT.measurableSpace] (A ∩ {ω | T ω ≠ ⊤}) := hA.inter hE
  have hFX : hT.measurableSpace ≤ 𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔
      MeasurableSpace.comap N' inferInstance ⊔ cycNull Pr :=
    hT.measurableSpace_le'.trans (iSup_le fun t =>
      (cycMultiFilt_le_X P 𝒢₀ hN.measurable h𝒢 t).trans
        (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
  have hind : Indep hT.measurableSpace (MeasurableSpace.comap N'' inferInstance) Pr :=
    indep_of_indep_of_le_left hI3.symm hFX
  have hind' : Pr (A ∩ {ω | T ω ≠ ⊤} ∩ {ω | (fun k => walkMap (cycSlice k (N'' ω))) ∈ Γ2}) =
      Pr (A ∩ {ω | T ω ≠ ⊤}) * Pr {ω | (fun k => walkMap (cycSlice k (N'' ω))) ∈ Γ2} :=
    (Indep_iff _ _ _).1 hind _ _ hAE
      (by
        have hg : Measurable fun ν : Measure (ℕ × RingSpace d β) =>
            fun k => walkMap (cycSlice k ν) :=
          measurable_pi_iff.2 fun k => measurable_walkMap.comp (measurable_cycSlice k)
        exact ⟨_, hg hΓ2, rfl⟩)
  have e1 : A ∩ {ω | T ω ≠ ⊤} ∩ {ω | (fun s : ℝ≥0 =>
          envWalk (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) (δ ω) s -
            (δ ω).start) ∈ Γ1} ∩ {ω | (fun k => walkMap (cycSlice k (N'' ω))) ∈ Γ2} =
      (A ∩ {ω | (fun k => walkMap (cycSlice k (N'' ω))) ∈ Γ2}) ∩ {ω | T ω ≠ ⊤} ∩
        {ω | (fun s : ℝ≥0 =>
          envWalk (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) (δ ω) s -
            (δ ω).start) ∈ Γ1} := by
    ext ω; simp only [mem_inter_iff, mem_ofPred_eq]; tauto
  have e2 : (A ∩ {ω | (fun k => walkMap (cycSlice k (N'' ω))) ∈ Γ2}) ∩ {ω | T ω ≠ ⊤} =
      A ∩ {ω | T ω ≠ ⊤} ∩ {ω | (fun k => walkMap (cycSlice k (N'' ω))) ∈ Γ2} := by
    ext ω; simp only [mem_inter_iff, mem_ofPred_eq]; tauto
  rw [e1, hbA, e2, hind']
  ring

end ElboimSly.Cyclic

end
