/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycPlanCouplingLaw
public import ElboimSly.Foundations.Cyclic.CycHitFreeze
public import ElboimSly.Foundations.Cyclic.CycMultiMain
public import Mathlib

/-!
# The plan-level coupling after a stopping time

Plan-level coupling after a stopping time (a), (b), (c). Part (d) (the regenerated continuation) needs
the regenerated walk and its law (the constructions of the regenerated walk) and is not formalized here.

Setting: as in `cyc_multi_exploration_a` (plan `𝒫`, `N, N' ∼ PPP(μ)` on `𝒮 = I × S_β`, `𝒢₀`,
`ℱ^𝒫_s = cycMultiFilt`, `T` a stopping time, records and regions of `cycNgood N`), and
`Ñ_T = N|_{𝒮∖R_T} + N'|_{R_T}` (`tildeMeasure N N' (cycRegionStop P (cycNgood N) T)`). A walk datum
is an `ℱ_T`-measurable `δ : Ω → CycData I d`; `P^ν_δ` is `envWalk ν δ` (the constant `u` off the
good measures).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

universe u'

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β)
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS I d β)}
  (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)

/-- The measurable version of `Ñ`. -/
theorem measurable_tildeTauG {S : Type*} [MeasurableSpace S] (μ : Measure S) [SigmaFinite μ]
    {Ω : Type*} [MeasurableSpace Ω] {N N' : Ω → Measure S} (hN : Measurable N)
    (hN' : Measurable N') {Rg : Ω → Set S}
    (hZ : MeasurableSet {p : Ω × S | p.2 ∈ Rg p.1}) :
    Measurable (tildeMeasure (fun ω => tau μ (N ω)) (fun ω => tau μ (N' ω)) Rg) := by
  have h1 := measurable_tau_restrict_section μ hZ.compl
  have h2 := measurable_tau_restrict_section μ hZ
  exact measurable_add_measure.comp
    ((h1.comp (measurable_id.prodMk hN)).prodMk (h2.comp (measurable_id.prodMk hN')))

include hN hN' hI1 hI2 in
/-- **plan-level coupling after a stopping time** (a) (b). -/
theorem cyc_plan_coupling (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    {δ : Ω → CycData I d} (hδ : Measurable[hT.measurableSpace] δ) :
    -- (a), measurability of the conditional expectation
    (∀ {F : Ω × (ℝ≥0 → Fin d → ℤ) → ℝ≥0∞},
      Measurable[hT.measurableSpace.prod inferInstance] F →
      Measurable[hT.measurableSpace]
        (fun ω => ∫⁻ ν, F (ω, envWalk ν (δ ω)) ∂(Pr.map N))) ∧
    -- (a), conditional law
    (∀ {F : Ω × (ℝ≥0 → Fin d → ℤ) → ℝ≥0∞},
      Measurable[hT.measurableSpace.prod inferInstance] F →
      ∫⁻ ω in {ω | T ω ≠ ⊤}, F (ω, envWalk
          (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) (δ ω)) ∂Pr =
        ∫⁻ ω in {ω | T ω ≠ ⊤}, ∫⁻ ν, F (ω, envWalk ν (δ ω)) ∂(Pr.map N) ∂Pr) ∧
    -- (b), the recentred path is fresh
    (∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A → ∀ {Γ : Set (ℝ≥0 → Fin d → ℤ)},
      MeasurableSet Γ → ∀ {Ω' : Type u'} [MeasurableSpace Ω'] {Pr' : Measure Ω'}
        {M : Ω' → Measure (RingSpace d β)},
        IsPoissonPointProcess M (ringIntensity d β) Pr' →
      Pr (A ∩ {ω | T ω ≠ ⊤} ∩ {ω | (fun s : ℝ≥0 =>
          envWalk (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) (δ ω) s -
            (δ ω).start) ∈ Γ}) =
        Pr (A ∩ {ω | T ω ≠ ⊤}) * Pr' {ω' | walkMap (M ω') ∈ Γ}) := by
  obtain ⟨hE, -, hregset, -, -, hb, -, -, -⟩ :=
    cyc_multi_exploration_a P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT
  have hPr := hN.isProbabilityMeasure
  set E : Set Ω := {ω | T ω ≠ ⊤} with hEdef
  have hEm : MeasurableSet E := hT.measurableSpace_le _ hE
  set Rg := cycRegionStop P (cycNgood N) T with hRg
  have hle : hT.measurableSpace.prod (inferInstance : MeasurableSpace (CycS I d β)) ≤
      mΩ.prod inferInstance :=
    sup_le_sup (MeasurableSpace.comap_mono hT.measurableSpace_le) le_rfl
  set Ytil := tildeMeasure (fun ω => tau (cycIntensity I d β) (N ω))
    (fun ω => tau (cycIntensity I d β) (N' ω)) Rg with hYdef
  have hY : Measurable Ytil :=
    measurable_tildeTauG (cycIntensity I d β) hN.measurable hN'.measurable (hle _ hregset)
  have hYae : ∀ᵐ ω ∂Pr, Ytil ω = tildeMeasure N N' Rg ω := by
    filter_upwards [hN.tau_comp_ae_eq, hN'.tau_comp_ae_eq] with ω h1 h2
    simp only [hYdef, tildeMeasure]
    rw [h1, h2]
  have hstep : ∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A →
      ∀ {B : Set (Measure (CycS I d β))}, MeasurableSet B →
      Pr (E ∩ A ∩ Ytil ⁻¹' B) = Pr (E ∩ A) * (Pr.map N) B := by
    intro A hA B hB
    have h1 := hb hA hB
    have h2 : Pr (E ∩ A ∩ Ytil ⁻¹' B) =
        Pr (A ∩ {ω | T ω ≠ ⊤} ∩ {ω | tildeMeasure N N' Rg ω ∈ B}) := by
      rw [show E ∩ A = A ∩ {ω | T ω ≠ ⊤} from inter_comm _ _]
      refine measure_congr (Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl ?_)
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [hYae] with ω hω
      simp only [mem_preimage, hω]
    rw [h2, h1, inter_comm A]
  have hfr : ∀ {G : Ω × Measure (CycS I d β) → ℝ≥0∞},
      Measurable[hT.measurableSpace.prod inferInstance] G →
      ∫⁻ ω in E, G (ω, Ytil ω) ∂Pr = ∫⁻ ω in E, ∫⁻ ν, G (ω, ν) ∂(Pr.map N) ∂Pr :=
    fun hG => lintegral_freeze_restrict hT.measurableSpace hT.measurableSpace_le hE hY
      (Pr.map N) hstep hG
  -- measurability of the integrand
  have hfst : @Measurable _ _ (hT.measurableSpace.prod inferInstance) hT.measurableSpace
      (Prod.fst : Ω × Measure (CycS I d β) → Ω) := @measurable_fst _ _ hT.measurableSpace _
  have hsnd : @Measurable _ _ (hT.measurableSpace.prod inferInstance) _
      (Prod.snd : Ω × Measure (CycS I d β) → Measure (CycS I d β)) :=
    @measurable_snd _ _ hT.measurableSpace _
  have hGm : ∀ {F : Ω × (ℝ≥0 → Fin d → ℤ) → ℝ≥0∞},
      Measurable[hT.measurableSpace.prod inferInstance] F →
      Measurable[hT.measurableSpace.prod inferInstance]
        (fun p : Ω × Measure (CycS I d β) => F (p.1, envWalk p.2 (δ p.1))) := by
    intro F hF
    have hpair : @Measurable _ _ (hT.measurableSpace.prod inferInstance) _
        (fun p : Ω × Measure (CycS I d β) => (p.2, δ p.1)) :=
      hsnd.prodMk (hδ.comp hfst)
    have h1 : @Measurable _ _ (hT.measurableSpace.prod inferInstance) _
        (fun p : Ω × Measure (CycS I d β) => envWalk p.2 (δ p.1)) :=
      (measurable_envWalk (I := I) (d := d) (β := β)).comp hpair
    exact hF.comp (hfst.prodMk h1)
  refine ⟨?_, ?_, ?_⟩
  · intro F hF
    have := measurable_lintegral_freeze (Pr.map N) (𝒳 := GSpace hT.measurableSpace)
      (F := fun p : GSpace hT.measurableSpace × Measure (CycS I d β) =>
        F (p.1, envWalk p.2 (δ p.1))) (hGm hF)
    exact this
  · intro F hF
    have := hfr (hGm hF)
    beta_reduce at this
    refine Eq.trans (lintegral_congr_ae (ae_restrict_of_ae (hYae.mono fun ω h => ?_))) this
    show F (ω, envWalk (tildeMeasure N N' Rg ω) (δ ω)) = F (ω, envWalk (Ytil ω) (δ ω))
    rw [h]
  · intro A hA Γ hΓ Ω' _ Pr' M hM
    have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
    have hmapW : @Measurable _ _ (hT.measurableSpace.prod inferInstance) _
        (fun q : Ω × (ℝ≥0 → Fin d → ℤ) => fun s : ℝ≥0 => q.2 s - (δ q.1).start) := by
      have hfst' : @Measurable _ _ (hT.measurableSpace.prod inferInstance) hT.measurableSpace
          (Prod.fst : Ω × (ℝ≥0 → Fin d → ℤ) → Ω) := @measurable_fst _ _ hT.measurableSpace _
      have hsnd' : @Measurable _ _ (hT.measurableSpace.prod inferInstance) _
          (Prod.snd : Ω × (ℝ≥0 → Fin d → ℤ) → ℝ≥0 → Fin d → ℤ) :=
        @measurable_snd _ _ hT.measurableSpace _
      let : MeasurableSpace (Ω × (ℝ≥0 → Fin d → ℤ)) := hT.measurableSpace.prod inferInstance
      refine measurable_pi_iff.2 fun s => ?_
      have hst : @Measurable _ _ (hT.measurableSpace.prod inferInstance) _
          (fun q : Ω × (ℝ≥0 → Fin d → ℤ) => (δ q.1).start) :=
        (measurable_fst.comp measurable_snd).comp (hδ.comp hfst')
      exact ((measurable_pi_apply s).comp hsnd').sub hst
    set S : Set (Ω × (ℝ≥0 → Fin d → ℤ)) :=
      {q | q.1 ∈ A ∧ (fun s : ℝ≥0 => q.2 s - (δ q.1).start) ∈ Γ} with hS
    have hSm : @MeasurableSet _ (hT.measurableSpace.prod inferInstance) S := by
      have hfst' : @Measurable _ _ (hT.measurableSpace.prod inferInstance) hT.measurableSpace
          (Prod.fst : Ω × (ℝ≥0 → Fin d → ℤ) → Ω) := @measurable_fst _ _ hT.measurableSpace _
      exact (hfst' hA).inter (hmapW hΓ)
    set F : Ω × (ℝ≥0 → Fin d → ℤ) → ℝ≥0∞ := S.indicator 1 with hF
    have hFm : Measurable[hT.measurableSpace.prod inferInstance] F := by
      refine Measurable.indicator ?_ hSm
      exact measurable_const
    have hYw : Measurable fun ω => envWalk (Ytil ω) (δ ω) :=
      (measurable_envWalk (I := I) (d := d) (β := β)).comp
        (hY.prodMk (hδ.mono hT.measurableSpace_le le_rfl))
    have hS' : MeasurableSet {ω | ω ∈ A ∧ (fun s : ℝ≥0 => envWalk (Ytil ω) (δ ω) s -
        (δ ω).start) ∈ Γ} := by
      refine hAm.inter ?_
      have : Measurable fun ω => fun s : ℝ≥0 => envWalk (Ytil ω) (δ ω) s - (δ ω).start := by
        refine measurable_pi_iff.2 fun s => ?_
        exact ((measurable_pi_apply s).comp hYw).sub
          ((measurable_fst.comp measurable_snd).comp
            (hδ.mono hT.measurableSpace_le le_rfl))
      exact this hΓ
    have e0 : A ∩ {ω | T ω ≠ ⊤} ∩ {ω | (fun s : ℝ≥0 =>
          envWalk (tildeMeasure N N' Rg ω) (δ ω) s - (δ ω).start) ∈ Γ} =ᵐ[Pr]
        {ω | ω ∈ A ∧ (fun s : ℝ≥0 => envWalk (Ytil ω) (δ ω) s - (δ ω).start) ∈ Γ} ∩ E := by
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [hYae] with ω hω
      simp only [mem_inter_iff, mem_ofPred_eq, hEdef, hω]
      tauto
    have e1 : Pr (A ∩ {ω | T ω ≠ ⊤} ∩ {ω | (fun s : ℝ≥0 =>
          envWalk (tildeMeasure N N' Rg ω) (δ ω) s - (δ ω).start) ∈ Γ}) =
        ∫⁻ ω in E, F (ω, envWalk (Ytil ω) (δ ω)) ∂Pr := by
      rw [measure_congr e0, ← Measure.restrict_apply' hEm, ← lintegral_indicator_one hS']
      refine lintegral_congr fun ω => ?_
      show _ = S.indicator 1 (ω, envWalk (Ytil ω) (δ ω))
      by_cases h : ω ∈ A ∧ (fun s : ℝ≥0 => envWalk (Ytil ω) (δ ω) s - (δ ω).start) ∈ Γ
      · rw [Set.indicator_of_mem (s := S) (by exact h), Set.indicator_of_mem (by exact h)]
        rfl
      · rw [Set.indicator_of_notMem (s := S) (by exact h), Set.indicator_of_notMem (by exact h)]
    have hlaw : ∀ ω, ∫⁻ ν, F (ω, envWalk ν (δ ω)) ∂(Pr.map N) =
        A.indicator (fun _ => Pr' {ω' | walkMap (M ω') ∈ Γ}) ω := by
      intro ω
      by_cases hω : ω ∈ A
      · have hWm : Measurable fun ν : Measure (CycS I d β) =>
            fun s : ℝ≥0 => envWalk ν (δ ω) s - (δ ω).start := by
          refine measurable_pi_iff.2 fun s => ?_
          have := (measurable_pi_apply s).comp
            ((measurable_envWalk (I := I) (d := d) (β := β)).comp
              (measurable_id.prodMk (measurable_const (a := δ ω))))
          exact this.sub_const _
        have : (fun ν : Measure (CycS I d β) => F (ω, envWalk ν (δ ω))) =
            ((fun ν : Measure (CycS I d β) =>
              fun s : ℝ≥0 => envWalk ν (δ ω) s - (δ ω).start) ⁻¹' Γ).indicator 1 := by
          funext ν
          show S.indicator 1 (ω, envWalk ν (δ ω)) = _
          by_cases h : (fun s : ℝ≥0 => envWalk ν (δ ω) s - (δ ω).start) ∈ Γ
          · rw [Set.indicator_of_mem (s := S) (by exact ⟨hω, h⟩), Set.indicator_of_mem (by exact h)]
            rfl
          · rw [Set.indicator_of_notMem (s := S) (by exact fun h' => h h'.2),
              Set.indicator_of_notMem (by exact h)]
        rw [this, lintegral_indicator_one (hWm hΓ), Set.indicator_of_mem hω,
          Measure.map_apply hN.measurable (hWm hΓ)]
        have := law_envWalk hN hM (δ ω)
        have h2 := congrArg (fun m : Measure (ℝ≥0 → Fin d → ℤ) => m Γ) this
        beta_reduce at h2
        have hm1 : Measurable fun ω'' => fun s : ℝ≥0 => envWalk (N ω'') (δ ω) s - (δ ω).start := by
          refine measurable_pi_iff.2 fun s => ?_
          have := (measurable_pi_apply s).comp
            ((measurable_envWalk (I := I) (d := d) (β := β)).comp
              (hN.measurable.prodMk (measurable_const (a := δ ω))))
          exact this.sub_const _
        have hm2 : Measurable fun ω' => walkMap (M ω') := measurable_walkMap.comp hM.measurable
        rw [Measure.map_apply hm1 hΓ, Measure.map_apply hm2 hΓ] at h2
        exact h2
      · have : (fun ν : Measure (CycS I d β) => F (ω, envWalk ν (δ ω))) = fun _ => 0 := by
          funext ν
          show S.indicator 1 (ω, envWalk ν (δ ω)) = 0
          exact Set.indicator_of_notMem (s := S) (fun h' => hω h'.1) _
        rw [this, Set.indicator_of_notMem hω]
        simp
    rw [e1, hfr (hGm hFm)]
    simp_rw [hlaw]
    rw [lintegral_indicator_const hAm, Measure.restrict_apply' hEm, mul_comm]

/-- The discrepancy `D_T = {x ∈ R_T : N'({x}) ≠ cycRM(cycRec^𝒫(T))({x})}`: the points of the explored
region where the fresh environment and the known rings differ. -/
def cycDiscrepancy (P : CycPlan I d β) (N N' : Ω → Measure (CycS I d β)) (T : Ω → WithTop ℝ≥0)
    (ω : Ω) : Set (CycS I d β) :=
  {x | x ∈ cycRegionStop P (cycNgood N) T ω ∧
    N' ω {x} ≠ (cycRecStop P (cycNgood N) T ω).rm β {x}}

include hN hN' hI1 hI2 in
/-- **plan-level coupling after a stopping time** (c): agreement up to a discrepancy. Almost surely on `{T < ∞}`, for
every `r ≥ 0` such that the explored region of the world-line `(δ, r, P'(· ∧ r))` does not meet the
discrepancy `D_T`, the paths `P' = P^{Ñ_T}_δ` and `P = P^N_δ` agree on `[0, r]`; in particular
this holds when that region does not meet `R_T`. -/
theorem cyc_plan_coupling_agree (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    (δ : Ω → CycData I d) :
    ∀ᵐ ω ∂Pr, T ω ≠ ⊤ → ∀ r : ℝ≥0,
      (Disjoint (CycEntry.region β
          ((δ ω, (envPath (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) (δ ω)).cut r) :
            CycEntry I d)) (cycDiscrepancy P N N' T ω) ∨
        Disjoint (CycEntry.region β
          ((δ ω, (envPath (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) (δ ω)).cut r) :
            CycEntry I d)) (cycRegionStop P (cycNgood N) T ω)) →
      ∀ s : ℝ≥0, s ≤ r →
        envWalk (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) (δ ω) s =
          envWalk (N ω) (δ ω) s := by
  obtain ⟨hE, -, hregset, hae, -, hb, -, -, -⟩ :=
    cyc_multi_exploration_a P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT
  have hPr := hN.isProbabilityMeasure
  set Rg := cycRegionStop P (cycNgood N) T with hRg
  have hgoodN := CycSchemeEnv.ae_cycGood' hN
  have hgoodTilde : ∀ᵐ ω ∂Pr, T ω ≠ ⊤ → CycGood (tildeMeasure N N' Rg ω) := by
    have hFm : MeasurableSet {ν : Measure (CycS I d β) | ¬ CycGood ν} :=
      measurableSet_cycGood.compl
    have h0 := hb MeasurableSet.univ hFm
    have h1 : (Pr.map N) {ν : Measure (CycS I d β) | ¬ CycGood ν} = 0 := by
      rw [Measure.map_apply hN.measurable hFm]
      exact measure_eq_zero_iff_ae_notMem.2 (hgoodN.mono fun ω h hn => hn h)
    rw [h1, mul_zero] at h0
    have := measure_eq_zero_iff_ae_notMem.1 h0
    filter_upwards [this] with ω hω hTω
    by_contra hng
    exact hω ⟨⟨mem_univ _, hTω⟩, hng⟩
  filter_upwards [hgoodN, hae, hgoodTilde] with ω hgN hrm hgT hTω r hdisj s hsr
  have hRm : MeasurableSet (Rg ω) := measurableSet_cycRegionStop P (N := cycNgood N) T ω
  have hdisj' : Disjoint (CycEntry.region β
      ((δ ω, (envPath (tildeMeasure N N' Rg ω) (δ ω)).cut r) : CycEntry I d))
      (cycDiscrepancy P N N' T ω) := by
    rcases hdisj with h | h
    · exact h
    · refine h.mono_right ?_
      intro x hx; exact hx.1
  have hrm' := hrm hTω
  have hag : ∀ x ∈ CycEntry.region β
      ((δ ω, (envPath (tildeMeasure N N' Rg ω) (δ ω)).cut r) : CycEntry I d),
      tildeMeasure N N' Rg ω {x} = N ω {x} := by
    intro x hx
    have hxD : x ∉ cycDiscrepancy P N N' T ω := fun h => Set.disjoint_left.1 hdisj' hx h
    unfold tildeMeasure
    rw [Measure.add_apply, Measure.restrict_apply (measurableSet_singleton x),
      Measure.restrict_apply (measurableSet_singleton x)]
    by_cases hxR : x ∈ Rg ω
    · have hN'x : N' ω {x} = (cycRecStop P (cycNgood N) T ω).rm β {x} := by
        by_contra hne
        exact hxD ⟨hxR, hne⟩
      have h1 : {x} ∩ (Rg ω)ᶜ = ∅ := Set.singleton_inter_eq_empty.2 (not_not.2 hxR)
      have h2 : {x} ∩ Rg ω = {x} := Set.inter_eq_left.2 (Set.singleton_subset_iff.2 hxR)
      have h3 : N ω {x} = (cycRecStop P (cycNgood N) T ω).rm β {x} := by
        have := congrArg (fun m : Measure (CycS I d β) => m {x}) hrm'
        simp only [Measure.restrict_apply (measurableSet_singleton x), h2] at this
        exact this
      rw [h1, h2, measure_empty, zero_add, hN'x, h3]
    · have h1 : {x} ∩ (Rg ω)ᶜ = {x} := Set.inter_eq_left.2 (Set.singleton_subset_iff.2 hxR)
      have h2 : {x} ∩ Rg ω = ∅ := Set.singleton_inter_eq_empty.2 hxR
      rw [h1, h2, measure_empty, add_zero]
  have hgs : Good (cycSlice (δ ω).copy (tildeMeasure N N' Rg ω)) := hgT hTω _
  have hgn : Good (cycSlice (δ ω).copy (N ω)) := hgN _
  have := envFn_eq_of_agree hgs hgn hag s hsr
  unfold envWalk
  rw [ite_eq_left (hgT hTω), ite_eq_left hgN, this]

end ElboimSly.Cyclic

end
