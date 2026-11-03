/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiMain
public import ElboimSly.Foundations.Cyclic.CycMarkovRM
public import Mathlib

/-!
# ES22 §4: the resampling formula

Resampling formula.

For an exploration plan `𝒫`, `N ∼ PPP(μ)`, an a.s. finite stopping time `T` of the joint
exploration filtration `ℱ_s` (`cycMultiFilt`), with region `R_T` and record `ρ_T`:

* `es4_resample_a`: for every `ℱ_T ⊗ 𝔊`-measurable `F ≥ 0`, the function
  `G(ω) = ∫ F(ω, RM(ρ_T) + ν|_{S∖R_T}) Π_μ(dν)` is `ℱ_T`-measurable and
  `E[1_A F(·, N)] = E[1_A G]` for all `A ∈ ℱ_T` (this is the conditional expectation
  `E[F(·, N) | ℱ_T] = G` in integral form, for `[0, ∞]`-valued `F`);
* `es4_resample_b`: the event form `P(N ∈ B | ℱ_T) = Φ_B(ρ_T)` with `Φ_B` the explicit function
  `resampleProb` of the record, and the mathlib `condExp` statement;
* `es4_resample_c`: localization, since `Φ_B` depends on the record only through the pair
  `(RM(ρ), R(ρ))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β)
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS I d β)}

/-- `Φ(RM, R)(B) = Π_μ{ν : RM + ν|_{S∖R} ∈ B}`: the conditional probability of `{N ∈ B}` given
the explored region `R` and the ring measure `RM`. -/
noncomputable def resampleProb (Λ : Measure (Measure (CycS I d β))) (M : Measure (CycS I d β))
    (R : Set (CycS I d β)) (B : Set (Measure (CycS I d β))) : ℝ≥0∞ :=
  Λ {ν | M + ν.restrict Rᶜ ∈ B}

/-- The right side of the resampling formula (a): `∫ F(ω, RM(ρ_T) + ν|_{S∖R_T}) Π_μ(dν)`. -/
noncomputable def resampleInt (Pr : Measure Ω) (N : Ω → Measure (CycS I d β))
    (T : Ω → WithTop ℝ≥0) (F : Ω × Measure (CycS I d β) → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ ν, F (ω, (cycRecStop P (cycNgood N) T ω).rm β +
    ν.restrict (cycRegionStop P (cycNgood N) T ω)ᶜ) ∂(Pr.map N)

section main

variable (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)

include hN hN' hI1 hI2 in
/-- **resampling formula (a)**, integral form. -/
theorem es4_resample_a (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    (hfin : Pr {ω | T ω ≠ ⊤} = 1) {F : Ω × Measure (CycS I d β) → ℝ≥0∞}
    (hF : Measurable[hT.measurableSpace.prod inferInstance] F) :
    Measurable[hT.measurableSpace] (resampleInt P Pr N T F) ∧
      ∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A →
        ∫⁻ ω in A, F (ω, N ω) ∂Pr = ∫⁻ ω in A, resampleInt P Pr N T F ω ∂Pr := by
  have hPr := hN.isProbabilityMeasure
  obtain ⟨-, hrec, hZ, hrm_ae, hrm, -, -, -, hcond⟩ :=
    cyc_multi_exploration_a P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT
  set Rg := cycRegionStop P (cycNgood N) T with hRg
  set rmf : Ω → Measure (CycS I d β) := fun ω => (cycRecStop P (cycNgood N) T ω).rm β with hrmf
  have hrmG : Measurable (fun x : GSpace hT.measurableSpace => rmf x) := hrm
  have hFG : Measurable (fun p : GSpace hT.measurableSpace × Measure (CycS I d β) => F p) := hF
  set Zset : Set (GSpace hT.measurableSpace × CycS I d β) := {p | p.2 ∈ Rg p.1} with hZset
  have hZG : MeasurableSet Zset := hZ
  set μ := cycIntensity I d β with hμ
  have hH : Measurable (fun p : GSpace hT.measurableSpace × Measure (CycS I d β) =>
      F (p.1, rmf p.1 + (tau μ p.2).restrict (Prod.mk p.1 ⁻¹' {p : GSpace hT.measurableSpace × CycS I d β |
        p.2 ∈ Rg p.1}ᶜ))) :=
    hFG.comp (measurable_fst.prodMk (measurable_add_measure.comp
      ((hrmG.comp measurable_fst).prodMk (measurable_tau_restrict_section μ hZG.compl))))
  have hG : Measurable (fun x : GSpace hT.measurableSpace => ∫⁻ y, F (x, rmf x +
      (tau μ y).restrict (Prod.mk x ⁻¹' Zsetᶜ))
      ∂(Pr.map N)) := by
    have : SFinite (Pr.map N) := inferInstance
    exact measurable_lintegral_freeze (Pr.map N) hH
  have hGeq : resampleInt P Pr N T F = fun x : GSpace hT.measurableSpace => ∫⁻ y, F (x, rmf x +
      (tau μ y).restrict (Prod.mk x ⁻¹' Zsetᶜ))
      ∂(Pr.map N) := by
    funext ω
    unfold resampleInt
    refine lintegral_congr_ae ?_
    filter_upwards [(ae_map_iff hN.measurable.aemeasurable
      (measurableSet_lfSet μ)).2 hN.ae_mem_lfSet] with y hy
    rw [tau_of_mem _ hy]
    rfl
  refine ⟨by rw [hGeq]; exact hG, ?_⟩
  intro A hA
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  have hF2' : Measurable (fun p : GSpace hT.measurableSpace × Measure (CycS I d β) => F (p.1, rmf p.1 + p.2)) :=
    hFG.comp (measurable_fst.prodMk (measurable_add_measure.comp
      ((hrmG.comp measurable_fst).prodMk measurable_snd)))
  have hF2 : Measurable[hT.measurableSpace.prod inferInstance] (fun p : GSpace hT.measurableSpace × Measure (CycS I d β) =>
      (Prod.fst ⁻¹' (A : Set (GSpace hT.measurableSpace))).indicator
        (fun p : GSpace hT.measurableSpace × Measure (CycS I d β) => F (p.1, rmf p.1 + p.2)) p) :=
    hF2'.indicator (measurable_fst hA)
  have key := hcond hfin hF2
  have hlhs : ∫⁻ ω, (Prod.fst ⁻¹' (A : Set (GSpace hT.measurableSpace))).indicator
        (fun p : GSpace hT.measurableSpace × Measure (CycS I d β) => F (p.1, rmf p.1 + p.2))
        (ω, (N ω).restrict (Rg ω)ᶜ) ∂Pr = ∫⁻ ω in A, F (ω, N ω) ∂Pr := by
    rw [← lintegral_indicator hAm]
    refine lintegral_congr_ae ?_
    have hne : ∀ᵐ ω ∂Pr, T ω ≠ ⊤ := by
      have hm : MeasurableSet {ω | T ω ≠ ⊤} := hT.measurableSpace_le _ (measurableSet_ne_top hT)
      have h0 := (prob_compl_eq_zero_iff hm).2 hfin
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
      simpa using hω
    filter_upwards [hrm_ae, hne] with ω h1 h2
    have h3 := h1 h2
    by_cases hω : ω ∈ A
    · simp only [Set.indicator, Set.mem_preimage, hω, ite_true]
      congr 2
      have h3' : rmf ω = (N ω).restrict (Rg ω) := h3.symm
      rw [h3']
      exact Measure.restrict_add_restrict_compl (measurableSet_cycRegionStop P (N := cycNgood N) T ω)
    · simp [Set.indicator, hω]
  have hrhs : ∫⁻ ω, ∫⁻ ν, (Prod.fst ⁻¹' (A : Set (GSpace hT.measurableSpace))).indicator
        (fun p : GSpace hT.measurableSpace × Measure (CycS I d β) => F (p.1, rmf p.1 + p.2))
        (ω, ν.restrict (Rg ω)ᶜ) ∂(Pr.map N) ∂Pr = ∫⁻ ω in A, resampleInt P Pr N T F ω ∂Pr := by
    rw [← lintegral_indicator hAm]
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ A
    · simp [Set.indicator, hω, resampleInt]
      rfl
    · simp [Set.indicator, hω]
  rw [← hlhs, key, hrhs]

include hN hN' hI1 hI2 in
/-- **resampling formula (b)**, event form: for a measurable set `B` of measures, the function
`ω ↦ Φ_B(ρ_T) = resampleProb Π_μ RM(ρ_T) R_T B` is `ℱ_T`-measurable and
`P(A ∩ {N ∈ B}) = ∫_A Φ_B(ρ_T) dP` for all `A ∈ ℱ_T`; that is,
`P(N ∈ B | ℱ_T) = Φ_B(ρ_T)` almost surely. -/
theorem es4_resample_b (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    (hfin : Pr {ω | T ω ≠ ⊤} = 1) {B : Set (Measure (CycS I d β))} (hB : MeasurableSet B) :
    Measurable[hT.measurableSpace] (fun ω => resampleProb (Pr.map N)
        ((cycRecStop P (cycNgood N) T ω).rm β) (cycRegionStop P (cycNgood N) T ω) B) ∧
      ∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A →
        Pr (A ∩ {ω | N ω ∈ B}) = ∫⁻ ω in A, resampleProb (Pr.map N)
          ((cycRecStop P (cycNgood N) T ω).rm β) (cycRegionStop P (cycNgood N) T ω) B ∂Pr := by
  have hF : Measurable[hT.measurableSpace.prod inferInstance]
      (fun p : Ω × Measure (CycS I d β) => B.indicator (fun _ => (1 : ℝ≥0∞)) p.2) :=
    (measurable_const.indicator hB).comp (@measurable_snd _ _ hT.measurableSpace _)
  obtain ⟨h1, h2⟩ := es4_resample_a P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT hfin hF
  have hΦ : ∀ ω, resampleInt P Pr N T
      (fun p : Ω × Measure (CycS I d β) => B.indicator (fun _ => (1 : ℝ≥0∞)) p.2) ω =
      resampleProb (Pr.map N) ((cycRecStop P (cycNgood N) T ω).rm β)
        (cycRegionStop P (cycNgood N) T ω) B := by
    intro ω
    unfold resampleInt resampleProb
    have hm : Measurable fun ν : Measure (CycS I d β) =>
        (cycRecStop P (cycNgood N) T ω).rm β +
          ν.restrict (cycRegionStop P (cycNgood N) T ω)ᶜ :=
      measurable_add_measure.comp (measurable_const.prodMk
        (measurable_restrict_set (measurableSet_cycRegionStop P (N := cycNgood N) T ω).compl))
    have : (fun ν : Measure (CycS I d β) => B.indicator (fun _ => (1 : ℝ≥0∞))
        ((cycRecStop P (cycNgood N) T ω).rm β +
          ν.restrict (cycRegionStop P (cycNgood N) T ω)ᶜ)) =
        ((fun ν => (cycRecStop P (cycNgood N) T ω).rm β +
          ν.restrict (cycRegionStop P (cycNgood N) T ω)ᶜ) ⁻¹' B).indicator 1 := by
      funext ν; simp only [Set.indicator]; rfl
    simp only [this]
    exact lintegral_indicator_one (hm hB)
  have hfun : (fun ω => resampleProb (Pr.map N) ((cycRecStop P (cycNgood N) T ω).rm β)
      (cycRegionStop P (cycNgood N) T ω) B) = resampleInt P Pr N T
      (fun p : Ω × Measure (CycS I d β) => B.indicator (fun _ => (1 : ℝ≥0∞)) p.2) :=
    funext fun ω => (hΦ ω).symm
  refine ⟨by rw [hfun]; exact h1, fun {A} hA => ?_⟩
  have := h2 hA
  simp only [hΦ] at this
  have hNm : MeasurableSet (N ⁻¹' B) := hN.measurable hB
  rw [← this]
  have e : (fun ω => B.indicator (fun _ => (1 : ℝ≥0∞)) (N ω)) = (N ⁻¹' B).indicator 1 := by
    funext ω; simp only [Set.indicator]; rfl
  simp only [e]
  rw [lintegral_indicator_one hNm, Measure.restrict_apply hNm, inter_comm]
  rfl

end main

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
/-- **resampling formula (c)**, localization: `Φ_B(ρ)` depends on the record only through the pair
`(RM(ρ), R(ρ))`. If two plans/stopping times have the same explored region and ring measure at a
point `ω`, their conditional probabilities `Φ_B(ρ_T)(ω)`, `Φ_B(ρ'_{T'})(ω)` coincide; combined
with `es4_resample_b` for both, `P(N ∈ B | ℱ_T) = P(N ∈ B | ℱ'_{T'})` a.s. on such an event. -/
theorem es4_resample_c {Λ : Measure (Measure (CycS I d β))} {M M' : Measure (CycS I d β)}
    {R R' : Set (CycS I d β)} (hM : M = M') (hR : R = R') (B : Set (Measure (CycS I d β))) :
    resampleProb Λ M R B = resampleProb Λ M' R' B := by
  subst hM hR; rfl

end ElboimSly.Paper

end
