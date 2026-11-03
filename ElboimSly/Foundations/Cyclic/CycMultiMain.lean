/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiStopT
public import ElboimSly.Foundations.Cyclic.CycMultiDriven
public import ElboimSly.Foundations.Cyclic.CycMultiRM
public import ElboimSly.Foundations.Cyclic.CycMultiCond
public import ElboimSly.Foundations.Cyclic.CycMultiGood
public import Mathlib

/-!
# Summary of the Lean statements

Several walks explored one after another.

**(a)** `cyc_multi_exploration_a` (unconditional; bundles measurability of `{T<∞}`, `cycRec(T)`,
`R_T`, `N|_{R_T} = cycRM(cycRec(T))` a.s., the independence forms and the conditional forms; the
records are those of `cycNgood N`, i.e. `N` with fixed values off `{N ∈ Good}`, equal to `N` a.s.).
Its measurability-hypothesis helper is `cyc_multi_exploration_a_of_meas`, which reads: for a plan `𝒫` with `0 < K`, `N, N' ∼ PPP(μ)` on `I × Ed × 𝕋`
and a `σ`-algebra `𝒢₀` with `𝒢₀, σ(N), σ(N')` independent (as `Indep 𝒢₀ σ(N)` and
`Indep σ(N') (𝒢₀ ∨ σ(N))`), the joint exploration filtration `ℱ^𝒫_s` (`multiFilt`, i.e.
`cycFiltration`), every `(ℱ^𝒫_s)`-stopping time `T : Ω → WithTop ℝ≥0` and every `A ∈ ℱ^𝒫_T`:
`{T < ∞} ∈ ℱ^𝒫_T`, and
`P(A ∩ {T < ∞} ∩ {Ñ_T ∈ F}) = P(A ∩ {T < ∞}) Π_μ(F)` for `Ñ_T = N|_{S ∖ R_T} + N'|_{R_T}`
(`tildeMeasure N N' (cycRegionStop P N T)`) and `Π_μ = Law(N)`. If `P(T < ∞) = 1` this reads
`P(A ∩ {Ñ_T ∈ F}) = P(A) Π_μ(F)`: `Ñ_T` has the law of `N` and is independent of `ℱ^𝒫_T`.

**(b)** `cyc_multi_driven` (`CycMultiDriven`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β)
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS I d β)}
  (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)

include hN hN' hI1 hI2 in
/-- Several walks explored one after another (a), independence part, *conditional helper*: it assumes
that the final record `ω ↦ ρ^𝒫(N ω)` is measurable (needed to define the filtration `multiFilt`).
The source-named theorem `cyc_multi_exploration_a` removes this hypothesis. -/
theorem cyc_multi_exploration_a_of_meas (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ)
    (hR : Measurable fun ω => P.envFinal (N ω)) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (multiFilt 𝒢₀ P.junk Pr h𝒢 (fun ω => P.envFinal (N ω)) hR) T) :
    MeasurableSet[hT.measurableSpace] {ω | T ω ≠ ⊤} ∧
    (∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A →
      ∀ {F : Set (Measure (CycS I d β))}, MeasurableSet F →
        Pr (A ∩ {ω | T ω ≠ ⊤} ∩ {ω | tildeMeasure N N' (cycRegionStop P N T) ω ∈ F}) =
          Pr (A ∩ {ω | T ω ≠ ⊤}) * (Pr.map N) F) ∧
    (Pr {ω | T ω ≠ ⊤} = 1 → ∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A →
      ∀ {F : Set (Measure (CycS I d β))}, MeasurableSet F →
        Pr (A ∩ {ω | tildeMeasure N N' (cycRegionStop P N T) ω ∈ F}) = Pr A * (Pr.map N) F) := by
  have := hN.isProbabilityMeasure
  refine ⟨measurableSet_ne_top hT, fun {A} hA {F} hF => multi_stopped 𝒢₀ P hN hN' hI1 hI2 hK h𝒢 hR hT hA hF, ?_⟩
  intro h1 A hA F hF
  have hm : MeasurableSet {ω | T ω ≠ ⊤} := hT.measurableSpace_le _ (measurableSet_ne_top hT)
  have hae : {ω | T ω ≠ ⊤} =ᵐ[Pr] (univ : Set Ω) := by
    have : Pr {ω | T ω ≠ ⊤}ᶜ = 0 := by
      rw [prob_compl_eq_one_sub hm, h1]; simp
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with ω hω
    simpa using hω
  have := multi_stopped 𝒢₀ P hN hN' hI1 hI2 hK h𝒢 hR hT hA hF
  rw [measure_congr (Filter.EventuallyEqSet.inter (Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl hae)
    Filter.EventuallyEq.rfl), measure_congr (Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl hae),
    ] at this
  simpa only [inter_univ] using this

/-- The joint exploration filtration `ℱ^𝒫_s = 𝒢₀ ∨ σ(Rec^𝒫(s') : s' ≤ s) ∨ 𝒩` of world-lines of a plan; joint exploration filtration (c),
for the records of `N` "given fixed values off `{N ∈ Good}`" (`cycNgood N`): the final record
`ω ↦ ρ^𝒫(cycNgood N ω)` is measurable, so no measurability hypothesis is needed. -/
noncomputable def cycMultiFilt (hNm : Measurable N) (h𝒢 : 𝒢₀ ≤ mΩ) (Pr : Measure Ω) :
    Filtration ℝ≥0 mΩ :=
  multiFilt 𝒢₀ P.junk Pr h𝒢 (fun ω => P.envFinal (cycNgood N ω))
    (measurable_envFinal_cycNgood P hNm)

include hN hN' hI1 hI2 in
/-- Several walks explored one after another (a), complete and unconditional: the Markov property at
stopping times of the joint exploration, in the environment picture. For every
`(ℱ^𝒫_s)`-stopping time `T` (`ℱ^𝒫` as in `cycMultiFilt`, built from `cycNgood N`; `R_T`,
`cycRec^𝒫(T)` are those of `cycNgood N`, which equals `N` almost surely):
1. `{T < ∞} ∈ ℱ_T`;
2. `cycRec^𝒫(T)` is `ℱ_T`-measurable (a total function; junk value `Trunc_0` on `{T = ∞}`);
3. `{(ω, x) : x ∈ R_T(ω)} ∈ ℱ_T ⊗ ℬ(𝒮)` (`R_T = ∅` on `{T = ∞}`);
4. almost surely on `{T < ∞}`, `N|_{R_T} = cycRM(cycRec^𝒫(T))`; and `cycRM(cycRec^𝒫(T))` is
   `ℱ_T`-measurable;
5. for `A ∈ ℱ_T` and `F ∈ 𝔊`: `P(A ∩ {T<∞} ∩ {Ñ_T ∈ F}) = P(A ∩ {T<∞}) Π_μ(F)`, and without
   `{T<∞}` if `P(T < ∞) = 1` (then `Ñ_T ∼ PPP(μ)` independent of `ℱ_T`);
6. the conditional form `E[1_{T<∞} F(·, N|_{𝒮∖R_T})] = E[1_{T<∞} ∫ F(·, ν|_{𝒮∖R_T}) Π_μ(dν)]` for
   every `ℱ_T ⊗ 𝔊`-measurable `F ≥ 0`, and without `1_{T<∞}` if `P(T<∞) = 1`.
Here `Π_μ = Law(N)` and `Ñ_T = N|_{𝒮∖R_T} + N'|_{R_T}`. -/
theorem cyc_multi_exploration_a (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ)
    {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T) :
    MeasurableSet[hT.measurableSpace] {ω | T ω ≠ ⊤} ∧
    Measurable[hT.measurableSpace] (cycRecStop P (cycNgood N) T) ∧
    MeasurableSet[hT.measurableSpace.prod inferInstance]
      {p : Ω × CycS I d β | p.2 ∈ cycRegionStop P (cycNgood N) T p.1} ∧
    (∀ᵐ ω ∂Pr, T ω ≠ ⊤ → (N ω).restrict (cycRegionStop P (cycNgood N) T ω) =
      (cycRecStop P (cycNgood N) T ω).rm β) ∧
    Measurable[hT.measurableSpace] (fun ω => (cycRecStop P (cycNgood N) T ω).rm β) ∧
    (∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A →
      ∀ {F : Set (Measure (CycS I d β))}, MeasurableSet F →
        Pr (A ∩ {ω | T ω ≠ ⊤} ∩
            {ω | tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω ∈ F}) =
          Pr (A ∩ {ω | T ω ≠ ⊤}) * (Pr.map N) F) ∧
    (Pr {ω | T ω ≠ ⊤} = 1 → ∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A →
      ∀ {F : Set (Measure (CycS I d β))}, MeasurableSet F →
        Pr (A ∩ {ω | tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω ∈ F}) =
          Pr A * (Pr.map N) F) ∧
    (∀ {F : Ω × Measure (CycS I d β) → ℝ≥0∞},
      Measurable[hT.measurableSpace.prod inferInstance] F →
        ∫⁻ ω in {ω | T ω ≠ ⊤},
            F (ω, (N ω).restrict (cycRegionStop P (cycNgood N) T ω)ᶜ) ∂Pr =
          ∫⁻ ω in {ω | T ω ≠ ⊤},
            ∫⁻ ν, F (ω, ν.restrict (cycRegionStop P (cycNgood N) T ω)ᶜ) ∂(Pr.map N) ∂Pr) ∧
    (Pr {ω | T ω ≠ ⊤} = 1 → ∀ {F : Ω × Measure (CycS I d β) → ℝ≥0∞},
      Measurable[hT.measurableSpace.prod inferInstance] F →
        ∫⁻ ω, F (ω, (N ω).restrict (cycRegionStop P (cycNgood N) T ω)ᶜ) ∂Pr =
          ∫⁻ ω, ∫⁻ ν, F (ω, ν.restrict (cycRegionStop P (cycNgood N) T ω)ᶜ) ∂(Pr.map N) ∂Pr) := by
  have hN₂ := isPoissonPointProcess_cycNgood hN
  have hae := ae_cycNgood_eq hN
  have hI1₂ : Indep 𝒢₀ (MeasurableSpace.comap (cycNgood N) inferInstance) Pr :=
    indep_of_ae_sets hI1 (exists_ae_set_comap' hae)
  have hI2₂ : Indep (MeasurableSpace.comap N' inferInstance)
      (𝒢₀ ⊔ MeasurableSpace.comap (cycNgood N) inferInstance) Pr :=
    indep_of_ae_sets hI2 (exists_ae_set_comap hae 𝒢₀)
  have hR₂ := measurable_envFinal_cycNgood P hN.measurable
  have hRf : ∀ s, Measurable[cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr s]
      fun ω => CycRec.trunc s (P.envFinal (cycNgood N ω)) :=
    measurable_trunc_multiFilt P 𝒢₀ h𝒢 Pr hR₂
  have hmap : Pr.map (cycNgood N) = Pr.map N := Measure.map_congr hae
  have htilde : ∀ (S : Set Ω) (F : Set (Measure (CycS I d β))),
      Pr (S ∩ {ω | tildeMeasure (cycNgood N) N' (cycRegionStop P (cycNgood N) T) ω ∈ F}) =
        Pr (S ∩ {ω | tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω ∈ F}) := by
    intro S F
    refine measure_congr (Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl ?_)
    refine Filter.eventuallyEqSet_iff.2 (hae.mono fun ω h => ?_)
    simp only [mem_ofPred_eq, tildeMeasure, h]
  have hfull := cyc_multi_exploration_a_of_meas P 𝒢₀ hN₂ hN' hI1₂ hI2₂ hK h𝒢 hR₂ hT
  refine ⟨hfull.1, measurable_cycRecStop hRf hT, measurableSet_regionStop hRf hT, ?_,
    measurable_rm_cycRecStop P hRf hT, ?_, ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_cycRegionStop P hN₂ T, hae] with ω h1 h2 hTω
    rw [← h2]
    exact h1 hTω
  · intro A hA F hF
    have := hfull.2.1 hA hF
    rwa [htilde, hmap] at this
  · intro h1 A hA F hF
    have := hfull.2.2 h1 hA hF
    rwa [htilde, hmap] at this
  · intro F hF
    have := multi_cond_restrict P 𝒢₀ hN₂ hN' hI1₂ hI2₂ hK h𝒢 hR₂ hT hF
    rw [hmap] at this
    rw [← this]
    refine lintegral_congr_ae ?_
    exact ae_restrict_of_ae (hae.mono fun ω h => by beta_reduce; rw [h])
  · intro h1 F hF
    have := multi_cond_of_ae_fin P 𝒢₀ hN₂ hN' hI1₂ hI2₂ hK h𝒢 hR₂ hT h1 hF
    rw [hmap] at this
    rw [← this]
    refine lintegral_congr_ae ?_
    exact hae.mono fun ω h => by beta_reduce; rw [h]

end ElboimSly.Cyclic

end
