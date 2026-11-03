/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMarkovRM
public import ElboimSly.Foundations.Cyclic.CycMarkovFilt
public import ElboimSly.Foundations.Cyclic.CycMultiMain
public import Mathlib

/-!
# The Markov property of the environment at walk stopping times

Markov property of the environment at walk stopping times, deduced from several walks explored one after another (a) for the one-walk plan
`𝒫_W = onePlan` on the one-copy cyclic space `Unit × S_β`.

Setting. `N, N'` are `PPP(μ_β)` on `S_β` (`ringIntensity d β`), `𝒢₀` is a `σ`-algebra with `𝒢₀`, `σ(N)`,
`σ(N')` independent (as `Indep 𝒢₀ σ(N)` and `Indep σ(N') (𝒢₀ ∨ σ(N))`), and
`ℱ_t = 𝒢₀ ∨ ℱ^W_t` (`cycMarkovFilt`), the walk being that of `markovNgood N`, i.e. `N` "given fixed
values off `{N ∈ Good}`" (equal to `N` almost surely). For an `(ℱ_t)`-stopping time `T`,
`ℛ_T = ℛ_{(0,T]}(W)` is `markovRegion N T` (`∅` on `{T = ∞}`), `Ñ = N|_{S_β ∖ ℛ_T} + N'|_{ℛ_T}`
is `tildeMeasure N N' (markovRegion N T)`, and the ring measure of the jumps of `W` on `(0,T]` is
`Measure.count.restrict (markovRings N T ω)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (RingSpace d β)}
  (hN : IsPoissonPointProcess N (ringIntensity d β) Pr)
  (hN' : IsPoissonPointProcess N' (ringIntensity d β) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)

include hN hN' hI1 hI2 in
/-- **Markov property of the environment at walk stopping times**: the Markov property of the environment at walk stopping times. For every
`(ℱ_t)`-stopping time `T : Ω → [0, ∞]`, with `ℱ_T` its stopping-time σ-algebra:
0. `{T < ∞} ∈ ℱ_T`;
1. (a) almost surely on `{T < ∞}`, `N|_{ℛ_T}` is the ring measure `Σ_x δ_x` over the points
   `x = ({W(r-), W(r)}, [r])` of the jumps of `W` at times `r ∈ (0, T]`, and this ring measure is
   `ℱ_T`-measurable; moreover `{(ω, x) : x ∈ ℛ_T(ω)} ∈ ℱ_T ⊗ ℬ(S_β)`;
2. (b) for `A ∈ ℱ_T` and measurable `F` of measures, with `Π_{μ_β} = Law(N)`:
   `P(A ∩ {T<∞} ∩ {Ñ ∈ F}) = P(A ∩ {T<∞}) Π_{μ_β}(F)`;
3. (c) if `P(T < ∞) = 1`: `P(A ∩ {Ñ ∈ F}) = P(A) Π_{μ_β}(F)` (so `Ñ ∼ PPP(μ_β)` independent of `ℱ_T`),
   and the conditional form
   `E[F(·, N|_{S_β∖ℛ_T})] = E[∫ F(·, ν|_{S_β∖ℛ_T}) Π_{μ_β}(dν)]` for every `ℱ_T ⊗ 𝔊`-measurable
   `F ≥ 0` (in the version on `{T<∞}` as well). -/
theorem cyc_markov (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMarkovFilt 𝒢₀ h𝒢 hN.measurable Pr) T) :
    MeasurableSet[hT.measurableSpace] {ω | T ω ≠ ⊤} ∧
    Measurable[hT.measurableSpace] (fun ω => markovW N ω (ElboimSly.SRW.stopReal T ω)) ∧
    (∀ᵐ ω ∂Pr, T ω ≠ ⊤ → (N ω).restrict (markovRegion N T ω) =
      Measure.count.restrict (markovRings N T ω)) ∧
    Measurable[hT.measurableSpace] (fun ω => (Measure.count.restrict (markovRings N T ω) :
      Measure (RingSpace d β))) ∧
    MeasurableSet[hT.measurableSpace.prod inferInstance]
      {p : Ω × RingSpace d β | p.2 ∈ markovRegion N T p.1} ∧
    (∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A →
      ∀ {F : Set (Measure (RingSpace d β))}, MeasurableSet F →
        Pr (A ∩ {ω | T ω ≠ ⊤} ∩ {ω | tildeMeasure N N' (markovRegion N T) ω ∈ F}) =
          Pr (A ∩ {ω | T ω ≠ ⊤}) * (Pr.map N) F) ∧
    (Pr {ω | T ω ≠ ⊤} = 1 → ∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A →
      ∀ {F : Set (Measure (RingSpace d β))}, MeasurableSet F →
        Pr (A ∩ {ω | tildeMeasure N N' (markovRegion N T) ω ∈ F}) = Pr A * (Pr.map N) F) ∧
    (∀ {F : Ω × Measure (RingSpace d β) → ℝ≥0∞},
      Measurable[hT.measurableSpace.prod inferInstance] F →
        ∫⁻ ω in {ω | T ω ≠ ⊤}, F (ω, (N ω).restrict (markovRegion N T ω)ᶜ) ∂Pr =
          ∫⁻ ω in {ω | T ω ≠ ⊤},
            ∫⁻ ν, F (ω, ν.restrict (markovRegion N T ω)ᶜ) ∂(Pr.map N) ∂Pr) ∧
    (Pr {ω | T ω ≠ ⊤} = 1 → ∀ {F : Ω × Measure (RingSpace d β) → ℝ≥0∞},
      Measurable[hT.measurableSpace.prod inferInstance] F →
        ∫⁻ ω, F (ω, (N ω).restrict (markovRegion N T ω)ᶜ) ∂Pr =
          ∫⁻ ω, ∫⁻ ν, F (ω, ν.restrict (markovRegion N T ω)ᶜ) ∂(Pr.map N) ∂Pr) := by
  have hN₁ := isPoissonPointProcess_liftU hN
  have hN₁' := isPoissonPointProcess_liftU hN'
  have hle : ∀ X : Ω → Measure (RingSpace d β),
      MeasurableSpace.comap (fun ω => liftU (X ω)) inferInstance ≤
        MeasurableSpace.comap X inferInstance := by
    intro X
    rw [show (fun ω => liftU (X ω)) = liftU ∘ X from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono measurable_liftU.comap_le
  have hI1₁ : Indep 𝒢₀ (MeasurableSpace.comap (fun ω => liftU (N ω)) inferInstance) Pr :=
    indep_of_indep_of_le_right hI1 (hle N)
  have hI2₁ : Indep (MeasurableSpace.comap (fun ω => liftU (N' ω)) inferInstance)
      (𝒢₀ ⊔ MeasurableSpace.comap (fun ω => liftU (N ω)) inferInstance) Pr :=
    indep_of_indep_of_le_right (indep_of_indep_of_le_left hI2 (hle N')) (sup_le_sup_left (hle N) _)
  have hK : 0 < (onePlan d β).K := by
    show (0 : ℕ∞) < 1
    exact one_pos
  revert hT
  generalize hf : cycMarkovFilt 𝒢₀ h𝒢 hN.measurable Pr = f
  intro hT
  have hf' : f = cycMultiFilt (onePlan d β) 𝒢₀ (N := fun ω => liftU (N ω)) hN₁.measurable h𝒢 Pr :=
    hf.symm.trans (cycMarkovFilt_eq 𝒢₀ h𝒢 hN.measurable Pr)
  subst hf'
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    cyc_multi_exploration_a (onePlan d β) 𝒢₀ hN₁ hN₁' hI1₁ hI2₁ hK h𝒢 hT
  have hNm : Measurable N := hN.measurable
  -- events and laws
  have hev : ∀ (F : Set (Measure (RingSpace d β))) (ω : Ω),
      tildeMeasure (fun ω => liftU (N ω)) (fun ω => liftU (N' ω))
        (cycRegionStop (onePlan d β) (cycNgood fun ω => liftU (N ω)) T) ω ∈
          cycSlice () ⁻¹' F ↔ tildeMeasure N N' (markovRegion N T) ω ∈ F := by
    intro F ω
    rw [tilde_markov]
    simp
  have hset : ∀ (S : Set Ω) (F : Set (Measure (RingSpace d β))),
      S ∩ {ω | tildeMeasure (fun ω => liftU (N ω)) (fun ω => liftU (N' ω))
        (cycRegionStop (onePlan d β) (cycNgood fun ω => liftU (N ω)) T) ω ∈ cycSlice () ⁻¹' F} =
      S ∩ {ω | tildeMeasure N N' (markovRegion N T) ω ∈ F} := by
    intro S F
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, hev]
  have hlaw : ∀ F : Set (Measure (RingSpace d β)), MeasurableSet F →
      (Pr.map fun ω => liftU (N ω)) (cycSlice () ⁻¹' F) = (Pr.map N) F := by
    intro F hF
    rw [Measure.map_apply hN₁.measurable ((measurable_cycSlice ()) hF),
      Measure.map_apply hNm hF]
    congr 1
    ext ω
    simp
  have cond_aux : ∀ {F : Ω × Measure (RingSpace d β) → ℝ≥0∞},
      Measurable[hT.measurableSpace.prod inferInstance] F →
      Measurable[hT.measurableSpace.prod inferInstance]
        (fun p : Ω × Measure (Unit × RingSpace d β) => F (p.1, cycSlice () p.2)) ∧
      (∀ ω, F (ω, (N ω).restrict (markovRegion N T ω)ᶜ) =
        F (ω, cycSlice () ((liftU (N ω)).restrict
          (cycRegionStop (onePlan d β) (cycNgood fun ω => liftU (N ω)) T ω)ᶜ))) ∧
      (∀ ω, ∫⁻ ν, F (ω, ν.restrict (markovRegion N T ω)ᶜ) ∂(Pr.map N) =
        ∫⁻ νh, F (ω, cycSlice () (νh.restrict
          (cycRegionStop (onePlan d β) (cycNgood fun ω => liftU (N ω)) T ω)ᶜ))
            ∂(Pr.map fun ω => liftU (N ω))) := by
    intro F hF
    have hfst : @Measurable _ _ (hT.measurableSpace.prod inferInstance) hT.measurableSpace
        (Prod.fst : Ω × Measure (Unit × RingSpace d β) → Ω) := @measurable_fst _ _ hT.measurableSpace _
    have hsnd : @Measurable _ _ (hT.measurableSpace.prod inferInstance) _
        (Prod.snd : Ω × Measure (Unit × RingSpace d β) → Measure (Unit × RingSpace d β)) :=
      @measurable_snd _ _ hT.measurableSpace _
    refine ⟨hF.comp (hfst.prodMk ((measurable_cycSlice ()).comp hsnd)), fun ω => ?_, fun ω => ?_⟩
    · rw [cycRegionStop_markov, compl_unit_prod, cycSlice_restrict_liftU]
    · have hG : Measurable fun ν : Measure (RingSpace d β) => F (ω, ν) :=
        hF.comp (@measurable_prodMk_left Ω _ hT.measurableSpace _ ω)
      rw [cycRegionStop_markov, compl_unit_prod]
      exact (lintegral_restrict_liftU hNm (measurableSet_markovRegion N T ω).compl hG).symm
  have hZ : Measurable[hT.measurableSpace] (fun ω => markovW N ω (ElboimSly.SRW.stopReal T ω)) := by
    have hpath : Measurable[hT.measurableSpace] (fun ω => ((CycRec.coord (CycPlan.junk (onePlan d β))
        (cycRecStop (onePlan d β) (cycNgood fun ω => liftU (N ω)) T ω) 0).2.1 :
          CPath (Fin d → ℤ))) :=
      measurable_subtype_coe.comp (measurable_snd.comp
        ((CycRec.measurable_coord (CycPlan.junk (onePlan d β)) 0).comp h2))
    have := @measurable_fn_at (Fin d → ℤ) _ _ _ Ω hT.measurableSpace _ hpath
      (ElboimSly.SRW.stopReal T) (measurable_stopReal_stop hT)
    have heq : (fun ω => markovW N ω (ElboimSly.SRW.stopReal T ω)) = fun ω =>
        ((CycRec.coord (CycPlan.junk (onePlan d β))
          (cycRecStop (onePlan d β) (cycNgood fun ω => liftU (N ω)) T ω) 0).2.1 :
            CPath (Fin d → ℤ)).fn (ElboimSly.SRW.stopReal T ω) := by
      funext ω
      unfold cycRecStop
      rw [show cycNgood (fun ω => liftU (N ω)) ω = liftU (markovNgood N ω) from
        (liftU_markovNgood N ω).symm, trunc_envFinal_onePlan, coord_markovRec_gen]
      have := markovEntry_fn_markovW N ω (ElboimSly.SRW.stopReal T ω) (ElboimSly.SRW.stopReal T ω)
      rw [min_self] at this
      exact this.symm
    rw [heq]
    exact this
  refine ⟨h1, hZ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [h4] with ω hω hTω
    have h := hω hTω
    apply liftU_injective
    rw [liftU_restrict, ← cycRegionStop_markov, h, rm_cycRecStop_markov]
  · have : (fun ω => (Measure.count.restrict (markovRings N T ω) : Measure (RingSpace d β))) =
        fun ω => cycSlice () ((cycRecStop (onePlan d β) (cycNgood fun ω => liftU (N ω)) T ω).rm β) := by
      funext ω
      rw [rm_cycRecStop_markov, cycSlice_liftU]
    rw [this]
    exact (measurable_cycSlice ()).comp h5
  · have hfst : @Measurable _ _ (hT.measurableSpace.prod inferInstance) hT.measurableSpace
        (Prod.fst : Ω × RingSpace d β → Ω) := @measurable_fst _ _ hT.measurableSpace _
    have hsnd : @Measurable _ _ (hT.measurableSpace.prod inferInstance) _
        (Prod.snd : Ω × RingSpace d β → RingSpace d β) := @measurable_snd _ _ hT.measurableSpace _
    have hg : @Measurable _ _ (hT.measurableSpace.prod inferInstance)
        (hT.measurableSpace.prod inferInstance)
        (fun p : Ω × RingSpace d β => (p.1, ((), p.2))) :=
      hfst.prodMk (measurable_const.prodMk hsnd)
    have := h3.preimage hg
    convert this using 1
    ext p
    simp [cycRegionStop_markov]
  · intro A hA F hF
    have := h6 hA ((measurable_cycSlice ()) hF)
    rw [hset, hlaw F hF] at this
    exact this
  · intro hfin A hA F hF
    have := h7 hfin hA ((measurable_cycSlice ()) hF)
    rw [hset, hlaw F hF] at this
    exact this
  · intro F hF
    obtain ⟨hFh, e1, e2⟩ := cond_aux hF
    have := h8 hFh
    beta_reduce at this
    simp only [e1, e2]
    exact this
  · intro hfin F hF
    obtain ⟨hFh, e1, e2⟩ := cond_aux hF
    have := h9 hfin hFh
    beta_reduce at this
    simp only [e1, e2]
    exact this

end ElboimSly.Cyclic

end
