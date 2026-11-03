/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Resample
public import Mathlib

/-!
# The tower property for the resampling probabilities

ES22 Lemma 5.5, Step 2 (tower property `condExp_condExp_of_le`, `condExp_mono`).

For stopping times `T ≤ T'` of the joint exploration filtration, measurable sets `B`, `C` of
environments such that `{N ∈ B}` lies in `ℱ_{T'}`: if `P(N ∈ C | ℱ_{T'}) ≥ a` a.s. on `{N ∈ B}`,
then `P(N ∈ C | ℱ_T) ≥ a P(N ∈ B | ℱ_T)` a.s.  The conditional probabilities are the canonical
versions `Φ_B(ρ_T)` (`resampleProb`) of resampling formula.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper

variable {Ω : Type*}

/-- Almost-everywhere inequality of two `m`-measurable functions from the inequality of their
integrals over every `m`-measurable set. -/
theorem ae_le_of_setLIntegral_le_sub [mΩ : MeasurableSpace Ω] {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (Pr : @Measure Ω mΩ)
    [@IsFiniteMeasure Ω mΩ Pr] {f g : Ω → ℝ≥0∞} (hf : Measurable[m] f) (hg : Measurable[m] g)
    (h : ∀ A, MeasurableSet[m] A → ∫⁻ ω in A, f ω ∂Pr ≤ ∫⁻ ω in A, g ω ∂Pr) :
    f ≤ᵐ[Pr] g := by
  have : @IsFiniteMeasure Ω m (Pr.trim hm) := isFiniteMeasure_trim hm
  have : @SigmaFinite Ω m (Pr.trim hm) := by infer_instance
  have key : f ≤ᵐ[Pr.trim hm] g := by
    refine @ae_le_of_forall_setLIntegral_le_of_sigmaFinite Ω m (Pr.trim hm) _ f g hf ?_
    intro s hs _
    show ∫⁻ x, f x ∂(@Measure.restrict Ω m (Pr.trim hm) s) ≤
      ∫⁻ x, g x ∂(@Measure.restrict Ω m (Pr.trim hm) s)
    rw [restrict_trim hm Pr hs, lintegral_trim hm hf, lintegral_trim hm hg]
    exact h s hs
  exact ae_of_ae_trim hm key


section tower

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β) (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS I d β)}
  (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)

/-- The canonical version `Φ_X(ρ_T)` of `P(N ∈ X | ℱ_T)`. -/
noncomputable def resPhi (Pr : Measure Ω) (N : Ω → Measure (CycS I d β)) (T : Ω → WithTop ℝ≥0)
    (X : Set (Measure (CycS I d β))) (ω : Ω) : ℝ≥0∞ :=
  resampleProb (Pr.map N) ((cycRecStop P (cycNgood N) T ω).rm β)
    (cycRegionStop P (cycNgood N) T ω) X

include hN hN' hI1 hI2 in
/-- **Tower property**.  Let `T ≤ T'` be a.s. finite stopping times of the joint exploration
filtration, `B`, `C` measurable sets of environments with `{N ∈ B} ∈ ℱ_{T'}`.  If
`P(N ∈ C | ℱ_{T'}) ≥ a` a.s. on `{N ∈ B}`, then `P(N ∈ C | ℱ_T) ≥ a P(N ∈ B | ℱ_T)` a.s. -/
theorem resample_tower_lower (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T T' : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    (hT' : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T') (hTT' : T ≤ T')
    (hfin : Pr {ω | T ω ≠ ⊤} = 1) (hfin' : Pr {ω | T' ω ≠ ⊤} = 1)
    {B C : Set (Measure (CycS I d β))} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hH : MeasurableSet[hT'.measurableSpace] (N ⁻¹' B)) {a : ℝ≥0∞}
    (ha : ∀ᵐ ω ∂Pr, N ω ∈ B → a ≤ resPhi P Pr N T' C ω) :
    ∀ᵐ ω ∂Pr, a * resPhi P Pr N T B ω ≤ resPhi P Pr N T C ω := by
  have hPr := hN.isProbabilityMeasure
  obtain ⟨hmB, hBint⟩ := es4_resample_b P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT hfin hB
  obtain ⟨hmC, hCint⟩ := es4_resample_b P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT hfin hC
  obtain ⟨-, hCint'⟩ := es4_resample_b P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT' hfin' hC
  have hle := hT.measurableSpace_le
  have hmono : hT.measurableSpace ≤ hT'.measurableSpace := IsStoppingTime.measurableSpace_mono hT hT' hTT'
  refine ae_le_of_setLIntegral_le_sub hle Pr (hmB.const_mul a) hmC fun A hA => ?_
  have hAm : MeasurableSet A := hle _ hA
  have hHm : MeasurableSet (N ⁻¹' B) := hN.measurable hB
  have hAH : MeasurableSet[hT'.measurableSpace] (A ∩ N ⁻¹' B) := (hmono _ hA).inter hH
  have hBm : Measurable (resPhi P Pr N T B) := (hmB.mono hle le_rfl)
  calc ∫⁻ ω in A, a * resPhi P Pr N T B ω ∂Pr
      = a * ∫⁻ ω in A, resPhi P Pr N T B ω ∂Pr := lintegral_const_mul _ hBm
    _ = a * Pr (A ∩ N ⁻¹' B) := by
        have h1 : ∫⁻ ω in A, resPhi P Pr N T B ω ∂Pr = Pr (A ∩ N ⁻¹' B) := (hBint hA).symm
        rw [h1]
    _ = ∫⁻ ω in A ∩ N ⁻¹' B, a ∂Pr := by rw [setLIntegral_const]
    _ ≤ ∫⁻ ω in A ∩ N ⁻¹' B, resPhi P Pr N T' C ω ∂Pr := by
        refine lintegral_mono_ae ?_
        have h2 : ∀ᵐ ω ∂Pr, ω ∈ A ∩ N ⁻¹' B → a ≤ resPhi P Pr N T' C ω := by
          filter_upwards [ha] with ω hω hmem
          exact hω hmem.2
        exact (ae_restrict_iff' (hAm.inter hHm)).2 h2
    _ = Pr ((A ∩ N ⁻¹' B) ∩ {ω | N ω ∈ C}) := (hCint' hAH).symm
    _ ≤ Pr (A ∩ {ω | N ω ∈ C}) := measure_mono (fun ω hω => ⟨hω.1.1, hω.2⟩)
    _ = ∫⁻ ω in A, resPhi P Pr N T C ω ∂Pr := hCint hA


include hN hN' hI1 hI2 in
/-- Pulling out an `ℱ_T`-measurable event: a.s. on `{N ∈ K}`, `Φ_E ≤ Φ_{K ∩ E}`. -/
theorem resPhi_le_inter (hK0 : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    (hfin : Pr {ω | T ω ≠ ⊤} = 1) {K E : Set (Measure (CycS I d β))} (hK : MeasurableSet K)
    (hE : MeasurableSet E) (hKT : MeasurableSet[hT.measurableSpace] (N ⁻¹' K)) :
    ∀ᵐ ω ∂Pr, N ω ∈ K → resPhi P Pr N T E ω ≤ resPhi P Pr N T (K ∩ E) ω := by
  have hPr := hN.isProbabilityMeasure
  obtain ⟨hmE, hEint⟩ := es4_resample_b P 𝒢₀ hN hN' hI1 hI2 hK0 h𝒢 hT hfin hE
  obtain ⟨hmKE, hKEint⟩ := es4_resample_b P 𝒢₀ hN hN' hI1 hI2 hK0 h𝒢 hT hfin (hK.inter hE)
  have hle := hT.measurableSpace_le
  have h1 : Measurable[hT.measurableSpace] ((N ⁻¹' K).indicator (resPhi P Pr N T E)) :=
    hmE.indicator hKT
  have key : (N ⁻¹' K).indicator (resPhi P Pr N T E) ≤ᵐ[Pr] resPhi P Pr N T (K ∩ E) := by
    refine ae_le_of_setLIntegral_le_sub hle Pr h1 hmKE fun A hA => ?_
    have hAm : MeasurableSet A := hle _ hA
    have hKm : MeasurableSet (N ⁻¹' K) := hN.measurable hK
    have hAK : MeasurableSet[hT.measurableSpace] (A ∩ N ⁻¹' K) := hA.inter hKT
    refine le_of_eq ?_
    calc ∫⁻ ω in A, (N ⁻¹' K).indicator (resPhi P Pr N T E) ω ∂Pr
        = ∫⁻ ω in A ∩ N ⁻¹' K, resPhi P Pr N T E ω ∂Pr := by
          rw [lintegral_indicator hKm, Measure.restrict_restrict hKm, inter_comm]
      _ = Pr ((A ∩ N ⁻¹' K) ∩ {ω | N ω ∈ E}) := (hEint hAK).symm
      _ = Pr (A ∩ {ω | N ω ∈ K ∩ E}) := by
          congr 1; ext ω; simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]; tauto
      _ = ∫⁻ ω in A, resPhi P Pr N T (K ∩ E) ω ∂Pr := hKEint hA
  filter_upwards [key] with ω hω hmem
  simpa [Set.indicator, hmem] using hω

include hN hN' hI1 hI2 in
/-- **Step 2 of ES22 Lemma 5.5**: from the step-1 bound at `T'` and the bound at `T`,
`P(N ∈ C | ℱ_T) ≥ a c` a.s. on `{N ∈ K}`. -/
theorem es5_5_step2 (hK0 : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T T' : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    (hT' : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T') (hTT' : T ≤ T')
    (hfin : Pr {ω | T ω ≠ ⊤} = 1) (hfin' : Pr {ω | T' ω ≠ ⊤} = 1)
    {K E C : Set (Measure (CycS I d β))} (hK : MeasurableSet K) (hE : MeasurableSet E)
    (hC : MeasurableSet C) (hKT : MeasurableSet[hT.measurableSpace] (N ⁻¹' K))
    (hKET : MeasurableSet[hT'.measurableSpace] (N ⁻¹' (K ∩ E))) {a c : ℝ≥0∞}
    (hstep1 : ∀ᵐ ω ∂Pr, N ω ∈ K ∩ E → a ≤ resPhi P Pr N T' C ω)
    (hc : ∀ᵐ ω ∂Pr, N ω ∈ K → c ≤ resPhi P Pr N T E ω) :
    ∀ᵐ ω ∂Pr, N ω ∈ K → a * c ≤ resPhi P Pr N T C ω := by
  have h1 := resample_tower_lower P 𝒢₀ hN hN' hI1 hI2 hK0 h𝒢 hT hT' hTT' hfin hfin'
    (hK.inter hE) hC hKET hstep1
  have h2 := resPhi_le_inter P 𝒢₀ hN hN' hI1 hI2 hK0 h𝒢 hT hfin hK hE hKT
  filter_upwards [h1, h2, hc] with ω hω1 hω2 hω3 hmem
  calc a * c ≤ a * resPhi P Pr N T E ω := by gcongr; exact hω3 hmem
    _ ≤ a * resPhi P Pr N T (K ∩ E) ω := by gcongr; exact hω2 hmem
    _ ≤ resPhi P Pr N T C ω := hω1

end tower

end ElboimSly.Paper.Escape
