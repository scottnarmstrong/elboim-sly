/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78TauRc
public import Mathlib

/-!
# A measurable, right-continuous surrogate for the glued continuation `W'`

One excursion succeeds with probability at least frac12 (the walk `W'_i` of w_2 after zeta_i, given ℱ^+_zeta_i).
The walk `contGlue β (planFirst P N N' T δ) (contSeq N'')` of `cyc_plan_coupling_regen_law` is only
a.e.-measurable (the measure `tildeMeasure N N' R` is). `planFirstTil` replaces it by the version
built from `Ytil = tildeMeasure (τ N) (τ N') R`, and `planSurr` is the corresponding glued walk.
It is measurable (`measurable_planSurr`), right-continuous everywhere (`isRCPath_planSurr`) and
equal almost surely to the original (`planSurr_ae_eq`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β)
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS I d β)} {N'' : Ω → Measure (ℕ × RingSpace d β)}
  (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)

/-- The measurable version `Ytil` of the tilde measure. -/
noncomputable def planYtil (P : CycPlan I d β) (N N' : Ω → Measure (CycS I d β))
    (T : Ω → WithTop ℝ≥0) : Ω → Measure (CycS I d β) :=
  tildeMeasure (fun ω => tau (cycIntensity I d β) (N ω))
    (fun ω => tau (cycIntensity I d β) (N' ω)) (cycRegionStop P (cycNgood N) T)

/-- `planFirst` with `Ytil` in place of the tilde measure. -/
noncomputable def planFirstTil (P : CycPlan I d β) (N N' : Ω → Measure (CycS I d β))
    (T : Ω → WithTop ℝ≥0) (δ : Ω → CycData I d) (ω : Ω) : ℝ≥0 → Fin d → ℤ :=
  fun s => envWalk (planYtil P N N' T ω) (δ ω) s - (δ ω).start

/-- The surrogate for the glued continuation `W'`. -/
noncomputable def planSurr (P : CycPlan I d β) (N N' : Ω → Measure (CycS I d β))
    (N'' : Ω → Measure (ℕ × RingSpace d β)) (T : Ω → WithTop ℝ≥0) (δ : Ω → CycData I d)
    (ω : Ω) : ℝ≥0 → Fin d → ℤ :=
  contGlue β.toNNReal (planFirstTil P N N' T δ ω) (contSeq N'' ω)

include hN hN' hI1 hI2 in
theorem measurable_planFirstTil (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    {δ : Ω → CycData I d} (hδ : Measurable[hT.measurableSpace] δ) :
    Measurable (planFirstTil P N N' T δ) := by
  obtain ⟨-, -, hregset, -, -, -, -, -, -⟩ := cyc_multi_exploration_a P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT
  have hle : hT.measurableSpace.prod (inferInstance : MeasurableSpace (CycS I d β)) ≤
      mΩ.prod inferInstance :=
    sup_le_sup (MeasurableSpace.comap_mono hT.measurableSpace_le) le_rfl
  have hY : Measurable (planYtil P N N' T) :=
    measurable_tildeTauG (cycIntensity I d β) hN.measurable hN'.measurable (hle _ hregset)
  have hδm : Measurable δ := hδ.mono hT.measurableSpace_le le_rfl
  refine measurable_pi_iff.2 fun s => ?_
  have h1 := (measurable_pi_apply s).comp (measurable_envWalk.comp (hY.prodMk hδm))
  have h2 : Measurable fun ω => (δ ω).start := (measurable_fst.comp measurable_snd).comp hδm
  exact h1.sub h2

include hN hN' hI1 hI2 in
theorem planFirstTil_ae_eq {T : Ω → WithTop ℝ≥0} (δ : Ω → CycData I d) :
    ∀ᵐ ω ∂Pr, planFirstTil P N N' T δ ω = planFirst P N N' T δ ω := by
  filter_upwards [hN.tau_comp_ae_eq, hN'.tau_comp_ae_eq] with ω h1 h2
  funext s
  simp only [planFirstTil, planFirst, planYtil, tildeMeasure]
  rw [h1, h2]

theorem measurable_contSeq' (hN'' : IsPoissonPointProcess N''
    ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pr) : Measurable (contSeq N'') :=
  measurable_pi_iff.2 fun k => measurable_walkSlice hN'' k

include hN hN' hI1 hI2 in
theorem measurable_planSurr (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    {δ : Ω → CycData I d} (hδ : Measurable[hT.measurableSpace] δ)
    (hN'' : IsPoissonPointProcess N'' ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pr) :
    Measurable (planSurr P N N' N'' T δ) := by
  have h1 := measurable_planFirstTil P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT hδ
  have h2 := measurable_contSeq' hN''
  have h4 := h1.prodMk h2
  refine measurable_pi_iff.2 fun t => ?_
  have h5 := measurable_contGlue_at (d := d) (b := β.toNNReal) t
  have e : (fun ω => planSurr P N N' N'' T δ ω t) = (fun x : (ℝ≥0 → Fin d → ℤ) × (ℕ → ℝ≥0 → Fin d → ℤ) =>
      contGlue β.toNNReal x.1 x.2 t) ∘ (fun ω => (planFirstTil P N N' T δ ω, contSeq N'' ω)) := by
    funext ω
    rfl
  rw [e]
  exact h5.comp h4

theorem isRCPath_planSurr (T : Ω → WithTop ℝ≥0) (δ : Ω → CycData I d) (ω : Ω) :
    IsRCPath (planSurr P N N' N'' T δ ω) := by
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  have hp : IsRCPath (planFirstTil P N N' T δ ω) :=
    isRCPath_sub_const (isRCPath_envWalk (planYtil P N N' T ω) (δ ω)) (δ ω).start
  have hq : ∀ k, IsRCPath (contSeq N'' ω k) := fun k => isRCPath_walkMap _
  exact isRCPath_contGlue hb hp hq

include hN hN' hI1 hI2 in
theorem planSurr_ae_eq {T : Ω → WithTop ℝ≥0} (δ : Ω → CycData I d) :
    ∀ᵐ ω ∂Pr, planSurr P N N' N'' T δ ω =
      contGlue β.toNNReal (planFirst P N N' T δ ω) (contSeq N'' ω) := by
  filter_upwards [planFirstTil_ae_eq P 𝒢₀ hN hN' hI1 hI2 (T := T) δ] with ω h
  simp only [planSurr, h]

end ElboimSly.Paper.Step

end
