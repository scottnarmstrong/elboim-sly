/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycPlanCouplingCont
public import Mathlib

/-!
# Plan-level coupling after a stopping time (d): the regenerated continuation

Plan-level coupling after a stopping time (d). Let `P' = P^{Ñ_T}_δ`, `u = δ.start`, and let `N''` be a
`PPP(# ⊗ μ_β)` independent of `σ(𝒢₀,N,N') ∨ 𝒩`. The walk `W'` of the statement is
`contGlue β (P' - u) (walks of the copies of N'')`: its first piece is `P' - u` with closing time
`treg(P' - u)`, and the `(i+1)`-st piece is the cyclic walk of the copy `i - 1` of `N''` (our
copies are indexed from `0`, as in `regenWalk`).

* `cyc_plan_coupling_regen_agree`: `W'(r) = P'(r) - u` for `r ∈ [0, treg(P' - u)]`;
* `cyc_plan_coupling_regen_law`: `P(A ∩ {T < ∞} ∩ {W' ∈ Γ}) = P(A ∩ {T < ∞}) P(W_reg ∈ Γ)`, with
  `W_reg` the regenerated walk of the copies of `N''` (the law of `W_reg` is the law of the
  regenerated walk by the constructions of the regenerated walk).
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
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)

/-- The recentred environment path `P' - u` after the stopping time `T`. -/
noncomputable def planFirst (P : CycPlan I d β) (N N' : Ω → Measure (CycS I d β))
    (T : Ω → WithTop ℝ≥0) (δ : Ω → CycData I d) (ω : Ω) : ℝ≥0 → Fin d → ℤ :=
  fun s => envWalk (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) (δ ω) s - (δ ω).start

/-- The walks of the copies of `N''`. -/
noncomputable def contSeq (N'' : Ω → Measure (ℕ × RingSpace d β)) (ω : Ω) :
    ℕ → ℝ≥0 → Fin d → ℤ := fun k => walkMap (cycSlice k (N'' ω))

include hN hN' hI1 hI2 in
theorem aemeasurable_planFirst (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    {δ : Ω → CycData I d} (hδ : Measurable[hT.measurableSpace] δ) :
    AEMeasurable (planFirst P N N' T δ) Pr := by
  obtain ⟨-, -, hregset, -, -, -, -, -, -⟩ := cyc_multi_exploration_a P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT
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
  have hδm : Measurable δ := hδ.mono hT.measurableSpace_le le_rfl
  have hm : Measurable fun ω => (fun s : ℝ≥0 => envWalk (Ytil ω) (δ ω) s - (δ ω).start) := by
    refine measurable_pi_iff.2 fun s => ?_
    have h1 := (measurable_pi_apply s).comp (measurable_envWalk.comp (hY.prodMk hδm))
    have h2 : Measurable fun ω => (δ ω).start :=
      (measurable_fst.comp measurable_snd).comp hδm
    exact h1.sub h2
  refine hm.aemeasurable.congr ?_
  filter_upwards [hYae] with ω hω
  funext s
  simp only [planFirst, hω]
  rfl

theorem contSeq_zero_apply (ν : Measure (ℕ × RingSpace d β)) (k : ℕ) :
    walkMap (cycSlice k ν) 0 = 0 := by
  classical
  unfold walkMap
  exact cycWalk_zero (by split_ifs with h; exacts [h, good_zero]) _ _

/-- `W'(r) = P'(r) - u` for `r ∈ [0, treg(P' - u)]` (pathwise, for any first piece). -/
theorem contGlue_agree {b : ℝ≥0} (hb : 0 < b) (p : ℝ≥0 → Fin d → ℤ)
    (q : ℕ → ℝ≥0 → Fin d → ℤ) (hq : ∀ k, q k 0 = 0) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) ≤ pathTreg b p) : contGlue b p q r = p r := by
  set σ := partialSums fun k => pathTreg b (contPieces p q k) with hσ
  have hm : Monotone σ := monotone_nat_of_le_succ fun n => by
    rw [hσ, partialSums_succ]; exact le_self_add
  have h0 : σ 0 = 0 := by simp [hσ, partialSums]
  have h1 : σ 1 = pathTreg b p := by
    rw [hσ, show (1 : ℕ) = 0 + 1 from rfl, partialSums_succ]
    simp [partialSums, contPieces]
  rcases hr.lt_or_eq with hlt | heq
  · have hc : gluedCount σ r = 0 := gluedCount_eq hm (by rw [h0]; exact zero_le)
      (by rw [h1]; exact hlt)
    unfold contGlue gluedWalk
    rw [← hσ, hc, h0]
    simp [contPieces]
  · -- `r = treg(p) < ∞`
    have hfin : pathTreg b p < ⊤ := heq ▸ ENNReal.coe_lt_top
    obtain ⟨j, -, hj, hz⟩ := pathTreg_exists (b := b) hfin
    have h2 : σ 2 = pathTreg b p + pathTreg b (q 0) := by
      rw [hσ, show (2 : ℕ) = 1 + 1 from rfl, partialSums_succ]
      simp [partialSums, contPieces]
    have hc : gluedCount σ r = 1 := by
      refine gluedCount_eq hm (by rw [h1, heq]) ?_
      rw [h2, heq]
      refine ENNReal.lt_add_right hfin.ne ?_
      exact (lt_of_lt_of_le (by exact_mod_cast hb) (le_pathTreg b (q 0))).ne'
    unfold contGlue gluedWalk
    rw [← hσ, hc, h1]
    have hr' : r = j * b := by
      have : (r : ℝ≥0∞) = (((j : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) := by rw [heq, hj]
      exact_mod_cast this
    simp only [contPieces]
    rw [← heq, ENNReal.toNNReal_coe, tsub_self, hq 0, hr', hz]

end ElboimSly.Cyclic

end
