/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycHitCoupleRegenAe
public import Mathlib

/-!
# ES22 Lemma 2.1: Lemma 2.1 of ES22 for the regenerated walk, law form

ES22 Lemma 2.1 (b)--(e) (ES22 Lemma 2.1, ES22 §2; ES22 §2, ES22 §4).

`N` is a `PPP(# ⊗ μ_β)` on `ℕ × S_β` (copy `k` is piece `k + 1`), `N'` and `𝒢₀` are as in
Several walks explored one after another, and `T` is a stopping time of the joint exploration filtration
`ℱ^{𝒫_reg}` (`cycMultiFilt (regPlan d β)`). The regenerated walk of an environment `ν` is
`regW ν`: `regW ν = regenWalk (slices ν)` for good `ν` (`regW_eq_regenWalk`) and
`regRecWalk (ρ^{𝒫_reg}(ν)) = regW ν` almost surely for a `PPP` (`cyc_hit_couple_regen`, 2nd and
3rd conjuncts).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (ℕ × RingSpace d β)}

theorem ae_regW_eq_regRecWalk {M : Ω → Measure (ℕ × RingSpace d β)}
    (hM : IsPoissonPointProcess M (cycIntensity ℕ d β) Pr) :
    ∀ᵐ ω ∂Pr, ∀ t : ℝ≥0,
      regRecWalk ((regPlan d β).envFinal (M ω)) t = regW (M ω) t := by
  filter_upwards [ae_cycGood hM] with ω hω t
  rw [regW_eq_regenWalk hω, regRecWalk_envFinal_eq_regenWalk hω]

/-- **ES22 Lemma 2.1** (ES22 Lemma 2.1 for the regenerated walk, law form).
There is a `PPP(# ⊗ μ_β)` `M` (the environment after `T`) such that, with `W = regW N` and
`W' = regW M` the regenerated walks of `N` and `M`:
* `W = W_reg(ρ^{𝒫_reg}(N))` and `W' = W_reg(ρ^{𝒫_reg}(M))` almost surely;
* (b) `P(A ∩ {T<∞} ∩ {W' ∈ Γ}) = P(A ∩ {T<∞}) P(W ∈ Γ)` for `A ∈ ℱ_T` and measurable `Γ`; if
  `P(T<∞) = 1`, then `W'` is independent of `ℱ_T` and `Law(W') = Law(W)`;
* almost surely on `{T = t}` (with `ν^· = slices N`, `α = regenStart`, `thit = cycThit`): `M` is
  good, (c) `W(t+s) - W(t) = W'(s)` for `t + s ≤ thit(t)`, and the first piece of `W'` does not close
  before `thit(t) - t` if `α(t) < t`; (d) `thit(t) = ∞` if `α(t) = t` and `thit(t) ≤ σ_{k_t+1}`
  if `α(t) < t`; (e) `thit(t)` is the infimum through `W'`. -/
theorem cyc_hit_couple_regen (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr)
    (hN' : IsPoissonPointProcess N' (cycIntensity ℕ d β) Pr)
    (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
    (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
      (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)
    (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt (regPlan d β) 𝒢₀ hN.measurable h𝒢 Pr) T) :
    ∃ M : Ω → Measure (ℕ × RingSpace d β), IsPoissonPointProcess M (cycIntensity ℕ d β) Pr ∧
      (∀ᵐ ω ∂Pr, ∀ t : ℝ≥0, regRecWalk ((regPlan d β).envFinal (N ω)) t = regW (N ω) t) ∧
      (∀ᵐ ω ∂Pr, ∀ t : ℝ≥0, regRecWalk ((regPlan d β).envFinal (M ω)) t = regW (M ω) t) ∧
      (∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A → ∀ {Γ : Set (ℝ≥0 → Fin d → ℤ)},
        MeasurableSet Γ →
        Pr (A ∩ {ω | T ω ≠ ⊤} ∩ {ω | regW (M ω) ∈ Γ}) =
          Pr (A ∩ {ω | T ω ≠ ⊤}) * Pr {ω | regW (N ω) ∈ Γ}) ∧
      (Pr {ω | T ω ≠ ⊤} = 1 →
        Indep hT.measurableSpace
          (MeasurableSpace.comap (fun ω => regW (M ω)) inferInstance) Pr ∧
        Pr.map (fun ω => regW (M ω)) = Pr.map (fun ω => regW (N ω))) ∧
      (∀ᵐ ω ∂Pr, CycGood (N ω) ∧ ∀ t : ℝ≥0, T ω = t →
        CycGood (M ω) ∧
        (∀ s : ℝ≥0, ENNReal.ofReal ((t : ℝ) + s) ≤ ElboimSly.cycThit (slices (N ω)) (t : ℝ) →
          ElboimSly.regenWalk (slices (N ω)) ((t : ℝ) + s) -
              ElboimSly.regenWalk (slices (N ω)) (t : ℝ) =
            ElboimSly.regenWalk (slices (M ω)) (s : ℝ)) ∧
        (ElboimSly.regenStart (slices (N ω)) (t : ℝ) < t →
          ∀ s : ℝ≥0, ENNReal.ofReal ((t : ℝ) + s) ≤ ElboimSly.cycThit (slices (N ω)) (t : ℝ) →
            (s : ℝ≥0∞) < ElboimSly.cycTreg (slices (M ω) 0)) ∧
        (ElboimSly.regenStart (slices (N ω)) (t : ℝ) = t →
          ElboimSly.cycThit (slices (N ω)) (t : ℝ) = ⊤) ∧
        (ElboimSly.regenStart (slices (N ω)) (t : ℝ) < t →
          ElboimSly.cycThit (slices (N ω)) (t : ℝ) ≤
            ElboimSly.regenSigma (slices (N ω))
              (ElboimSly.regenCount (slices (N ω)) (t : ℝ) + 1)) ∧
        (ElboimSly.cycThit (slices (N ω)) (t : ℝ) =
          ⨅ s ∈ {s : ℝ | (t : ℝ) < s ∧ ∃ s' : ℝ, (∃ kk : ℤ, s' = s + kk * β) ∧
            ElboimSly.regenStart (slices (N ω)) (t : ℝ) < s' ∧ s' < t ∧
            ‖ElboimSly.regenWalk (slices (N ω)) (t : ℝ) +
              ElboimSly.regenWalk (slices (M ω)) (s - t) -
                ElboimSly.regenWalk (slices (N ω)) s'‖ ≤ 1},
            ENNReal.ofReal s)) := by
  obtain ⟨hMm, hlaw, ha⟩ := regen_couple_core 𝒢₀ hN hN' hI1 hI2 h𝒢 hT
  have hPr := hN.isProbabilityMeasure
  have hM : IsPoissonPointProcess (regM N N' T) (cycIntensity ℕ d β) Pr :=
    hN.of_map_eq hMm hlaw
  refine ⟨regM N N' T, hM, ae_regW_eq_regRecWalk hN, ae_regW_eq_regRecWalk hM, ha, ?_,
    regen_couple_ae 𝒢₀ hN hN' hI1 hI2 h𝒢 hT⟩
  intro hfin
  have hWN : Measurable fun ω => regW (N ω) := measurable_regW.comp hN.measurable
  have hWM : Measurable fun ω => regW (regM N N' T ω) := measurable_regW.comp hMm
  have hEm : MeasurableSet {ω | T ω ≠ ⊤} := hT.measurableSpace_le _ (measurableSet_ne_top hT)
  have hae : {ω | T ω ≠ ⊤} =ᵐ[Pr] (univ : Set Ω) := by
    have : Pr {ω | T ω ≠ ⊤}ᶜ = 0 := by
      rw [prob_compl_eq_one_sub hEm, hfin]; simp
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with ω hω
    simpa using hω
  have key : ∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A → ∀ {Γ : Set (ℝ≥0 → Fin d → ℤ)},
      MeasurableSet Γ → Pr (A ∩ {ω | regW (regM N N' T ω) ∈ Γ}) =
        Pr A * Pr {ω | regW (N ω) ∈ Γ} := by
    intro A hA Γ hΓ
    have h1 := ha hA hΓ
    rw [measure_congr (Filter.EventuallyEqSet.inter (Filter.EventuallyEqSet.inter
      Filter.EventuallyEq.rfl hae) Filter.EventuallyEq.rfl),
      measure_congr (Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl hae)] at h1
    simp only [inter_univ] at h1
    exact h1
  have hlawW : ∀ {Γ : Set (ℝ≥0 → Fin d → ℤ)}, MeasurableSet Γ →
      Pr ((fun ω => regW (regM N N' T ω)) ⁻¹' Γ) = Pr ((fun ω => regW (N ω)) ⁻¹' Γ) := by
    intro Γ hΓ
    have := key (A := univ) MeasurableSet.univ hΓ
    simp only [univ_inter, measure_univ, one_mul] at this
    exact this
  refine ⟨?_, ?_⟩
  · rw [Indep_iff]
    rintro t1 t2 h1 ⟨Γ, hΓ, rfl⟩
    rw [hlawW hΓ]
    exact key h1 hΓ
  · ext Γ hΓ
    rw [Measure.map_apply hWM hΓ, Measure.map_apply hWN hΓ]
    exact hlawW hΓ

end ElboimSly.Cyclic

end
