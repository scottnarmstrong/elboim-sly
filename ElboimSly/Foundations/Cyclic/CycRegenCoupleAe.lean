/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenCouplePoint
public import ElboimSly.Foundations.Cyclic.CycRegenCoupleCore
public import Mathlib

/-!
# ES22 Lemma 2.1 (c)--(e): the almost-sure wiring at a stopping time

ES22 Lemma 2.1 (c)--(e), proof: "Work on the a.s. event where, in addition,
on `{T < ∞}` the measure `Ñ_T` is good". On `{T = t}`, for a good `N`, `M = regM N N' T` is
`Sh_{Z_0} Ñ` with `Z_0 = (k_t, W(t), L_t)` (`regM_eq`), so the deterministic statements of
`CycRegenCouplePoint` apply (`regen_couple_ae`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (ℕ × RingSpace d β)}

theorem regRegion_eq {T : Ω → WithTop ℝ≥0} {ω : Ω} {t : ℝ≥0} (hT : T ω = t)
    (hg : CycGood (N ω)) :
    cycRegionStop (regPlan d β) (cycNgood N) T ω = regRegion (N ω) t := by
  have : cycNgood N ω = N ω := by simp [cycNgood, hg]
  unfold cycRegionStop cycRegionAt regRegion
  rw [hT]
  simp only [WithTop.recTopCoe_coe, this]

theorem regM_eq {T : Ω → WithTop ℝ≥0} {ω : Ω} {t : ℝ≥0} (hT : T ω = t)
    (hg : CycGood (N ω)) (h1 : N ω ∈ lfSet (cycIntensity ℕ d β))
    (h2 : N' ω ∈ lfSet (cycIntensity ℕ d β)) :
    regM N N' T ω = cycShift (regZ0 (N ω) t) (tildeEnv (N ω) (N' ω) (regRegion (N ω) t)) := by
  classical
  have hne : T ω ≠ ⊤ := by rw [hT]; exact WithTop.coe_ne_top
  have hng : cycNgood N ω = N ω := by simp [cycNgood, hg]
  have hstop : ElboimSly.SRW.stopReal T ω = t := by
    unfold ElboimSly.SRW.stopReal; rw [hT]; rfl
  have hZ : regZ N T ω = regZ0 (N ω) t := by
    unfold regZ cycRecStop regZ0
    rw [hstop, hng]
    exact recZ_trunc_regPlan hg t
  have hY : regYtil N N' T ω = tildeEnv (N ω) (N' ω) (regRegion (N ω) t) := by
    unfold regYtil tildeMeasure
    beta_reduce
    rw [regRegion_eq hT hg, tau_of_mem _ h1, tau_of_mem _ h2]
  unfold regM
  rw [ite_eq_left hne, hZ, hY]

theorem ae_tilde_good_aux (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr)
    (hN' : IsPoissonPointProcess N' (cycIntensity ℕ d β) Pr)
    (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
    (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
      (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)
    (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt (regPlan d β) 𝒢₀ hN.measurable h𝒢 Pr) T) :
    ∀ᵐ ω ∂Pr, T ω ≠ ⊤ →
      CycGood (tildeMeasure N N' (cycRegionStop (regPlan d β) (cycNgood N) T) ω) := by
  obtain ⟨-, -, -, -, -, hb, -, -, -⟩ :=
    cyc_multi_exploration_a (regPlan d β) 𝒢₀ hN hN' hI1 hI2 hK_regPlan' h𝒢 hT
  have hFm : MeasurableSet {ν : Measure (ℕ × RingSpace d β) | ¬ CycGood ν} :=
    measurableSet_cycGood.compl
  have h0 := hb MeasurableSet.univ hFm
  have h1 : (Pr.map N) {ν : Measure (ℕ × RingSpace d β) | ¬ CycGood ν} = 0 := by
    rw [Measure.map_apply hN.measurable hFm]
    exact measure_eq_zero_iff_ae_notMem.2 ((ae_cycGood hN).mono fun ω h hn => hn h)
  rw [h1, mul_zero] at h0
  have := measure_eq_zero_iff_ae_notMem.1 h0
  filter_upwards [this] with ω hω hTω
  by_contra hng
  exact hω ⟨⟨mem_univ _, hTω⟩, hng⟩

end ElboimSly.Cyclic

end
