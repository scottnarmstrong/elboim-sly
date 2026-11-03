/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenCoupleAe
public import Mathlib

/-!
# ES22 Lemma 2.1 (c)--(e): almost-sure statements

ES22 Lemma 2.1 (c), (d), (e). For the environment `M = regM N N' T`, almost
surely on `{T = t}` (writing `ν^· = slices (N ω)`, `W = regenWalk ν^·`, `W' = regenWalk (slices M)`,
`α = regenStart`, `thit = cycThit`):
* `M` is good;
* (c) `W(t + s) - W(t) = W'(s)` for `t + s ≤ thit(t)`; and if `α(t) < t`, the first piece of `W'`
  does not close before `thit(t) - t`;
* (d) `thit(t) = ∞` if `α(t) = t`, and `thit(t) ≤ σ_{k_t + 1}` if `α(t) < t`;
* (e) `thit(t) = inf {s > t : ∃ s' ∈ s + βℤ, α(t) < s' < t, ‖W(t) + W'(s - t) - W(s')‖ ≤ 1}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (ℕ × RingSpace d β)}

theorem regen_couple_ae (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr)
    (hN' : IsPoissonPointProcess N' (cycIntensity ℕ d β) Pr)
    (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
    (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
      (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)
    (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt (regPlan d β) 𝒢₀ hN.measurable h𝒢 Pr) T) :
    ∀ᵐ ω ∂Pr, CycGood (N ω) ∧ ∀ t : ℝ≥0, T ω = t →
      CycGood (regM N N' T ω) ∧
      (∀ s : ℝ≥0, ENNReal.ofReal ((t : ℝ) + s) ≤ ElboimSly.cycThit (slices (N ω)) (t : ℝ) →
        ElboimSly.regenWalk (slices (N ω)) ((t : ℝ) + s) -
            ElboimSly.regenWalk (slices (N ω)) (t : ℝ) =
          ElboimSly.regenWalk (slices (regM N N' T ω)) (s : ℝ)) ∧
      (ElboimSly.regenStart (slices (N ω)) (t : ℝ) < t →
        ∀ s : ℝ≥0, ENNReal.ofReal ((t : ℝ) + s) ≤ ElboimSly.cycThit (slices (N ω)) (t : ℝ) →
          (s : ℝ≥0∞) < ElboimSly.cycTreg (slices (regM N N' T ω) 0)) ∧
      (ElboimSly.regenStart (slices (N ω)) (t : ℝ) = t →
        ElboimSly.cycThit (slices (N ω)) (t : ℝ) = ⊤) ∧
      (ElboimSly.regenStart (slices (N ω)) (t : ℝ) < t →
        ElboimSly.cycThit (slices (N ω)) (t : ℝ) ≤
          ElboimSly.regenSigma (slices (N ω)) (ElboimSly.regenCount (slices (N ω)) (t : ℝ) + 1)) ∧
      (ElboimSly.cycThit (slices (N ω)) (t : ℝ) =
        ⨅ s ∈ {s : ℝ | (t : ℝ) < s ∧ ∃ s' : ℝ, (∃ kk : ℤ, s' = s + kk * β) ∧
          ElboimSly.regenStart (slices (N ω)) (t : ℝ) < s' ∧ s' < t ∧
          ‖ElboimSly.regenWalk (slices (N ω)) (t : ℝ) +
            ElboimSly.regenWalk (slices (regM N N' T ω)) (s - t) -
              ElboimSly.regenWalk (slices (N ω)) s'‖ ≤ 1},
          ENNReal.ofReal s) := by
  filter_upwards [ae_cycGood hN, hN.ae_mem_lfSet, hN'.ae_mem_lfSet,
    ae_tilde_good_aux 𝒢₀ hN hN' hI1 hI2 h𝒢 hT] with ω hg h1 h2 hÑ
  refine ⟨hg, fun t hTt => ?_⟩
  have hne : T ω ≠ ⊤ := by rw [hTt]; exact WithTop.coe_ne_top
  have hÑ' : CycGood (tildeEnv (N ω) (N' ω) (regRegion (N ω) t)) := by
    have := hÑ hne
    unfold tildeMeasure at this
    rw [regRegion_eq hTt hg] at this
    exact this
  have hlf : tildeEnv (N ω) (N' ω) (regRegion (N ω) t) ∈ lfSet (cycIntensity ℕ d β) :=
    tilde_mem_lfSet _ h1 h2 _
  have hM := regM_eq hTt hg h1 h2
  have hgood := good_slices_regShift hg t hÑ' hlf
  have hgk : ∀ j, Good (slices (N ω) j) := hg
  refine ⟨?_, fun s hs => ?_, fun hlt s hs => ?_, fun heq => ?_, fun hlt => ?_, ?_⟩
  · rw [hM]; exact hgood
  · rw [hM]; exact (regen_agree_M hg t hÑ' hlf hs).symm
  · rw [hM]
    refine regen_first_open_M hg t hÑ' hlf ?_ hs
    rw [← NNReal.coe_pos, regLast_coe]
    linarith
  · exact cycThit_eq_top heq
  · exact cycThit_le_sigma hgk t.2 (by linarith)
  · rw [hM]; exact regen_thit_eq_M hg t hÑ' hlf

end ElboimSly.Cyclic

end
