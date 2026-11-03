/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.TwoCount
public import ElboimSly.Paper.Heavy.EscMeas
public import ElboimSly.Paper.Heavy.TwoTransfer
public import ElboimSly.Foundations.Cyclic.CycMultiGood
public import ElboimSly.Paper.Heavy.ScalesFactsB
public import ElboimSly.Foundations.Cyclic.CycRegenEnvAe

/-!
# Lemma 6.2, conditional on the interface with §5

ES22 Lemma 6.2 (§6).

`es6_two_of_interface`: under the standing assumptions, for `m ≥ m₀` and `B ∈ ℬ_m`,
`P(τ'(B) ≤ t_n ∧ t_reg) ≤ e^{-n³/17} + e^{-c₅ n³}`.

The only inputs beyond the setting are the distinctly named hypotheses
* `hI : HeavyEscInterface...`, the conclusion of interface with S6 (§5);
* `hAd`, the adaptedness of the regenerated walk to `avoidFilt` (ES22 Lemma 2.1 (a)).

The probability is that of the event for the first piece `W^{N^1}` of the regenerated walk, which
coincides with the one for `W` on `[0, t_reg]` (the functionals before closing, `tauPrimeBlock_regen_iff`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- ES22 Lemma 6.2, conditional on the interface interface with S6. -/
theorem es6_two_of_interface {E : HeavyEscConsts} {n₀ n : ℕ} {t₀ : ℝ}
    (hI : HeavyEscInterface d β E n₀ n t₀) {Ω : Type} (𝒢₀ : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] {Pr : Measure Ω} {N N' : Ω → Measure (CycS ℕ d β)}
    (S : Es4Setting d β n₀ n t₀ 𝒢₀ Pr N N') (hT : HeavyT d n₀ E n) (hβ5 : E.beta5 ≤ β)
    {m : ℕ} (hm : heavyM0 d t₀ n ≤ m) (ι : Fin d → ℤ) :
    Pr {ω | heavyTauPrimeBlock d n (fun s : ℝ => cycWalk (cycSlice 0 (N ω)) 0 0 s) m ι ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (cycSlice 0 (N ω)))} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 3 / 17)) + Real.exp (-(E.c5 * (n : ℝ) ^ 3))) := by
  have := S.space.ppp.isProbabilityMeasure
  have hβ : 0 < β := Fact.out
  have hp := S.params
  have hAd := avoidWalk_cycNgood_adapted S
  have hn3 : 3 ≤ n := by have := hT.t4; omega
  have hjm : heavyScaleJ n ≤ m := (scales_facts_b hp.five_le hp.one_lt hp.le_four hT).1.trans hm
  have hE : ∀ ι', MeasurableSet
      (heavyEscSet (avoidWalk (cycNgood N)) n (heavyScaleJ n)
        (heavyXi (avoidWalk (cycNgood N)) (heavyScaleJ n) ι')) :=
    fun ι' => measurableSet_heavyEscSet hAd
      (hAd.isStoppingTime_entrance (heavyBlock (heavyScaleJ n) ι')).measurable' (by omega) _
  have hTcl : IsStoppingTime (avoidFilt 𝒢₀ S.space)
      (fun ω => cycClosingTime β (avoidWalk (cycNgood N) ω)) :=
    hAd.isStoppingTime_cycClosingTime hβ
  have htn0 : 0 ≤ indScale t₀ n :=
    ((by positivity : (0 : ℝ) ≤ 4 ^ n)).trans (indScale_gt_four_pow hp.one_lt n).le
  have hcount := heavy_two_count (μ := Pr) hAd hn3 hjm ι htn0 (indScale_le_four_pow hp.le_four n)
    hE hTcl
  have hint := hI 𝒢₀ S hβ5 (heavyEscVersion hAd Pr n)
    (fun ι' => (stronglyMeasurable_condExp).measurable) (fun ι' => Filter.EventuallyEq.rfl)
  have hg : ∀ ω k, Good (avoidEnv (cycNgood N) ω k) := by
    intro ω k; rw [avoidEnv_eq_cycSlice]; exact cycGood_cycNgood N ω k
  have hcl : ∀ ω, cycClosingTime β (avoidWalk (cycNgood N) ω) =
      cycTreg (avoidEnv (cycNgood N) ω 0) := fun ω =>
    cycClosingTime_regenWalk (hg ω) (hAd.path ω)
  have hae := ae_cycNgood_eq S.space.ppp
  have h1 : Pr {ω | heavyTauPrimeBlock d n (fun s : ℝ => cycWalk (cycSlice 0 (N ω)) 0 0 s) m ι ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (cycSlice 0 (N ω)))} ≤
      Pr {ω | heavyTauPrimeBlock d n (avoidWalk (cycNgood N) ω) m ι ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycClosingTime β (avoidWalk (cycNgood N) ω))} := by
    refine measure_mono_ae ?_
    filter_upwards [hae] with ω hω hmem
    have e0 : avoidEnv (cycNgood N) ω 0 = cycSlice 0 (N ω) := by
      rw [avoidEnv_eq_cycSlice, hω]
    have := (tauPrimeBlock_regen_iff (ν := avoidEnv (cycNgood N) ω) (hg ω) (hAd.path ω) n m ι
      (tn := indScale t₀ n)).2
    rw [hcl]
    exact this (by rw [e0]; exact hmem)
  have h2 : Pr {ω | heavyTauV (avoidWalk (cycNgood N) ω) (heavyScaleJ n)
        (fun ι' => heavyEscVersion hAd Pr n ι' ω) ((n : ℝ) ^ (-escGamma d)) <
        min (ENNReal.ofReal (indScale t₀ n))
          (cycClosingTime β (avoidWalk (cycNgood N) ω))} ≤
      ENNReal.ofReal (Real.exp (-(E.c5 * (n : ℝ) ^ 3))) := by
    refine le_trans (le_of_eq ?_) hint
    congr 1
    ext ω
    simp only [mem_ofPred_eq, hcl]
  calc _ ≤ _ := h1
    _ ≤ _ := hcount
    _ ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 3 / 17))) +
        ENNReal.ofReal (Real.exp (-(E.c5 * (n : ℝ) ^ 3))) := add_le_add le_rfl h2
    _ = _ := by rw [ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]

end ElboimSly.Paper.Heavy
