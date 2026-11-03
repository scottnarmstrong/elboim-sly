/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Two
public import ElboimSly.Paper.Heavy.Cor63
public import ElboimSly.Paper.Heavy.TauFastBound
public import ElboimSly.Paper.Heavy.ThrE

/-!
# Corollary 6.3, conditional on the interface with §5

Corollary after Lemma 6.2 (ES22 §6, eq. (tau')).

`es6_three_of_interface`:
`P(τ' ≤ t_n ∧ t_reg) ≤ ϖ_n + (n+1) 5^{d(n+1)} (e^{-n³/17} + e^{-c₅ n³})`, from
`es6_two_of_interface`, `es6_taufast_prob` and the union bound `es6_three_of_two`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Corollary after Lemma 6.2, conditional on the interface interface with S6. -/
theorem es6_three_of_interface {E : HeavyEscConsts} {n₀ n : ℕ} {t₀ : ℝ}
    (hI : HeavyEscInterface d β E n₀ n t₀) {Ω : Type} (𝒢₀ : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] {Pr : Measure Ω} {N N' : Ω → Measure (CycS ℕ d β)}
    (S : Es4Setting d β n₀ n t₀ 𝒢₀ Pr N N') (hT : HeavyT d n₀ E n) (hβ5 : E.beta5 ≤ β) :
    Pr {ω | heavyTauPrime d t₀ n (fun s : ℝ => cycWalk (cycSlice 0 (N ω)) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (cycSlice 0 (N ω)))} ≤
      ENNReal.ofReal (heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2)) +
        (n + 1) * 5 ^ (d * (n + 1)) *
          (Real.exp (-((n : ℝ) ^ 3 / 17)) + Real.exp (-(E.c5 * (n : ℝ) ^ 3)))) := by
  have hp := S.params
  have hβ2 : 2 ≤ β := by linarith [hp.beta_sigma, (by norm_num : (2 : ℝ) ≤ 10 ^ 14)]
  have hν : IsPoissonPointProcess (fun ω => cycSlice 0 (N ω)) (ringIntensity d β) Pr :=
    isPoissonPointProcess_slice S.space.ppp 0
  have hgood : ∀ᵐ ω ∂Pr, Good (cycSlice 0 (N ω)) := Interchange.ae_good hν
  have hfast := es6_taufast_prob (Pe := Pr) hp.one_lt hp.le_four hβ2 hν n
  have h3 := es6_three_of_two (Pe := Pr) (env := fun ω => cycSlice 0 (N ω)) (n₀ := n₀)
    (E := E) hp.one_lt hp.le_four hT hgood hfast
    (q := Real.exp (-((n : ℝ) ^ 3 / 17)) + Real.exp (-(E.c5 * (n : ℝ) ^ 3)))
    (fun m ι hm => es6_two_of_interface hI 𝒢₀ S hT hβ5 hm ι)
  refine h3.trans (le_of_eq ?_)
  have hq : 0 ≤ Real.exp (-((n : ℝ) ^ 3 / 17)) + Real.exp (-(E.c5 * (n : ℝ) ^ 3)) := by positivity
  have hcj : 0 ≤ heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2)) := by
    have := heavyCJ_pos (d := d); positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add hcj (by positivity)]
  congr 1
  push_cast
  ring

end ElboimSly.Paper.Heavy
