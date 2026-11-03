/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Three
public import ElboimSly.Paper.Heavy.TauHatIid
public import ElboimSly.Paper.Heavy.BlockProbBC

/-!
# MathbbP(𝒢(i))ge1-e^-cn^3, conditional on the interface with §5

mathbbP(𝒢(i))ge1-e^-cn^3 (ES22 §6, ES22 §6).

`es6_tauhat_of_interface`: `P(𝒢(i)ᶜ) ≤ A_n e^{-c_♭ n³}` for every piece `i`, from
`es6_tauhat_given_prime_bad`, `es6_taubad` and `es6_three_of_interface`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- mathbbP(𝒢(i))ge1-e^-cn^3, conditional on the interface interface with S6. -/
theorem es6_tauhat_of_interface {E : HeavyEscConsts} {n₀ n : ℕ} {t₀ : ℝ}
    (hI : HeavyEscInterface d β E n₀ n t₀) {Ω : Type} (𝒢₀ : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] {Pr : Measure Ω} {N N' : Ω → Measure (CycS ℕ d β)}
    (S : Es4Setting d β n₀ n t₀ 𝒢₀ Pr N N') (hT : HeavyT d n₀ E n) (hβ5 : E.beta5 ≤ β)
    (k : ℕ) :
    Pr {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) k)} ≤
      ENNReal.ofReal (heavyA d n * Real.exp (-(heavyc d E * (n : ℝ) ^ 3))) := by
  have hp := S.params
  have hβ2 : 2 ≤ β := by linarith [hp.beta_sigma, (by norm_num : (2 : ℝ) ≤ 10 ^ 14)]
  have hn : 1 ≤ n := by have := hT.t4; omega
  have hbad := es6_taubad hp.five_le hp.eight_le hp.one_lt hp.le_four hT hp.beta_sigma hp.beta_lt
    hp.ind S.space.ppp
  have e : ∀ ω, copyEnv (N ω) 0 = cycSlice 0 (N ω) := fun ω => congrFun (avoidEnv_eq_cycSlice N ω) 0
  simp only [e] at hbad
  exact es6_tauhat_given_prime_bad hp.five_le hp.one_lt hp.le_four hβ2 hn S.space.ppp
    (es6_three_of_interface hI 𝒢₀ S hT hβ5) hbad k

end ElboimSly.Paper.Heavy
