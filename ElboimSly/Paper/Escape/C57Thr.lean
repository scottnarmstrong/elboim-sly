/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C57Final
public import ElboimSly.Paper.Escape.Plan5Count
public import Mathlib

/-!
# ES22 Claim 5.7 with the numerical thresholds only

ES22 Claim 5.7.

`es5_7_thr`: `es5_7_cond` with the counting hypothesis replaced by its numerical input
(`n ≥ n_D`, `ln β ≤ n^{17}/7`, the choice `r_7(d)` of `L₇`).  What remains are the thresholds
of the proof: the levels, `L₇`, `t₇` and the error terms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Brownian ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ}

theorem es5_7_thr (hd : 5 ≤ k + 2) :
    ∃ nD : ℕ, ∃ C₄₃ C₄₂ : ℝ, 0 < C₄₃ ∧ 0 < C₄₂ ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ),
      Es4Params (k + 2) β n₀ n t₀ → ∀ {Ω : Type} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
        {Pr : Measure Ω} {N N' N'' : Ω → Measure (CycS ℕ (k + 2) β)},
        IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr →
        IsPoissonPointProcess N' (cycIntensity ℕ (k + 2) β) Pr →
        IsPoissonPointProcess N''
          ((Measure.count : Measure ℕ).prod (ringIntensity (k + 2) β)) Pr →
        Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr →
        Indep (MeasurableSpace.comap N' inferInstance)
          (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr →
        Indep (MeasurableSpace.comap N'' inferInstance)
          (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ MeasurableSpace.comap N' inferInstance ⊔
            cycNull Pr) Pr →
        𝒢₀ ≤ mΩ → ∀ (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β),
        1 ≤ i → i ≤ escIstar n (escJ n) → 2 ≤ n → (n : ℝ) ^ 20 ≤ 2 ^ escJ n → 4 ≤ escJ n →
        16 * (escIstar n (escJ n) * escLambda n) ≤ 3 * 2 ^ escJ n →
        (4 : ℝ) ^ n₀ < 4 ^ escJ n → (4 : ℝ) ^ escJ n ≤ 4 ^ n →
        ((4 : ℝ) ^ escJ n) ^ indThetaH < (2 : ℝ) ^ escJ n / 64 →
        ∀ {S : ℝ≥0}, (S : ℝ) = ((2 : ℝ) ^ escJ n) ^ 2 / 4 → 0 < S → (S : ℝ) ≤ 4 ^ n →
        ∀ {t7 L7 : ℝ}, (4 : ℝ) ^ (n₀ + 1) ≤ t7 → t7 ≤ (4 : ℝ) ^ n → t7 ^ indThetaH ≤ L7 + 1 →
        L7 + 1 ≤ t7 ^ (1 / 2 : ℝ) → (4 : ℝ) ^ (n₀ + 1) ≤ L7 → L7 ≤ (4 : ℝ) ^ n →
        0 ≤ C₄₃ * (L7 + 1) ^ (k + 2 - 2) * t7 ^ (-((k + 2 - 2 : ℕ) : ℝ) / 2) →
        0 ≤ C₄₂ * L7 ^ (-(1 : ℝ) / 30) →
        max (Real.log β) 10 ≤ L7 + 1 →
        t7 + 4 * (L7 + 1) ^ 2 * Real.log (L7 + 1) ^ 2 < β →
        L7 + 1 < (n : ℝ) ^ 17 / 6 - 2 →
        nD ≤ n → Real.exp 2 ≤ Real.log β → Real.log β ≤ (n : ℝ) ^ 17 / 7 →
        (2 : ℝ) ^ escJ n < 2 * n ^ 20 → escIstar n (escJ n) ≤ n ^ 3 →
        (∀ r : ℝ, L7 ≤ r → 3 ^ (k + 2) * (6 * 33 ^ (k + 2) * (r + 1) ^ 2 *
          Real.log (r + 1) ^ (2 * (k + 2) + 2)) ≤ r ^ (8 / 3 : ℝ) / 2) →
        ∀ {c : ℝ≥0∞}, c ≤ ENNReal.ofReal (c57 (k + 2)) -
          ENNReal.ofReal (Real.exp (-((avoidLevel ((4 : ℝ) ^ escJ n) : ℕ) : ℝ) ^ 2)) -
          ENNReal.ofReal (C₄₃ * (L7 + 1) ^ (k + 2 - 2) * t7 ^ (-((k + 2 - 2 : ℕ) : ℝ) / 2)) -
          ENNReal.ofReal (C₄₂ * L7 ^ (-(1 : ℝ) / 30)) →
        ∀ᵐ ω ∂Pr, c ≤ resPhi (plan5 n β tn u β' i hlog) Pr N
          (lamT (plan5 n β tn u β' i hlog) N (escIstar n (escJ n) + 1))
          (exitSet (β := β) (escJ n) u S
            (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2))) ω := by
  obtain ⟨C₄₃, C₄₂, h43, h42, H⟩ := es5_7_cond (k := k) hd
  obtain ⟨nD, hnD, Hc⟩ := count_avoid k
  refine ⟨nD, C₄₃, C₄₂, h43, h42, ?_⟩
  intro β _ n₀ n t₀ hp Ω 𝒢₀ mΩ Pr N N' N'' hN hN' hN'' hI1 hI2 hI3 h𝒢 tn u β' i hlog hi1 hiI hn
    hj1 hj4 hIlam hT1 hT2 hε S hS hS0 hS4 t7 L7 ht71 ht72 ht7L hLt hL71 hL72 hεf hεa hL7 hβ hnL
    hnD' hβe hlb hj2 hI hvis c hc
  exact H β n₀ n t₀ hp 𝒢₀ hN hN' hN'' hI1 hI2 hI3 h𝒢 tn u β' i hlog hi1 hiI hn hj1 hj4 hIlam hT1
    hT2 hε hS hS0 hS4 ht71 ht72 ht7L hLt hL71 hL72 hεf hεa hL7 hβ hnL
    (fun ν hν r hr => Hc tn u β' i hlog hν hnD' hβe hlb hj1 hj2 hI hIlam hi1 hiI hL7 hvis r hr) hc

end ElboimSly.Paper.Escape
