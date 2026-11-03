/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.TauFastBound
public import ElboimSly.Paper.Heavy.TauHatProb
public import Mathlib

/-!
# MathbbP(𝒢(i))ge1-e^-cn^3 and eq. (tau.bad) with the fast and jump bounds discharged

mathbbP(𝒢(i))ge1-e^-cn^3; Eq. (tau.bad).

`es6_tauhat_of_prime_bad` is `es6_tauhat_of` with `hfast`, `hjump` proved (eq. (taufast),
`es6_taufast_prob`, `es6_taujump_prob`).  `es6_taubad_of_poisson` is `es6_taubad_of` with `hfast`
proved, for the first piece of a Poisson environment.  What remains as hypotheses are the bounds
of corollary after Lemma 6.2 (`hprime`), of ES22 Lemma 6.6, ES22 Lemma 6.7 (`h6`, `h7`), the resulting `hbad`, and the
identical distribution `hiid` of the pieces.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω}
  {N : Ω → Measure (ℕ × RingSpace d β)}

/-- mathbbP(𝒢(i))ge1-e^-cn^3, conditional only on `hprime` (corollary after Lemma 6.2), `hbad`
(eq. (tau.bad)) and `hiid`; the bounds on `τ_fast` and `τ_jump` are eq. (taufast). -/
theorem es6_tauhat_of_prime_bad {E : HeavyEscConsts} {n : ℕ} {t₀ : ℝ} (hd : 5 ≤ d)
    (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hβ : 2 ≤ β)
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (hprime : Pe {ω | heavyTauPrime d t₀ n (fun s : ℝ => cycWalk (cycSlice 0 (N ω)) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (cycSlice 0 (N ω)))} ≤
      ENNReal.ofReal (heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2)) +
        (n + 1) * 5 ^ (d * (n + 1)) *
          (Real.exp (-((n : ℝ) ^ 3 / 17)) + Real.exp (-(E.c5 * (n : ℝ) ^ 3)))))
    (hbad : Pe {ω | heavyTauBad d β t₀ n (fun s : ℝ => cycWalk (cycSlice 0 (N ω)) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (cycSlice 0 (N ω)))} ≤
      ENNReal.ofReal (heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2)) +
        max (Real.exp (-(indDelta d ^ 2 * (n : ℝ) ^ 3 / (2 * 33 ^ d))))
          (Real.exp (-(indDelta d ^ 3 * (n : ℝ) ^ 3 / 2)))))
    (hiid : ∀ k : ℕ, Pe {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) k)} =
      Pe {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) 0)}) (k : ℕ) :
    Pe {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) k)} ≤
      ENNReal.ofReal (heavyA d n * Real.exp (-(heavyc d E * (n : ℝ) ^ 3))) :=
  es6_tauhat_of hd hN
    (es6_taufast_prob ht1 ht4 hβ (isPoissonPointProcess_slice hN 0) n)
    (es6_taujump_prob ht1 ht4 hβ (isPoissonPointProcess_slice hN 0) n) hprime hbad hiid k

/-- Eq. (tau.bad), conditional only on the bounds `h6`, `h7` of ES22 Lemma 6.6 and
ES22 Lemma 6.7; the bound on `τ_fast` is eq. (taufast). -/
theorem es6_taubad_of_poisson {n₀ n : ℕ} {t₀ : ℝ} {E : HeavyEscConsts}
    {env : Ω → Measure (RingSpace d β)} (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    (hβ : 2 ≤ β) (hT : HeavyT d n₀ E n)
    (hν : IsPoissonPointProcess env (ringIntensity d β) Pe) {q₆ q₇ : ℝ}
    (h6 : β < indScale t₀ n ^ (5 * indDelta d) →
      Pe {ω | n < {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n (env ω) ι}.ncard} ≤
        ENNReal.ofReal q₆)
    (h7 : ¬ β < indScale t₀ n ^ (5 * indDelta d) →
      Pe {ω | ∃ ι ∈ heavyBstar d n, HeavyBlockBad d β t₀ n (env ω) ι} ≤ ENNReal.ofReal q₇) :
    Pe {ω | heavyTauBad d β t₀ n (fun s : ℝ => cycWalk (env ω) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))} ≤
      ENNReal.ofReal (heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2))) +
        ENNReal.ofReal (max q₆ q₇) :=
  es6_taubad_of hd ht1 ht4 (by linarith) hT (Interchange.ae_good hν)
    (es6_taufast_prob ht1 ht4 hβ hν n) h6 h7

end ElboimSly.Paper.Heavy
