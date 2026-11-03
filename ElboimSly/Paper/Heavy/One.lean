/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.OneDetB

/-!
# Theorem 6.1, conditional on mathbbP(𝒢(i))ge1-e^-cn^3

ES22 Theorem 6.1 (§6, proof ES22 §6).

`es6_one_of_tauhat`: with probability at least `1 - e^{-c_6 n³}`, for every `t ∈ [0, t_n - t_n^ε]`,
`|𝒯 ∩ [t, t + t_n^ε]| ≥ (0.9 + 2/n) t_n^ε`.  The proof is ES22 Lemma 6.12 (`es6_twelve_of_tauhat`) plus
the pathwise statement `es6_one_det` on `𝒢`.

The per-piece bound `hGi` of mathbbP(𝒢(i))ge1-e^-cn^3, the induction hypothesis behind the geometric
premise `hP` of geometric domination of regenerations, and the thresholds `n ≥ N₆` (as `HeavyT`) enter as hypotheses.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω}
  {N : Ω → Measure (ℕ × RingSpace d β)}

/-- ES22 Theorem 6.1, conditional on the per-piece bound `hGi` of mathbbP(𝒢(i))ge1-e^-cn^3. -/
theorem es6_one_of_tauhat {E : HeavyEscConsts} {n₀ n : ℕ} {t₀ : ℝ}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀) (hβ : 15 ≤ β) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    (hβt : β < indScale t₀ n) (hT : HeavyT d n₀ E n)
    (hP : GeoPremise Pe N ((4 : ℝ) ^ n))
    (hGi : ∀ k : ℕ, Pe {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) k)} ≤
      ENNReal.ofReal (heavyA d n * Real.exp (-(heavyc d E * (n : ℝ) ^ 3)))) :
    Pe {ω | ¬ ∀ t : ℝ, 0 ≤ t → t + indScale t₀ n ^ heavyEps d ≤ indScale t₀ n →
        ENNReal.ofReal ((9 / 10 + 2 / (n : ℝ)) * indScale t₀ n ^ heavyEps d) ≤
          volume ({s : ℝ | 0 ≤ s ∧ IsRelaxedTime (geoSlices N ω) s} ∩
            Icc t (t + indScale t₀ n ^ heavyEps d))} ≤
      ENNReal.ofReal (Real.exp (-(heavyC6 d E * (n : ℝ) ^ 3))) := by
  have hn : 4 ≤ n := hT.t4
  have h12 := es6_twelve_of_tauhat (E := E) hN hd hβ hn ht1 ht4 hP hGi hT.t11
  have hgood := ae_cycGood hN
  refine (measure_mono_ae ?_).trans h12
  filter_upwards [hgood] with ω hω hbad
  by_contra hG
  exact hbad fun t ht0 htle =>
    es6_one_det hd hn0 ht1 ht4 hβt hT (fun k => hω k) hG ht0 htle

end ElboimSly.Paper.Heavy
