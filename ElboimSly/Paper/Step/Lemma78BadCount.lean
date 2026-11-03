/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BlockProbBC
public import ElboimSly.Paper.Heavy.GoodLocalMeas
public import ElboimSly.Paper.Heavy.GoodLocalIndep
public import ElboimSly.Paper.Heavy.Six
public import ElboimSly.Paper.Heavy.Seven

/-!
# Bad blocks for a single Poisson environment

Discovered bad blocks for two walks, "Counting" (ES22 §7), using ES22 Lemma 6.6 and ES22 Lemma 6.7 for a
single, non-regenerated environment `N₀` (applied to `N` and to the shifted environment `N*`). The
single-block bounds of probability that a block is bad (b), (c) are transferred from the regenerated setting
by uniqueness in law.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Heavy

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Law transfer for the event `{B bad}`: a single environment has the same block-badness
probability as the first copy of a regenerated one. -/
theorem blockBad_single_eq {t₀ : ℝ} {n : ℕ} (ι : Fin d → ℤ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N₀ : Ω → Measure (RingSpace d β)}
    (hN₀ : IsPoissonPointProcess N₀ (ringIntensity d β) P)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {N : Ω' → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P') :
    P {ω | HeavyBlockBad d β t₀ n (N₀ ω) ι} =
      P' {ω | HeavyBlockBad d β t₀ n (copyEnv (N ω) 0) ι} := by
  have h0 := Roots.isPoissonPointProcess_copyEnv hN 0
  have hlaw := hN₀.map_eq_map h0
  have hm := measurableSet_heavyBlockBad (d := d) (β := β) t₀ n ι
  have e1 : P {ω | HeavyBlockBad d β t₀ n (N₀ ω) ι} = (P.map N₀) {ν | HeavyBlockBad d β t₀ n ν ι} :=
    (Measure.map_apply hN₀.measurable hm).symm
  have e2 : P' {ω | HeavyBlockBad d β t₀ n (copyEnv (N ω) 0) ι} =
      (P'.map fun ω => copyEnv (N ω) 0) {ν | HeavyBlockBad d β t₀ n ν ι} :=
    (Measure.map_apply h0.measurable hm).symm
  rw [e1, e2, hlaw]

/-- ES22 Lemma 6.6 for a single environment (up to the hypothesis `hH`). -/
theorem es6_six_single {n₀ n : ℕ} {t₀ : ℝ} {E : HeavyEscConsts} (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀)
    (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n) (hβ6 : (10 : ℝ) ^ 14 ≤ β)
    (hβt : β < indScale t₀ n)
    (hH : ∀ n', n₀ ≤ n' → n' < n → ∀ t₀' : ℝ, 1 < t₀' → t₀' ≤ 4 → IndHyp d β n' t₀')
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N₀ : Ω → Measure (RingSpace d β)}
    (hN₀ : IsPoissonPointProcess N₀ (ringIntensity d β) P) :
    P {ω | n < {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n (N₀ ω) ι}.ncard} ≤
      ENNReal.ofReal (Real.exp (-(indDelta d ^ 2 * (n : ℝ) ^ 3 / (2 * 33 ^ d)))) := by
  obtain ⟨Ω', mΩ', P', N, hP', hN, -⟩ :=
    exists_isPoissonPointProcess ((Measure.count : Measure ℕ).prod (ringIntensity d β))
  have h1 : 1 ≤ n := by have := hT.t4; omega
  refine es6_six_of_blockprob (env := N₀) h1 hT.t7.2 (fun ι _ => ?_)
    (fun A hA => heavyBlockBad_indep hN₀ t₀ n A hA)
  rw [blockBad_single_eq ι hN₀ hN]
  exact es6_blockprob_b hd hn0 ht1 ht4 hT hβ6 hβt hH hN ι

/-- ES22 Lemma 6.7 for a single environment (up to the hypothesis `hH`). -/
theorem es6_seven_single {n₀ n : ℕ} {t₀ : ℝ} {E : HeavyEscConsts} (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀)
    (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n) (hβ6 : (10 : ℝ) ^ 14 ≤ β)
    (hβt : β < indScale t₀ n) (h5 : indScale t₀ n ^ (5 * indDelta d) ≤ β)
    (hH : ∀ n', n₀ ≤ n' → n' < n → ∀ t₀' : ℝ, 1 < t₀' → t₀' ≤ 4 → IndHyp d β n' t₀')
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N₀ : Ω → Measure (RingSpace d β)}
    (hN₀ : IsPoissonPointProcess N₀ (ringIntensity d β) P) :
    P {ω | ∃ ι ∈ heavyBstar d n, HeavyBlockBad d β t₀ n (N₀ ω) ι} ≤
      ENNReal.ofReal (Real.exp (-(indDelta d ^ 3 * (n : ℝ) ^ 3 / 2))) := by
  obtain ⟨Ω', mΩ', P', N, hP', hN, -⟩ :=
    exists_isPoissonPointProcess ((Measure.count : Measure ℕ).prod (ringIntensity d β))
  have h1 : 1 ≤ n := by have := hT.t4; omega
  refine es6_seven_of_blockprob (env := N₀) h1 hT.t8.2 (fun ι _ => ?_)
  rw [blockBad_single_eq ι hN₀ hN]
  exact es6_blockprob_c hd hn0 ht1 ht4 hT hβ6 hβt h5 hH hN ι

end ElboimSly.Paper.Step

end
