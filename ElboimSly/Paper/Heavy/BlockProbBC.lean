/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BlockProb
public import ElboimSly.Paper.Heavy.Six
public import ElboimSly.Paper.Heavy.TauHatFast
public import Mathlib

/-!
# Probability that a block is bad, parts (b) and (c); Lemmas 6.6 and 6.7; eq. (tau.bad)

Probability that a block is bad (b), (c), ES22 Lemma 6.6, ES22 Lemma 6.7, eq. (tau.bad).

The single-block bounds follow from `es6_blockprob_a` by (T7) and (T8) and the elementary bounds
`p_ℓ ≤ e^{-ℓ²}` (`p_ℓ = e^{-ℓ³}` when `t_ℓ < β`).  Lemmas 6.6 and 6.7 are then the conditional
statements `es6_six_of_blockprob`, `es6_seven_of_blockprob` with the single-block bound and the
independence at distance (`heavyBlockBad_indep`) supplied.  `es6_taubad` combines them with
`es6_taubad_of_poisson`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem exp_neg_sq_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {m : ℕ} :
    Real.exp (-(y ^ m)) ≤ Real.exp (-(x ^ m)) := by
  apply Real.exp_le_exp.2
  have := pow_le_pow_left₀ hx hxy m
  linarith

/-- Probability that a block is bad (b). -/
theorem es6_blockprob_b {n₀ n : ℕ} {t₀ : ℝ} {E : HeavyEscConsts} (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀)
    (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n) (hβ6 : (10 : ℝ) ^ 14 ≤ β)
    (hβt : β < indScale t₀ n)
    (hH : ∀ n', n₀ ≤ n' → n' < n → ∀ t₀' : ℝ, 1 < t₀' → t₀' ≤ 4 → IndHyp d β n' t₀')
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    (ι : Fin d → ℤ) :
    P {ω | HeavyBlockBad d β t₀ n (copyEnv (N ω) 0) ι} ≤
      ENNReal.ofReal (Real.exp (-(indDelta d ^ 2 * (n : ℝ) ^ 2))) := by
  refine (es6_blockprob_a hd hn0 ht1 ht4 hT hβ6 hβt hH hN ι).trans ?_
  apply ENNReal.ofReal_le_ofReal
  refine le_trans ?_ hT.t7.1
  obtain ⟨⟨hκk, hk'⟩, ⟨hn0k, hlt, hkn⟩, -⟩ := scales_facts_a hd hn0 ht1 ht4 hT
  have hκ0 : 0 ≤ heavyKappa d n := le_trans (Nat.cast_nonneg _) hT.t1.1
  have hk'R : (heavyKappa d n) ≤ (heavyLevelPrime d t₀ n : ℝ) := hκk
  have hkR : (heavyKappa d n) ≤ (heavyLevel d n : ℝ) :=
    hκk.trans (by exact_mod_cast hlt.le)
  have h1 : indFailBound β (heavyT0pp d t₀ n) (heavyLevelPrime d t₀ n) ≤
      Real.exp (-(heavyKappa d n) ^ 2) := by
    refine (indFailBound_le _ _ _).trans ?_
    apply Real.exp_le_exp.2
    have := pow_le_pow_left₀ hκ0 hk'R 2
    linarith
  have h2 : indFailBound β t₀ (heavyLevel d n) ≤ Real.exp (-(heavyKappa d n) ^ 2) := by
    refine (indFailBound_le _ _ _).trans ?_
    apply Real.exp_le_exp.2
    have := pow_le_pow_left₀ hκ0 hkR 2
    linarith
  have hpos : 0 ≤ (9 * 2 ^ heavyLevel d n : ℝ) ^ (2 * d) * (4 ^ (n + 1) + 1) ^ 2 := by positivity
  apply mul_le_mul_of_nonneg_left _ hpos
  linarith

/-- Probability that a block is bad (c). -/
theorem es6_blockprob_c {n₀ n : ℕ} {t₀ : ℝ} {E : HeavyEscConsts} (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀)
    (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n) (hβ6 : (10 : ℝ) ^ 14 ≤ β)
    (hβt : β < indScale t₀ n) (hβ5 : indScale t₀ n ^ (5 * indDelta d) ≤ β)
    (hH : ∀ n', n₀ ≤ n' → n' < n → ∀ t₀' : ℝ, 1 < t₀' → t₀' ≤ 4 → IndHyp d β n' t₀')
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    (ι : Fin d → ℤ) :
    P {ω | HeavyBlockBad d β t₀ n (copyEnv (N ω) 0) ι} ≤
      ENNReal.ofReal (Real.exp (-(indDelta d ^ 3 * (n : ℝ) ^ 3))) := by
  refine (es6_blockprob_a hd hn0 ht1 ht4 hT hβ6 hβt hH hN ι).trans ?_
  apply ENNReal.ofReal_le_ofReal
  refine le_trans ?_ hT.t8.1
  obtain ⟨⟨hκk, hk'⟩, ⟨hn0k, hlt, hkn⟩, -⟩ := scales_facts_a hd hn0 ht1 ht4 hT
  obtain ⟨hd1, hd2, -⟩ := scales_facts_d hd ht1 ht4 hT
  have hk16 := hT.t1.2
  have hκ0 : 0 ≤ heavyKappa d n := le_trans (Nat.cast_nonneg _) hT.t1.1
  have hk'R : (heavyKappa d n) ≤ (heavyLevelPrime d t₀ n : ℝ) := hκk
  have hkR : (heavyKappa d n) ≤ (heavyLevel d n : ℝ) :=
    hκk.trans (by exact_mod_cast hlt.le)
  have hS := blockScales_of hd hn0 ht1 ht4 hT
  obtain ⟨h1t, h4t, et⟩ := heavyT0pp_spec (d := d) (t₀ := t₀) (n := n) hS.tk_gt
  have hfb1 : indFailBound β (heavyT0pp d t₀ n) (heavyLevelPrime d t₀ n) =
      Real.exp (-((heavyLevelPrime d t₀ n : ℝ) ^ 3)) := by
    unfold indFailBound
    rw [ite_eq_left]
    rw [et]; linarith
  have hfb2 : indFailBound β t₀ (heavyLevel d n) = Real.exp (-((heavyLevel d n : ℝ) ^ 3)) := by
    unfold indFailBound
    rw [ite_eq_left]
    linarith
  have h1 : indFailBound β (heavyT0pp d t₀ n) (heavyLevelPrime d t₀ n) ≤
      Real.exp (-(heavyKappa d n) ^ 3) := by
    rw [hfb1]; exact exp_neg_sq_le hκ0 hk'R
  have h2 : indFailBound β t₀ (heavyLevel d n) ≤ Real.exp (-(heavyKappa d n) ^ 3) := by
    rw [hfb2]; exact exp_neg_sq_le hκ0 hkR
  have hpos : 0 ≤ (9 * 2 ^ heavyLevel d n : ℝ) ^ (2 * d) * (4 ^ (n + 1) + 1) ^ 2 := by positivity
  apply mul_le_mul_of_nonneg_left _ hpos
  linarith

/-- ES22 Lemma 6.6, unconditional. -/
theorem es6_six {n₀ n : ℕ} {t₀ : ℝ} {E : HeavyEscConsts} (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀)
    (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n) (hβ6 : (10 : ℝ) ^ 14 ≤ β)
    (hβt : β < indScale t₀ n) (_h5 : β < indScale t₀ n ^ (5 * indDelta d))
    (hH : ∀ n', n₀ ≤ n' → n' < n → ∀ t₀' : ℝ, 1 < t₀' → t₀' ≤ 4 → IndHyp d β n' t₀')
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P) :
    P {ω | n < {ι | ι ∈ heavyBstar d n ∧
        HeavyBlockBad d β t₀ n (copyEnv (N ω) 0) ι}.ncard} ≤
      ENNReal.ofReal (Real.exp (-(indDelta d ^ 2 * (n : ℝ) ^ 3 / (2 * 33 ^ d)))) := by
  have hbl : ∀ ι, P {ω | HeavyBlockBad d β t₀ n (copyEnv (N ω) 0) ι} ≤
      ENNReal.ofReal (Real.exp (-(indDelta d ^ 2 * (n : ℝ) ^ 2))) := fun ι =>
    es6_blockprob_b hd hn0 ht1 ht4 hT hβ6 hβt hH hN ι
  have h1 : 1 ≤ n := by have := hT.t4; omega
  exact es6_six_of_blockprob (env := fun ω => copyEnv (N ω) 0) h1 hT.t7.2 (fun ι _ => hbl ι)
    (fun A hA => heavyBlockBad_indep (Roots.isPoissonPointProcess_copyEnv hN 0) t₀ n A hA)

/-- ES22 Lemma 6.7, unconditional. -/
theorem es6_seven {n₀ n : ℕ} {t₀ : ℝ} {E : HeavyEscConsts} (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀)
    (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n) (hβ6 : (10 : ℝ) ^ 14 ≤ β)
    (hβt : β < indScale t₀ n) (h5 : indScale t₀ n ^ (5 * indDelta d) ≤ β)
    (hH : ∀ n', n₀ ≤ n' → n' < n → ∀ t₀' : ℝ, 1 < t₀' → t₀' ≤ 4 → IndHyp d β n' t₀')
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P) :
    P {ω | ∃ ι ∈ heavyBstar d n, HeavyBlockBad d β t₀ n (copyEnv (N ω) 0) ι} ≤
      ENNReal.ofReal (Real.exp (-(indDelta d ^ 3 * (n : ℝ) ^ 3 / 2))) := by
  have h1 : 1 ≤ n := by have := hT.t4; omega
  exact es6_seven_of_blockprob (env := fun ω => copyEnv (N ω) 0) h1 hT.t8.2
    (fun ι _ => es6_blockprob_c hd hn0 ht1 ht4 hT hβ6 hβt h5 hH hN ι)

/-- Eq. (tau.bad), unconditional: the bounds of ES22 Lemma 6.6 and ES22 Lemma 6.7 are
discharged. -/
theorem es6_taubad {n₀ n : ℕ} {t₀ : ℝ} {E : HeavyEscConsts} (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀)
    (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n) (hβ6 : (10 : ℝ) ^ 14 ≤ β)
    (hβt : β < indScale t₀ n)
    (hH : ∀ n', n₀ ≤ n' → n' < n → ∀ t₀' : ℝ, 1 < t₀' → t₀' ≤ 4 → IndHyp d β n' t₀')
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P) :
    P {ω | heavyTauBad d β t₀ n (fun s : ℝ => cycWalk (copyEnv (N ω) 0) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (copyEnv (N ω) 0))} ≤
      ENNReal.ofReal (heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2)) +
        max (Real.exp (-(indDelta d ^ 2 * (n : ℝ) ^ 3 / (2 * 33 ^ d))))
          (Real.exp (-(indDelta d ^ 3 * (n : ℝ) ^ 3 / 2)))) := by
  have hβ2 : 2 ≤ β := by
    have : (2 : ℝ) ≤ 10 ^ 14 := by norm_num
    linarith
  have := es6_taubad_of_poisson (env := fun ω => copyEnv (N ω) 0) (Pe := P) (n₀ := n₀)
    (E := E) hd ht1 ht4 hβ2 hT (Roots.isPoissonPointProcess_copyEnv hN 0)
    (q₆ := Real.exp (-(indDelta d ^ 2 * (n : ℝ) ^ 3 / (2 * 33 ^ d))))
    (q₇ := Real.exp (-(indDelta d ^ 3 * (n : ℝ) ^ 3 / 2)))
    (fun h5 => es6_six hd hn0 ht1 ht4 hT hβ6 hβt h5 hH hN)
    (fun h5 => es6_seven hd hn0 ht1 ht4 hT hβ6 hβt (not_lt.1 h5) hH hN)
  refine this.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg (heavyCJ_pos (d := d)).le (by positivity))
    (Real.exp_pos _).le) (le_max_of_le_left (Real.exp_pos _).le)]

end ElboimSly.Paper.Heavy
