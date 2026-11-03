/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BlockProbGB
public import ElboimSly.Paper.Heavy.BlockProbCount
public import ElboimSly.Paper.Heavy.BlockProbNum
public import ElboimSly.Frozen.Defs.IndHyp
public import Mathlib

/-!
# Probability that a block is bad, part (a)

Probability that a block is bad (a) (deviations F54, F60).

Let `N` be a Poisson point process of intensity `# ⊗ μ_β` on `ℕ × S_β` (construction (i)) and
`N^1 = copyEnv N 0`.  Under the standing assumptions, with `k = ⌊4δn⌋`, `k'` the scale index of
`t'_k`, `t₀''` the initial time with `t_{k'}(t₀'') = t'_k`:
`P(B bad) ≤ (9·2^k)^{2d} (4^{n+1}+1)² (2 p_{k'} + p_k + 4d e^{-k⁴/3200})`.
(GB1) is (H1) at level `k'`, (GB2) is (H4) at level `k'` with Gaussian maximal bound, (GB3) is (H5) at
level `k`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The scale facts used in the block-probability proof. -/
structure BlockScales (d n₀ n : ℕ) (E : HeavyEscConsts) (t₀ : ℝ) : Prop where
  k16 : 16 ≤ heavyLevel d n
  n0_le : n₀ ≤ heavyLevelPrime d t₀ n
  lt : heavyLevelPrime d t₀ n < heavyLevel d n
  k_lt_n : heavyLevel d n < n
  tk_gt : 1 < heavyTkPrime d t₀ n
  tk_le : heavyTkPrime d t₀ n ≤ (4 : ℝ) ^ (heavyLevel d n + 1) / (heavyLevel d n : ℝ) ^ 4
  tk_theta : heavyTkPrime d t₀ n ^ indThetaH ≤ (2 : ℝ) ^ (heavyLevel d n - 2)

theorem blockScales_of {n₀ n : ℕ} {E : HeavyEscConsts} {t₀ : ℝ} (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀)
    (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n) : BlockScales d n₀ n E t₀ := by
  have hk := hT.t1.2
  obtain ⟨-, ⟨h1, h2, h3⟩, -⟩ := scales_facts_a hd hn0 ht1 ht4 hT
  obtain ⟨c1, c2, c3, c4⟩ := scales_facts_c ht1 ht4 hk
  refine ⟨hk, h1, h2, by omega, ?_, c3, c4⟩
  linarith

/-- The probability that a block is bad: the union bound over the starting data. -/
theorem es6_blockprob_a {n₀ n : ℕ} {t₀ : ℝ} {E : HeavyEscConsts} (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀)
    (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n) (hβ6 : (10 : ℝ) ^ 14 ≤ β)
    (hβt : β < indScale t₀ n)
    (hH : ∀ n', n₀ ≤ n' → n' < n → ∀ t₀' : ℝ, 1 < t₀' → t₀' ≤ 4 → IndHyp d β n' t₀')
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    (ι : Fin d → ℤ) :
    P {ω | HeavyBlockBad d β t₀ n (copyEnv (N ω) 0) ι} ≤
      ENNReal.ofReal ((9 * 2 ^ heavyLevel d n : ℝ) ^ (2 * d) * (4 ^ (n + 1) + 1) ^ 2 *
        (2 * indFailBound β (heavyT0pp d t₀ n) (heavyLevelPrime d t₀ n) +
          indFailBound β t₀ (heavyLevel d n) +
          4 * d * Real.exp (-((heavyLevel d n : ℝ) ^ 4 / 3200)))) := by
  classical
  have hβpos : 0 < β := Fact.out
  set k := heavyLevel d n with hk
  set k' := heavyLevelPrime d t₀ n with hk'
  set tk := heavyTkPrime d t₀ n with htk
  set t0pp := heavyT0pp d t₀ n with ht0pp
  have hS := blockScales_of hd hn0 ht1 ht4 hT
  have htkpos : 0 < tk := by linarith [hS.tk_gt]
  obtain ⟨h1t, h4t, et⟩ := heavyT0pp_spec (d := d) (t₀ := t₀) (n := n) hS.tk_gt
  have hIH := hH k' hS.n0_le (hS.lt.trans hS.k_lt_n) t0pp h1t h4t
  have hIK := hH k (hS.n0_le.trans hS.lt.le) hS.k_lt_n t₀ ht1 ht4
  have hN1 := hIH.1 Ω P N hN
  have henv := Roots.isPoissonPointProcess_copyEnv hN 0
  have hH5 := hIK.2 Ω P (fun ω => copyEnv (N ω) 0) henv
  set p1 := indFailBound β t0pp k' with hp1def
  set p2 := indFailBound β t₀ k with hp2def
  have hp1le : p1 ≤ 1 := indFailBound_le_one β t0pp k'
  have hp1ge : 0 ≤ p1 := indFailBound_nonneg β t0pp k'
  have hp2ge : 0 ≤ p2 := indFailBound_nonneg β t₀ k
  -- (H1)
  have hH1 : ENNReal.ofReal (1 - p1) ≤ P {ω | IsRelaxedPath (fun j => copyEnv (N ω) j) tk} := by
    have := hN1.1
    unfold IndH1 at this
    rw [et] at this
    exact this
  -- (H4)
  have hN4 := hN1.2.2.2
  unfold IndH4 at hN4
  obtain ⟨σ, hσ, hC⟩ := hN4
  have hσ12 := sigma_mem_Icc hβ6 (by rw [et]; exact htkpos) hσ
  rw [et] at hC
  have hσpos : 0 < σ := by linarith [hσ12.1]
  have hεpos : 0 < tk ^ indThetaH := Real.rpow_pos_of_pos htkpos _
  obtain ⟨j, hj⟩ : ∃ j, k = j + 2 := ⟨k - 2, by have := hS.k16; omega⟩
  have hlpos : (0 : ℝ) < 2 ^ (k - 2) := by positivity
  have hR : (2 : ℝ) ^ (k - 1) = 2 * 2 ^ (k - 2) := by
    rw [hj]; simp only [show j + 2 - 1 = j + 1 by omega, Nat.add_sub_cancel]; ring
  have hlR : (2 : ℝ) ^ (k - 2) + tk ^ indThetaH ≤ (2 : ℝ) ^ (k - 1) := by
    rw [hR]; linarith [hS.tk_theta]
  have hE2 : ∀ x : (Fin d → ℤ) × ℤ, P {ω | Good (copyEnv (N ω) 0) ∧ ∃ s ∈ Icc (0 : ℝ) tk,
      (2 : ℝ) ^ (k - 1) < ‖cycWalk (copyEnv (N ω) 0) x.1 x.2 s - x.1‖} ≤
      ENNReal.ofReal p1 + (4 * d : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-((k : ℝ) ^ 4 / 3200))) := by
    intro x
    refine (gb2_prob hN htkpos hσpos hεpos hlpos hlR hC x.1 x.2).trans ?_
    exact add_le_add le_rfl (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
      (gb2_numeric hS.k16 htkpos hS.tk_le hσpos hσ12.2)))
  have hE1 : ∀ x : (Fin d → ℤ) × ℤ, P {ω | Good (copyEnv (N ω) 0) ∧
      ¬ cycClosesBy (copyEnv (N ω) 0) x.1 x.2 tk ∧
      volume {s : ℝ | s ∈ Icc 0 tk ∧
        IsRelaxedTimeWrt β (fun r => cycWalk (copyEnv (N ω) 0) x.1 x.2 r) 0 s} <
        ENNReal.ofReal ((9 / 10 + 1 / (k' : ℝ)) * tk)} ≤ ENNReal.ofReal p1 := fun x =>
    gb1_prob hN htkpos.le (κ := k') rfl hp1le hH1 x.1 x.2
  have hE3 : ∀ x y : (Fin d → ℤ) × ℤ, (0 : ℝ) ≤ x.2 → (x.2 : ℝ) ≤ β → (0 : ℝ) ≤ y.2 →
      (y.2 : ℝ) ≤ β →
      P {ω | cycOmega (copyEnv (N ω) 0) x.1 y.1 x.2 y.2 tk ∧
        ENNReal.ofReal ((3.9 : ℝ) ^ k) ≤
          volume {s₂ : ℝ | s₂ ∈ Icc 0 tk ∧ ∃ s₁ ∈ Icc (0 : ℝ) tk,
            ‖cycWalk (copyEnv (N ω) 0) x.1 x.2 s₁ - cycWalk (copyEnv (N ω) 0) y.1 y.2 s₂‖ ≤
              (1.9 : ℝ) ^ k}} ≤ ENNReal.ofReal p2 := by
    intro x y h1 h2 h3 h4
    have := hH5 x.1 y.1 x.2 y.2 ⟨h1, h2⟩ ⟨h3, h4⟩
    refine le_trans (le_of_eq ?_) this
    congr 1
    ext ω
    simp only [mem_ofPred_eq]
    rw [show tk = indScaleReduced t₀ k from rfl]
    norm_num
  obtain ⟨Uf, hUf, hUfc⟩ := exists_finset_nbhd k ι
  obtain ⟨Q, hQ, hQc⟩ := exists_finset_times n (hβt.le.trans (indScale_le_four_pow ht4 n))
  set D : Finset ((Fin d → ℤ) × ℤ) := Uf ×ˢ Q with hD
  have hmemD : ∀ x : (Fin d → ℤ) × ℤ, x ∈ D ↔
      x.1 ∈ latNbhd (heavyBlock k ι) ((2 : ℝ) ^ (k + 2)) ∧ (0 : ℝ) ≤ x.2 ∧ (x.2 : ℝ) ≤ β := by
    intro x
    simp only [hD, Finset.mem_product, hUf, hQ]
  let E1 : (Fin d → ℤ) × ℤ → Set Ω := fun x => {ω | Good (copyEnv (N ω) 0) ∧
      ¬ cycClosesBy (copyEnv (N ω) 0) x.1 x.2 tk ∧
      volume {s : ℝ | s ∈ Icc 0 tk ∧
        IsRelaxedTimeWrt β (fun r => cycWalk (copyEnv (N ω) 0) x.1 x.2 r) 0 s} <
        ENNReal.ofReal ((9 / 10 + 1 / (k' : ℝ)) * tk)}
  let E2 : (Fin d → ℤ) × ℤ → Set Ω := fun x => {ω | Good (copyEnv (N ω) 0) ∧
      ∃ s ∈ Icc (0 : ℝ) tk, (2 : ℝ) ^ (k - 1) < ‖cycWalk (copyEnv (N ω) 0) x.1 x.2 s - x.1‖}
  let E3 : (Fin d → ℤ) × ℤ → (Fin d → ℤ) × ℤ → Set Ω := fun x y =>
    {ω | cycOmega (copyEnv (N ω) 0) x.1 y.1 x.2 y.2 tk ∧
        ENNReal.ofReal ((3.9 : ℝ) ^ k) ≤
          volume {s₂ : ℝ | s₂ ∈ Icc 0 tk ∧ ∃ s₁ ∈ Icc (0 : ℝ) tk,
            ‖cycWalk (copyEnv (N ω) 0) x.1 x.2 s₁ - cycWalk (copyEnv (N ω) 0) y.1 y.2 s₂‖ ≤
              (1.9 : ℝ) ^ k}}
  have hsub : {ω | HeavyBlockBad d β t₀ n (copyEnv (N ω) 0) ι} ⊆
      (⋃ x ∈ D, (E1 x ∪ E2 x)) ∪ ⋃ x ∈ D, ⋃ y ∈ D, E3 x y := by
    rintro ω ⟨hg, hnot⟩
    by_contra hcon
    apply hnot
    simp only [HeavyBlockGood]
    intro u₁ hu₁ u₂ hu₂ q₁ q₂ h0 h1 h2 h3
    have hx : (u₁, q₁) ∈ D := (hmemD _).2 ⟨hu₁, h0, h1⟩
    have hy : (u₂, q₂) ∈ D := (hmemD _).2 ⟨hu₂, h2, h3⟩
    have hA : ∀ x ∈ D, ω ∉ E1 x ∪ E2 x := fun x hx h =>
      hcon (Or.inl (Set.mem_iUnion₂.2 ⟨x, hx, h⟩))
    have hB : ∀ x ∈ D, ∀ y ∈ D, ω ∉ E3 x y := fun x hx y hy h =>
      hcon (Or.inr (Set.mem_iUnion₂.2 ⟨x, hx, Set.mem_iUnion₂.2 ⟨y, hy, h⟩⟩))
    refine ⟨?_, fun s hs => ?_, fun hΩ => ?_⟩
    · by_contra hc
      obtain ⟨hc1, hc2⟩ := not_or.1 hc
      exact hA _ hx (Or.inl ⟨hg, hc1, not_le.1 hc2⟩)
    · by_contra hc
      exact hA _ hx (Or.inr ⟨hg, s, hs, not_le.1 hc⟩)
    · by_contra hc
      exact hB _ hx _ hy ⟨hΩ, not_lt.1 hc⟩
  -- the union bound
  set a : ℝ≥0∞ := ENNReal.ofReal p1 with ha
  set g : ℝ≥0∞ := (4 * d : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-((k : ℝ) ^ 4 / 3200))) with hg
  set b : ℝ≥0∞ := ENNReal.ofReal p2 with hb
  have hU1 : P (⋃ x ∈ D, (E1 x ∪ E2 x)) ≤ (D.card : ℝ≥0∞) * (a + (a + g)) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ x ∈ D, P (E1 x ∪ E2 x) ≤ ∑ _x ∈ D, (a + (a + g)) := by
          refine Finset.sum_le_sum fun x _ => (measure_union_le _ _).trans ?_
          exact add_le_add (hE1 x) (hE2 x)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hU2 : P (⋃ x ∈ D, ⋃ y ∈ D, E3 x y) ≤ (D.card : ℝ≥0∞) * ((D.card : ℝ≥0∞) * b) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ x ∈ D, P (⋃ y ∈ D, E3 x y) ≤ ∑ _x ∈ D, ((D.card : ℝ≥0∞) * b) := by
          refine Finset.sum_le_sum fun x hx => (measure_biUnion_finset_le _ _).trans ?_
          calc ∑ y ∈ D, P (E3 x y) ≤ ∑ _y ∈ D, b := by
                refine Finset.sum_le_sum fun y hy => ?_
                obtain ⟨-, a1, a2⟩ := (hmemD x).1 hx
                obtain ⟨-, a3, a4⟩ := (hmemD y).1 hy
                exact hE3 x y a1 a2 a3 a4
            _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hP1 : P {ω | HeavyBlockBad d β t₀ n (copyEnv (N ω) 0) ι} ≤
      (D.card : ℝ≥0∞) * (a + (a + g)) + (D.card : ℝ≥0∞) * ((D.card : ℝ≥0∞) * b) :=
    (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hU1 hU2))
  refine hP1.trans ?_
  -- real arithmetic
  set e : ℝ := Real.exp (-((k : ℝ) ^ 4 / 3200)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  set m : ℝ := (D.card : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  set M : ℝ := (9 * 2 ^ k : ℝ) ^ d * (4 ^ (n + 1) + 1) with hM
  have hmM : m ≤ M := by
    have hcard : D.card ≤ (9 * 2 ^ k) ^ d * (4 ^ (n + 1) + 1) := by
      rw [hD, Finset.card_product]
      exact Nat.mul_le_mul hUfc hQc
    have : (D.card : ℝ) ≤ (((9 * 2 ^ k) ^ d * (4 ^ (n + 1) + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    simpa [hM] using this
  have hmsq : m ≤ m ^ 2 := by
    rcases Nat.eq_zero_or_pos D.card with h0 | h0
    · simp [hm, h0]
    · have : (1 : ℝ) ≤ m := Nat.one_le_cast.2 h0
      nlinarith
  have hg' : g = ENNReal.ofReal (4 * d * e) := by
    rw [hg, ENNReal.ofReal_mul (by positivity)]
    simp
  have h4e : 0 ≤ 4 * (d : ℝ) * e := by positivity
  have hreal : (D.card : ℝ≥0∞) * (a + (a + g)) + (D.card : ℝ≥0∞) * ((D.card : ℝ≥0∞) * b) =
      ENNReal.ofReal (m * (p1 + (p1 + 4 * d * e)) + m * (m * p2)) := by
    have e1 : (D.card : ℝ≥0∞) = ENNReal.ofReal m := (ENNReal.ofReal_natCast _).symm
    have e2 : a + (a + g) = ENNReal.ofReal (p1 + (p1 + 4 * d * e)) := by
      rw [hg', ha, ← ENNReal.ofReal_add hp1ge h4e, ← ENNReal.ofReal_add hp1ge (by positivity)]
    rw [e1, e2, hb, ← ENNReal.ofReal_mul hm0, ← ENNReal.ofReal_mul hm0,
      ← ENNReal.ofReal_mul hm0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [hreal]
  apply ENNReal.ofReal_le_ofReal
  have hS0 : 0 ≤ 2 * p1 + p2 + 4 * (d : ℝ) * e := by positivity
  have e3 : (9 * 2 ^ k : ℝ) ^ (2 * d) * (4 ^ (n + 1) + 1) ^ 2 = M ^ 2 := by
    have : (9 * 2 ^ k : ℝ) ^ (2 * d) = ((9 * 2 ^ k : ℝ) ^ d) ^ 2 := by
      rw [← pow_mul, mul_comm d 2]
    rw [this, hM]; ring
  rw [e3]
  calc m * (p1 + (p1 + 4 * d * e)) + m * (m * p2) ≤ m ^ 2 * (2 * p1 + 4 * d * e) + m ^ 2 * p2 := by
        have h1 : m * (p1 + (p1 + 4 * d * e)) = m * (2 * p1 + 4 * d * e) := by ring
        rw [h1]
        have h2 : 0 ≤ 2 * p1 + 4 * (d : ℝ) * e := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hmsq h2]
    _ = m ^ 2 * (2 * p1 + p2 + 4 * d * e) := by ring
    _ ≤ M ^ 2 * (2 * p1 + p2 + 4 * d * e) := by
        gcongr

end ElboimSly.Paper.Heavy
