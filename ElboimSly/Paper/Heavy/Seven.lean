/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.GoodBlocks
public import ElboimSly.Paper.Heavy.Thresholds

/-!
# Lemma 6.7

ES22 Lemma 6.7 (§6).

If `t_n^{5δ} ≤ β`, then `P(∃ B ∈ ℬ*, B bad) ≤ e^{-δ³n³/2}`.  The proof is a union bound over the at
most `5^{d(n+1)} ≤ e^{δ³n³/2}` blocks of `ℬ*` (`ncard_heavyBstar_le`) using the single-block bound
Probability that a block is bad (c) and (T8).

`es6_seven_of_blockprob` takes the single-block bound `hblk` (probability that a block is bad (c)) as a
distinctly named hypothesis; (T8) enters as `hT8` (the second conjunct of `HeavyT.t8`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]

/-- A union bound over a finite family of events of equal probability bound. -/
theorem measure_biUnion_heavyBstar_le {Pe : Measure Ω} {A : (Fin d → ℤ) → Set Ω} {n : ℕ}
    (hn : 1 ≤ n) {p : ℝ≥0∞} (hA : ∀ ι ∈ heavyBstar d n, Pe (A ι) ≤ p) :
    Pe (⋃ ι ∈ heavyBstar d n, A ι) ≤ ((5 ^ (d * (n + 1)) : ℕ) : ℝ≥0∞) * p := by
  have hfin : (heavyBstar d n).Finite := (Finset.finite_toSet _).subset (heavyBstar_subset d n)
  have e : (⋃ ι ∈ heavyBstar d n, A ι) = ⋃ ι ∈ hfin.toFinset, A ι := by
    ext x; simp
  rw [e]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ ι ∈ hfin.toFinset, Pe (A ι) ≤ ∑ _ι ∈ hfin.toFinset, p :=
        Finset.sum_le_sum fun ι hι => hA ι (hfin.mem_toFinset.1 hι)
    _ = (hfin.toFinset.card : ℝ≥0∞) * p := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        gcongr
        rw [← Set.ncard_eq_toFinset_card _ hfin]
        exact_mod_cast ncard_heavyBstar_le d n hn

/-- ES22 Lemma 6.7, conditional on the single-block bound `hblk` of
Probability that a block is bad (c). -/
theorem es6_seven_of_blockprob {Pe : Measure Ω} {t₀ : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hT8 : d * ((n : ℝ) + 1) * Real.log 5 ≤ indDelta d ^ 3 * (n : ℝ) ^ 3 / 2)
    {env : Ω → Measure (RingSpace d β)}
    (hblk : ∀ ι ∈ heavyBstar d n,
      Pe {ω | HeavyBlockBad d β t₀ n (env ω) ι} ≤
        ENNReal.ofReal (Real.exp (-(indDelta d ^ 3 * (n : ℝ) ^ 3)))) :
    Pe {ω | ∃ ι ∈ heavyBstar d n, HeavyBlockBad d β t₀ n (env ω) ι} ≤
      ENNReal.ofReal (Real.exp (-(indDelta d ^ 3 * (n : ℝ) ^ 3 / 2))) := by
  have h := measure_biUnion_heavyBstar_le (Pe := Pe)
    (A := fun ι => {ω | HeavyBlockBad d β t₀ n (env ω) ι}) hn hblk
  have e : {ω | ∃ ι ∈ heavyBstar d n, HeavyBlockBad d β t₀ n (env ω) ι} =
      ⋃ ι ∈ heavyBstar d n, {ω | HeavyBlockBad d β t₀ n (env ω) ι} := by
    ext ω; simp
  rw [e]
  refine h.trans ?_
  set x : ℝ := indDelta d ^ 3 * (n : ℝ) ^ 3 with hx
  have h5 : ((5 ^ (d * (n + 1)) : ℕ) : ℝ) ≤ Real.exp (x / 2) := by
    have : ((5 ^ (d * (n + 1)) : ℕ) : ℝ) = Real.exp (d * ((n : ℝ) + 1) * Real.log 5) := by
      have h := Real.exp_nat_mul (Real.log 5) (d * (n + 1))
      rw [Real.exp_log (by norm_num)] at h
      push_cast at h ⊢
      rw [h]
    rw [this]
    exact Real.exp_le_exp.2 hT8
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc _ ≤ Real.exp (x / 2) * Real.exp (-x) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end ElboimSly.Paper.Heavy
