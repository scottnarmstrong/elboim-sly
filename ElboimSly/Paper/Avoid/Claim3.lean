/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Claim3Window
public import ElboimSly.Paper.Avoid.Claim3Sum
public import Mathlib

/-!
# ES22 §4: Claim 4.3 (re-tuned)

ES22 Claim 4.3 (§4; deviations D11, F25, F03). Under (S1)–(S2),
for `t ∈ [4^{n₀+1}, 4ⁿ]` and `t^{θ_H} ≤ L ≤ t^{1/2}`:
`P(∀ s ∈ [t, 4ⁿ], ‖W(s)‖ ≥ L) ≥ 1 - C L^{d-2} t^{-(d-2)/2}`, with `C` depending only on `d`;
the same for every process with right-continuous paths and the law of `W`, and for the
translates `x₀ + X̃` with `‖· - x₀‖`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

section

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} [MeasurableSpace Ω]
  {Pr : Measure Ω} {N : Ω → Measure (CycS ℕ d β)}

/-- The regenerated walk has right-continuous paths almost surely. -/
theorem ae_isRCPath_avoidPath (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr) :
    ∀ᵐ ω ∂Pr, IsRCPath (avoidPath N ω) := by
  filter_upwards [ae_cycGood hN] with ω hω s
  have := regenWalk_rc hω s
  simpa only [avoidPath, avoidWalk, avoidEnv_eq_cycSlice] using this

/-- Probability of the bad event of ES22 Claim 4.3. -/
theorem es4_claim3_bad (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ),
      Es4Params d β n₀ n t₀ → ∀ {Ω : Type} [MeasurableSpace Ω] (Pr : Measure Ω)
        (N : Ω → Measure (CycS ℕ d β)), IsPoissonPointProcess N (cycIntensity ℕ d β) Pr →
        ∀ {t L : ℝ}, (4 : ℝ) ^ (n₀ + 1) ≤ t → t ≤ (4 : ℝ) ^ n → t ^ indThetaH ≤ L →
        Pr {ω | ∃ s : ℝ, t ≤ s ∧ s ≤ (4 : ℝ) ^ n ∧ ‖avoidWalk N ω s‖ < L} ≤
          ENNReal.ofReal (C * L ^ (d - 2) * t ^ (-((d - 2 : ℕ) : ℝ) / 2)) := by
  obtain ⟨C, hC, H⟩ := claim3_sum d hd
  refine ⟨C, hC, ?_⟩
  intro β _ n₀ n t₀ hp Ω _ Pr N hN t L ht1 ht2 htL
  have ht1' : (1 : ℝ) < t := lt_of_lt_of_le (one_lt_pow₀ (by norm_num) (by omega)) ht1
  have hL1 : 1 ≤ L := by
    refine le_trans ?_ htL
    exact Real.one_le_rpow ht1'.le (by norm_num [indThetaH])
  obtain ⟨hs1, hs2⟩ := avoidLevel_spec ht1'
  set ℓ₀ : ℕ := avoidLevel t + 1 with hℓ₀
  have hn₀ : n₀ ≤ avoidLevel t := avoidLevel_ge (lt_of_lt_of_le (pow_lt_pow_right₀ (by norm_num)
    (Nat.lt_succ_self n₀)) ht1)
  have hℓn : ℓ₀ ≤ n := avoidLevel_lt ht1' ht2
  have h8 : 8 * d ≤ ℓ₀ := by have := hp.eight_le; omega
  have hbad : {ω | ∃ s : ℝ, t ≤ s ∧ s ≤ (4 : ℝ) ^ n ∧ ‖avoidWalk N ω s‖ < L} ⊆
      {ω | ¬ IsRCPath (avoidPath N ω)} ∪ ⋃ ℓ ∈ Finset.Icc ℓ₀ n,
        {ω | ∃ q ∈ qSet ((4 : ℝ) ^ (ℓ - 1)).toNNReal ((4 : ℝ) ^ ℓ).toNNReal,
          ‖avoidWalk N ω (q : ℝ)‖ < L} := by
    intro ω ⟨s, hts, hsn, hsL⟩
    by_cases hrc : IsRCPath (avoidPath N ω)
    swap
    · exact Or.inl hrc
    right
    have hs1' : 1 < s := lt_of_lt_of_le ht1' hts
    obtain ⟨a1, a2⟩ := avoidLevel_spec hs1'
    have hlt := avoidLevel_lt hs1' hsn
    have hge : ℓ₀ ≤ avoidLevel s + 1 := by
      have : (4 : ℝ) ^ (ℓ₀ - 1) < (4 : ℝ) ^ (avoidLevel s + 1) :=
        lt_of_lt_of_le (by simpa [hℓ₀] using hs1) (hts.trans a2)
      have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).1 this
      omega
    simp only [mem_iUnion, Finset.mem_Icc, mem_ofPred_eq]
    refine ⟨avoidLevel s + 1, ⟨hge, by omega⟩, ?_⟩
    have hab : ((4 : ℝ) ^ (avoidLevel s + 1 - 1)).toNNReal ≤ s.toNNReal := by
      apply Real.toNNReal_le_toNNReal
      simpa using a1.le
    have hsb : s.toNNReal ≤ ((4 : ℝ) ^ (avoidLevel s + 1)).toNNReal :=
      Real.toNNReal_le_toNNReal a2
    obtain ⟨q, hq, hqs⟩ := exists_qSet hrc hab hsb
    refine ⟨q, hq, ?_⟩
    have : avoidPath N ω q = avoidPath N ω s.toNNReal := hqs
    simp only [avoidPath, Real.coe_toNNReal _ (by linarith : 0 ≤ s)] at this
    show ‖avoidWalk N ω (q : ℝ)‖ < L
    rw [this]
    exact hsL
  have hnull : Pr {ω | ¬ IsRCPath (avoidPath N ω)} = 0 := ae_iff.1 (ae_isRCPath_avoidPath hN)
  refine (measure_mono hbad).trans ((measure_union_le _ _).trans ?_)
  rw [hnull, zero_add]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ ℓ ∈ Finset.Icc ℓ₀ n, Pr {ω | ∃ q ∈ qSet ((4 : ℝ) ^ (ℓ - 1)).toNNReal
          ((4 : ℝ) ^ ℓ).toNNReal, ‖avoidWalk N ω (q : ℝ)‖ < L}
      ≤ ∑ ℓ ∈ Finset.Icc ℓ₀ n, (ENNReal.ofReal (Real.exp (-(((ℓ - 1 : ℕ) : ℝ) ^ 2))) +
          ENNReal.ofReal (ElboimSly.Brownian.Cfar d *
            ((L + ((4 : ℝ) ^ ℓ) ^ indThetaH) / 2 ^ (ℓ - 1)) ^ (d - 2))) :=
        Finset.sum_le_sum fun ℓ hℓ => es4_window3 hp hN (by linarith)
          (by have := (Finset.mem_Icc.1 hℓ).1; omega) (Finset.mem_Icc.1 hℓ).2
    _ = ENNReal.ofReal (∑ ℓ ∈ Finset.Icc ℓ₀ n, (Real.exp (-(((ℓ - 1 : ℕ) : ℝ) ^ 2)) +
          ElboimSly.Brownian.Cfar d *
            ((L + ((4 : ℝ) ^ ℓ) ^ indThetaH) / 2 ^ (ℓ - 1)) ^ (d - 2))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        · refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [ENNReal.ofReal_add (by positivity)
            (mul_nonneg (ElboimSly.Brownian.Cfar_pos d).le (by
              apply pow_nonneg; positivity))]
        · intro ℓ _
          exact add_nonneg (by positivity) (mul_nonneg (ElboimSly.Brownian.Cfar_pos d).le (by
            apply pow_nonneg; positivity))
    _ ≤ _ := ENNReal.ofReal_le_ofReal (H ℓ₀ n t L h8 (by simpa [hℓ₀] using hs1) (by
          simpa [hℓ₀] using hs2) htL)

end

end ElboimSly.Paper

end
