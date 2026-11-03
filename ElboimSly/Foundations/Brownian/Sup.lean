/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Reflection
public import ElboimSly.Foundations.Brownian.Moments
import Mathlib

/-!
# Gaussian maximal bound

Gaussian maximal bound.

For a standard `d`-dimensional Brownian motion and `h, λ > 0`:
* `P(∃ u ≤ h, λ ≤ ‖B(u)‖) ≤ 4 d e^{-λ²/(2h)}` (a). The written proof states the bound for
  `sup_{u∈[0,h]} ‖B(u)‖ ≥ λ`; on the compact interval the supremum of a continuous function is
  attained, so the event `{sup ≥ λ}` equals `{∃ u ∈ [0,h], λ ≤ ‖B(u)‖}`, which is the form used.
* `P(λ ≤ ‖B(h)‖) ≤ 2 d e^{-λ²/(2h)}` (b);
* the same for `σ B` with `λ` replaced by `λ/σ` (c).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

lemma gridPt_succ (h : ℝ≥0) (M k : ℕ) : gridPt h (2 ^ M) k = gridPt h (2 ^ (M + 1)) (2 * k) := by
  unfold gridPt
  push_cast
  rw [pow_succ]
  have : (2 : ℝ≥0) ^ M ≠ 0 := by positivity
  field_simp

/-- A coordinate of a standard Brownian motion: the one-sided maximal bound. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.sup_coord_le [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (i : Fin d) {h : ℝ≥0}
    (hh : h ≠ 0) {l : ℝ} (hl : 0 < l) :
    P {ω | ∃ u ≤ h, l ≤ B u ω i} ≤ 2 * ENNReal.ofReal (Real.exp (-l ^ 2 / (2 * h))) := by
  have hhpos : (0 : ℝ) < h := by positivity
  let E : ℝ → ℕ → Set Ω := fun l' M =>
    {ω | ∃ k ≤ 2 ^ M, l' ≤ B (gridPt h (2 ^ M) k) ω i}
  have hmono : ∀ l', Monotone (E l') := by
    intro l'
    refine monotone_nat_of_le_succ fun M => ?_
    rintro ω ⟨k, hk, hωk⟩
    refine ⟨2 * k, by rw [pow_succ]; omega, ?_⟩
    rwa [← gridPt_succ]
  have hlaw := (hB.isPreBrownianReal i).hasLaw_eval h
  have hbound : ∀ l', 0 < l' → ∀ M, P (E l' M) ≤ 2 * ENNReal.ofReal (Real.exp (-l' ^ 2 / (2 * h))) := by
    intro l' hl' M
    refine (hB.reflection i (pow_ne_zero M two_ne_zero) l').trans ?_
    gcongr
    exact measure_ge_le_exp_of_hasLaw hlaw hh hl'.le
  have hcover : ∀ l', 0 < l' → l' < l →
      {ω | ∃ u ≤ h, l ≤ B u ω i} ⊆ ⋃ M, E l' M := by
    intro l' hl' hll' ω ⟨u, huh, hlu⟩
    have hcont : Continuous fun t : ℝ≥0 => B t ω i :=
      (continuous_apply i).comp (hB.continuous_zero ω).1
    have hev : ∀ᶠ t in 𝓝 u, l' < B t ω i :=
      hcont.continuousAt.eventually (lt_mem_nhds (lt_of_lt_of_le hll' hlu))
    obtain ⟨ε, hε, hεt⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt ((h : ℝ) / ε) (by norm_num : (1 : ℝ) < 2)
    have h2M : (0 : ℝ) < 2 ^ M := by positivity
    set x : ℝ := (u : ℝ) * 2 ^ M / h with hx
    have hx0 : 0 ≤ x := by positivity
    set k := ⌊x⌋₊ with hk
    have hk1 : (k : ℝ) ≤ x := Nat.floor_le hx0
    have hk2 : x < k + 1 := Nat.lt_floor_add_one x
    have hkM : k ≤ 2 ^ M := by
      refine Nat.floor_le_of_le ?_
      have : (u : ℝ) ≤ h := by exact_mod_cast huh
      rw [hx, div_le_iff₀ hhpos]
      push_cast
      nlinarith
    have hg : ((gridPt h (2 ^ M) k : ℝ≥0) : ℝ) = k * h / 2 ^ M := by
      unfold gridPt; push_cast; rfl
    refine Set.mem_iUnion.2 ⟨M, k, hkM, ?_⟩
    have hdist : dist (gridPt h (2 ^ M) k) u < ε := by
      rw [NNReal.dist_eq, hg, abs_lt]
      have e1 : (k : ℝ) * h / 2 ^ M ≤ u := by
        rw [div_le_iff₀ h2M]
        have := mul_le_mul_of_nonneg_right hk1 hhpos.le
        rw [hx] at this
        field_simp at this
        linarith
      have e2 : (u : ℝ) < (k + 1) * h / 2 ^ M := by
        rw [lt_div_iff₀ h2M]
        have := mul_lt_mul_of_pos_right hk2 hhpos
        rw [hx] at this
        field_simp at this
        linarith
      have e3 : (h : ℝ) / 2 ^ M < ε := by
        rw [div_lt_iff₀ h2M]
        rw [div_lt_iff₀ hε] at hM
        linarith
      constructor
      · have : (k + 1 : ℝ) * h / 2 ^ M = k * h / 2 ^ M + h / 2 ^ M := by ring
        linarith
      · linarith
    exact (hεt hdist).le
  have hS : ∀ l', 0 < l' → l' < l →
      P {ω | ∃ u ≤ h, l ≤ B u ω i} ≤ 2 * ENNReal.ofReal (Real.exp (-l' ^ 2 / (2 * h))) := by
    intro l' hl' hll'
    refine (measure_mono (hcover l' hl' hll')).trans ?_
    exact le_of_tendsto' (tendsto_measure_iUnion_atTop (hmono l')) (hbound l' hl')
  -- let `l' ↑ l`
  have hlim : Tendsto (fun x : ℝ => 2 * ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * h)))) (𝓝[<] l)
      (𝓝 (2 * ENNReal.ofReal (Real.exp (-l ^ 2 / (2 * h))))) := by
    have hc : Continuous fun x : ℝ => Real.exp (-x ^ 2 / (2 * h)) := by fun_prop
    have := ENNReal.Tendsto.const_mul (a := 2)
      (ENNReal.tendsto_ofReal (hc.continuousAt.tendsto (x := l))) (Or.inr (by norm_num))
    exact this.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hl] with x hx using hS x hx.1 hx.2

/-- Gaussian maximal bound (a). -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.sup_norm_le [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) {h : ℝ≥0} (hh : h ≠ 0)
    {l : ℝ} (hl : 0 < l) :
    P {ω | ∃ u ≤ h, l ≤ ‖B u ω‖} ≤
      (4 * d : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-l ^ 2 / (2 * h))) := by
  have hcover : {ω | ∃ u ≤ h, l ≤ ‖B u ω‖} ⊆ ⋃ i : Fin d,
      ({ω | ∃ u ≤ h, l ≤ B u ω i} ∪ {ω | ∃ u ≤ h, l ≤ (fun t ω k => -B t ω k) u ω i}) := by
    rintro ω ⟨u, huh, hu⟩
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have : ‖B u ω‖ = 0 := by rw [norm_eq_zero]; exact Subsingleton.elim _ _
      linarith
    obtain ⟨i, hi⟩ := exists_abs_eq_norm (B u ω) hd
    rw [hi] at hu
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    rcases le_abs'.1 hu with h1 | h1
    · exact Or.inr ⟨u, huh, by show l ≤ -B u ω i; linarith⟩
    · exact Or.inl ⟨u, huh, h1⟩
  have hneg := hB.neg
  calc _ ≤ P (⋃ i : Fin d, ({ω | ∃ u ≤ h, l ≤ B u ω i} ∪
        {ω | ∃ u ≤ h, l ≤ (fun t ω k => -B t ω k) u ω i})) := measure_mono hcover
    _ ≤ ∑ i : Fin d, P ({ω | ∃ u ≤ h, l ≤ B u ω i} ∪
        {ω | ∃ u ≤ h, l ≤ (fun t ω k => -B t ω k) u ω i}) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin d, (2 * ENNReal.ofReal (Real.exp (-l ^ 2 / (2 * h))) +
        2 * ENNReal.ofReal (Real.exp (-l ^ 2 / (2 * h)))) := by
        refine Finset.sum_le_sum fun i _ => (measure_union_le _ _).trans ?_
        exact add_le_add (hB.sup_coord_le i hh hl) (hneg.sup_coord_le i hh hl)
    _ = (4 * d : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-l ^ 2 / (2 * h))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Gaussian maximal bound (b). -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.norm_ge_le [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) {h : ℝ≥0} (hh : h ≠ 0)
    {l : ℝ} (hl : 0 < l) :
    P {ω | l ≤ ‖B h ω‖} ≤ (2 * d : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-l ^ 2 / (2 * h))) := by
  have hcover : {ω | l ≤ ‖B h ω‖} ⊆ ⋃ i : Fin d,
      ({ω | l ≤ B h ω i} ∪ {ω | l ≤ (fun ω => -B h ω i) ω}) := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have : ‖B h ω‖ = 0 := by rw [norm_eq_zero]; exact Subsingleton.elim _ _
      linarith
    obtain ⟨i, hi⟩ := exists_abs_eq_norm (B h ω) hd
    rw [hi] at hω
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    rcases le_abs'.1 hω with h1 | h1
    · exact Or.inr (by show l ≤ -B h ω i; linarith)
    · exact Or.inl h1
  have hlaw : ∀ i, HasLaw (fun ω => B h ω i) (gaussianReal 0 h) P := fun i =>
    (hB.isPreBrownianReal i).hasLaw_eval h
  have hlawn : ∀ i, HasLaw (fun ω => -B h ω i) (gaussianReal 0 h) P := fun i => by
    simpa [Pi.neg_def] using gaussianReal_neg (hlaw i)
  calc _ ≤ P (⋃ i : Fin d, ({ω | l ≤ B h ω i} ∪ {ω | l ≤ (fun ω => -B h ω i) ω})) :=
        measure_mono hcover
    _ ≤ ∑ i : Fin d, P ({ω | l ≤ B h ω i} ∪ {ω | l ≤ (fun ω => -B h ω i) ω}) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin d, (ENNReal.ofReal (Real.exp (-l ^ 2 / (2 * h))) +
        ENNReal.ofReal (Real.exp (-l ^ 2 / (2 * h)))) := by
        refine Finset.sum_le_sum fun i _ => (measure_union_le _ _).trans ?_
        exact add_le_add (measure_ge_le_exp_of_hasLaw (hlaw i) hh hl.le)
          (measure_ge_le_exp_of_hasLaw (hlawn i) hh hl.le)
    _ = (2 * d : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-l ^ 2 / (2 * h))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Gaussian maximal bound (c), for the maximal bound: `σ B` with `λ` replaced by `λ/σ`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.sup_norm_smul_le [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) {h : ℝ≥0} (hh : h ≠ 0)
    {l σ : ℝ} (hl : 0 < l) (hσ : 0 < σ) :
    P {ω | ∃ u ≤ h, l ≤ ‖σ • B u ω‖} ≤
      (4 * d : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(l / σ) ^ 2 / (2 * h))) := by
  refine le_trans (measure_mono ?_) (hB.sup_norm_le hh (div_pos hl hσ))
  rintro ω ⟨u, huh, hu⟩
  refine ⟨u, huh, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ] at hu
  rw [div_le_iff₀ hσ]
  linarith

end ElboimSly.Brownian
