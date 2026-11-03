/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.OccStopping

import Mathlib

/-!
# Occupation of a cube at integer times

ES22 Lemma 9.3: occupation of a cube at integer times (ES22 Lemma 9.3, deviation F27).

* `later_visit_le`: Step 1 (one trial);
* `occTau_succ_le`: Step 2, `P(κ_{k+1} < ∞) ≤ P(κ_k < ∞)/2`, by random times with countably many values;
* `occupation_le`: Steps 3 and 4, `P(N > X r²) ≤ 2 e^{-c_occ X}`;
* `occupation_ae_lt_top`: `N < ∞` almost surely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
  {B : ℝ≥0 → Ω → (Fin d → ℝ)}

/-- The set of pairs `(z, w)` such that `z + w(T₀ + i) ∈ D` for some integer `i`. -/
def laterVisit (d : ℕ) (D : Set (Fin d → ℝ)) (T₀ : ℕ) : Set ((Fin d → ℝ) × PathSpace d) :=
  {p | ∃ i : ℕ, p.1 + p.2 ((T₀ + i : ℕ) : ℝ≥0) ∈ D}

lemma measurableSet_laterVisit (D : Set (Fin d → ℝ)) (hD : MeasurableSet D) (T₀ : ℕ) :
    MeasurableSet (laterVisit d D T₀) := by
  have : laterVisit d D T₀ = ⋃ i : ℕ, {p : (Fin d → ℝ) × PathSpace d |
      p.1 + p.2 ((T₀ + i : ℕ) : ℝ≥0) ∈ D} := by
    ext p; simp [laterVisit]
  rw [this]
  refine MeasurableSet.iUnion fun i => ?_
  have : Measurable fun p : (Fin d → ℝ) × PathSpace d => p.1 + p.2 ((T₀ + i : ℕ) : ℝ≥0) :=
    measurable_fst.add ((measurable_pi_apply _).comp measurable_snd)
  exact this hD

/-- One trial: from any starting point, the chance of a later visit is at most `1/2`. -/
lemma later_visit_le [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P) (hd : 3 ≤ d)
    {D : Set (Fin d → ℝ)} (hD : MeasurableSet D) {c : Fin d → ℝ} {r : ℝ} (hr : 0 < r)
    (hDQ : ∀ z ∈ D, ‖z - c‖ ≤ r) {T₀ : ℕ} (hT₀ : 0 < T₀)
    (hC : Cfar d * (r / Real.sqrt T₀) ^ (d - 2) ≤ 1 / 2) (z : Fin d → ℝ) :
    ∫⁻ w, (laterVisit d D T₀).indicator 1 (z, w) ∂(wienerMeasure d) ≤ 1 / 2 := by
  have hfib : MeasurableSet (Prod.mk z ⁻¹' laterVisit d D T₀) :=
    measurable_prodMk_left (measurableSet_laterVisit D hD T₀)
  have e : (fun w => (laterVisit d D T₀).indicator (1 : (Fin d → ℝ) × PathSpace d → ℝ≥0∞) (z, w)) =
      (Prod.mk z ⁻¹' laterVisit d D T₀).indicator 1 := by
    funext w; rfl
  rw [e, lintegral_indicator_one hfib, ← hB.map_pathMap_eq_wiener,
    Measure.map_apply hB.measurable_pathMap hfib]
  have hs : 0 < Real.sqrt T₀ := Real.sqrt_pos.2 (by exact_mod_cast hT₀)
  have h1 := far_hit_exists_le hB hd (z - c) hr hs
  refine le_trans (measure_mono ?_) (h1.trans ?_)
  · rintro ω ⟨i, hi⟩
    refine ⟨((T₀ + i : ℕ) : ℝ≥0), ?_, ?_⟩
    · rw [Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast
      linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    · have := hDQ _ hi
      have e2 : z - c + B ((T₀ + i : ℕ) : ℝ≥0) ω = z + B ((T₀ + i : ℕ) : ℝ≥0) ω - c := by abel
      rw [e2]; exact this
  · exact (ENNReal.ofReal_le_ofReal hC).trans
      (le_of_eq (by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp))

lemma measurableSet_occTau_lt_top (hB : ∀ t, Measurable (B t)) {D : Set (Fin d → ℝ)}
    (hD : MeasurableSet D) (T₀ k : ℕ) : MeasurableSet {ω | occTau B D T₀ k ω < ⊤} := by
  have e : {ω | occTau B D T₀ k ω < ⊤} =
      ⋃ j : ℕ, {ω | occTimes T₀ (visits B D ω) k = (j : ℕ∞)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, occTau_lt_top_iff, Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h
      exact ⟨n, hn.symm⟩
    · rintro ⟨n, hn⟩; rw [hn]; simp
  rw [e]
  exact MeasurableSet.iUnion fun j =>
    bmFiltration_le hB (j : ℝ≥0) _ (measurableSet_occTimes hB hD T₀ k j)

/-- ES22 Lemma 9.3: occupation of a cube at integer times, Step 2: `P(κ_{k+1} < ∞) ≤ P(κ_k < ∞)/2`. -/
theorem occTau_succ_le [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P)
    (hd : 3 ≤ d) {D : Set (Fin d → ℝ)} (hD : MeasurableSet D) {c : Fin d → ℝ} {r : ℝ}
    (hr : 0 < r) (hDQ : ∀ z ∈ D, ‖z - c‖ ≤ r) {T₀ : ℕ} (hT₀ : 0 < T₀)
    (hC : Cfar d * (r / Real.sqrt T₀) ^ (d - 2) ≤ 1 / 2) (k : ℕ) :
    P {ω | occTau B D T₀ (k + 1) ω < ⊤} ≤ (1 / 2) * P {ω | occTau B D T₀ k ω < ⊤} := by
  set Φ : (Fin d → ℝ) → PathSpace d → ℝ≥0∞ := fun z w => (laterVisit d D T₀).indicator 1 (z, w)
    with hΦdef
  have hΦ : Measurable (Function.uncurry Φ) := by
    have : Function.uncurry Φ = (laterVisit d D T₀).indicator 1 := by
      funext ⟨z, w⟩; rfl
    rw [this]
    exact measurable_one.indicator (measurableSet_laterVisit D hD T₀)
  have hcount : (Set.range ((↑) : ℕ → ℝ≥0)).Countable := Set.countable_range _
  have hτT : ∀ ω, occTau B D T₀ k ω ≠ ∞ → ∃ a ∈ Set.range ((↑) : ℕ → ℝ≥0),
      occTau B D T₀ k ω = a := by
    intro ω hω
    have h1 : occTimes T₀ (visits B D ω) k ≠ ⊤ := occTau_lt_top_iff.1 (lt_top_iff_ne_top.2 hω)
    obtain ⟨n, hn, -⟩ := occTimes_spec h1
    exact ⟨(n : ℝ≥0), ⟨n, rfl⟩, occTau_eq_natCast.2 hn⟩
  have hτ : ∀ a ∈ Set.range ((↑) : ℕ → ℝ≥0),
      MeasurableSet[bmFiltration B a] {ω | occTau B D T₀ k ω = a} := by
    rintro a ⟨j, rfl⟩
    have : {ω | occTau B D T₀ k ω = ((j : ℝ≥0) : ℝ≥0∞)} =
        {ω | occTimes T₀ (visits B D ω) k = (j : ℕ∞)} := by
      ext ω; exact occTau_eq_natCast
    rw [this]
    exact measurableSet_occTimes hB.measurable hD T₀ k j
  have hE : ∀ a ∈ Set.range ((↑) : ℕ → ℝ≥0),
      MeasurableSet[bmFiltration B a] (Set.univ ∩ {ω | occTau B D T₀ k ω = a}) := by
    intro a ha
    rw [Set.univ_inter]; exact hτ a ha
  have hbound := hB.lintegral_discrete_stopping_le hcount hτT hτ hE hΦ
    (A := Set.univ) (c := 1 / 2) (fun z _ => ?_) (fun _ _ => Set.mem_univ _)
  · rw [Set.univ_inter] at hbound
    calc P {ω | occTau B D T₀ (k + 1) ω < ⊤}
        = ∫⁻ ω, {ω | occTau B D T₀ (k + 1) ω < ⊤}.indicator 1 ω ∂P :=
          (lintegral_indicator_one (measurableSet_occTau_lt_top hB.measurable hD T₀ (k + 1))).symm
      _ ≤ ∫⁻ ω, {ω | occTau B D T₀ k ω < ⊤}.indicator (fun ω => Φ (B (occTau B D T₀ k ω).toNNReal ω)
            (shiftPath B (occTau B D T₀ k ω).toNNReal ω)) ω ∂P := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : ω ∈ {ω | occTau B D T₀ (k + 1) ω < ⊤}
          · rw [Set.indicator_of_mem hω]
            have h1 : occTimes T₀ (visits B D ω) (k + 1) ≠ ⊤ := occTau_lt_top_iff.1 hω
            obtain ⟨n, hn, i, hi, hvis⟩ := occTimes_succ_ne_top_iff.1 h1
            have hmem : ω ∈ {ω | occTau B D T₀ k ω < ⊤} := by
              show occTau B D T₀ k ω < ⊤
              rw [occTau_lt_top_iff, hn]; simp
            rw [Set.indicator_of_mem hmem, occTau_toNNReal hn]
            show (1 : ℝ≥0∞) ≤ (laterVisit d D T₀).indicator 1 _
            rw [Set.indicator_of_mem]
            · rfl
            · refine ⟨i - (n + T₀), ?_⟩
              have e1 : n + (T₀ + (i - (n + T₀))) = i := by omega
              have e2 : (n : ℝ≥0) + ((T₀ + (i - (n + T₀)) : ℕ) : ℝ≥0) = (i : ℝ≥0) := by
                rw [← Nat.cast_add, e1]
              simp only [shiftPath]
              rw [e2]
              simpa [visits] using hvis
          · rw [Set.indicator_of_notMem hω]; exact zero_le
      _ ≤ _ := hbound
  · have h := later_visit_le hB hd hD hr hDQ hT₀ hC z
    simpa [Φ] using h

/-- ES22 Lemma 9.3: occupation of a cube at integer times. The constant `K_occ = max {1, (2 C_far)^{2/(d-2)}}`. -/
noncomputable def Kocc (d : ℕ) : ℝ := max 1 ((2 * Cfar d) ^ (2 / ((d : ℝ) - 2)))

/-- ES22 Lemma 9.3: occupation of a cube at integer times. The constant `c_occ = ln 2 / (K_occ + 1)`. -/
noncomputable def cocc (d : ℕ) : ℝ := Real.log 2 / (Kocc d + 1)

lemma one_le_Kocc (d : ℕ) : 1 ≤ Kocc d := le_max_left _ _

lemma cocc_pos (d : ℕ) : 0 < cocc d := by
  unfold cocc
  have := one_le_Kocc d
  exact div_pos (Real.log_pos (by norm_num)) (by linarith)

/-- Step 1 arithmetic: with `T₀ ≥ K_occ r²`, one trial succeeds with probability `≤ 1/2`. -/
lemma far_trial_arith {d : ℕ} (hd : 3 ≤ d) {r : ℝ} (hr : 0 < r) {T₀ : ℕ}
    (hT : Kocc d * r ^ 2 ≤ T₀) :
    Cfar d * (r / Real.sqrt T₀) ^ (d - 2) ≤ 1 / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hK1 := one_le_Kocc (m + 2)
  set K := Kocc (m + 2) with hK
  have hC := Cfar_pos (m + 2)
  have hc2 : ((m + 2 : ℕ) : ℝ) - 2 = m := by push_cast; ring
  have hKm : 2 * Cfar (m + 2) ≤ K ^ ((m : ℝ) / 2) := by
    have h1 : (2 * Cfar (m + 2)) ^ (2 / ((m : ℝ))) ≤ K := by
      rw [hK, Kocc, hc2]; exact le_max_right _ _
    calc 2 * Cfar (m + 2) = ((2 * Cfar (m + 2)) ^ (2 / (m : ℝ))) ^ ((m : ℝ) / 2) := by
          rw [← Real.rpow_mul (by positivity)]
          have : 2 / (m : ℝ) * ((m : ℝ) / 2) = 1 := by field_simp
          rw [this, Real.rpow_one]
      _ ≤ K ^ ((m : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have hT0 : 0 < (T₀ : ℝ) := lt_of_lt_of_le (by positivity) hT
  have hsq : r * Real.sqrt K ≤ Real.sqrt T₀ := by
    rw [← Real.sqrt_sq hr.le, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 (by linarith)
  have h2 : r / Real.sqrt T₀ ≤ 1 / Real.sqrt K := by
    rw [div_le_div_iff₀ (Real.sqrt_pos.2 hT0) hsK]
    nlinarith
  have h3 : (r / Real.sqrt T₀) ^ m ≤ (1 / Real.sqrt K) ^ m :=
    pow_le_pow_left₀ (by positivity) h2 m
  have h4 : (Real.sqrt K) ^ m = K ^ ((m : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1; ring
  rw [Nat.add_sub_cancel]
  calc Cfar (m + 2) * (r / Real.sqrt T₀) ^ m ≤ Cfar (m + 2) * (1 / Real.sqrt K) ^ m :=
        mul_le_mul_of_nonneg_left h3 hC.le
    _ = Cfar (m + 2) / K ^ ((m : ℝ) / 2) := by rw [one_div, inv_pow, ← h4]; ring
    _ ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        linarith

/-- ES22 Lemma 9.3: occupation of a cube at integer times (ES22 Lemma 9.3, deviation F27). Let `d ≥ 3`, `σ ≥ 1`, `r ≥ 1`,
`D ⊆ Q(x, r)` Borel and `X ≥ 0`. The number `N` of integer times `i` with `y + σ B(i) ∈ D` satisfies
`P(N > X r²) ≤ 2 e^{-c_occ X}`. Here `N` is the `ℝ≥0∞`-valued count. -/
theorem occupation_le [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P) (hd : 3 ≤ d)
    (y x : Fin d → ℝ) {σ r : ℝ} (hσ : 1 ≤ σ) (hr : 1 ≤ r) {D : Set (Fin d → ℝ)}
    (hD : MeasurableSet D) (hDQ : D ⊆ Metric.closedBall x r) {X : ℝ} (hX : 0 ≤ X) :
    P {ω | ENNReal.ofReal (X * r ^ 2) <
        ∑' i : ℕ, {ω | y + σ • B (i : ℝ≥0) ω ∈ D}.indicator (1 : Ω → ℝ≥0∞) ω} ≤
      ENNReal.ofReal (2 * Real.exp (-(cocc d) * X)) := by
  have hr0 : 0 < r := by linarith
  have hσ0 : 0 < σ := by linarith
  -- reduction to `σ = 1`, `y = 0`
  set D' : Set (Fin d → ℝ) := {z | y + σ • z ∈ D} with hD'
  have hD'm : MeasurableSet D' := by
    have : Measurable fun z : Fin d → ℝ => y + σ • z := by fun_prop
    exact this hD
  set c : Fin d → ℝ := σ⁻¹ • (x - y) with hc
  have hDQ' : ∀ z ∈ D', ‖z - c‖ ≤ r := by
    intro z hz
    have h1 : ‖y + σ • z - x‖ ≤ r := by
      have := hDQ hz
      rwa [Metric.mem_closedBall, dist_eq_norm] at this
    have e : y + σ • z - x = σ • (z - c) := by
      rw [hc, smul_sub, smul_smul, mul_inv_cancel₀ hσ0.ne', one_smul]; abel
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hσ0] at h1
    nlinarith [norm_nonneg (z - c)]
  set K := Kocc d with hK
  have hK1 : 1 ≤ K := one_le_Kocc d
  set T₀ : ℕ := ⌈K * r ^ 2⌉₊ with hT₀
  have hKr : K * r ^ 2 ≤ T₀ := Nat.le_ceil _
  have hT₀lt : (T₀ : ℝ) < K * r ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hT₀pos : 0 < T₀ := by
    have : (0 : ℝ) < T₀ := lt_of_lt_of_le (by positivity) hKr
    exact_mod_cast this
  have hC := far_trial_arith hd hr0 hKr
  -- geometric decay
  have hdecay : ∀ k : ℕ, P {ω | occTau B D' T₀ k ω < ⊤} ≤ (1 / 2) ^ k := by
    intro k
    induction k with
    | zero => simpa using prob_le_one
    | succ k ih =>
      refine (occTau_succ_le hB hd hD'm hr0 hDQ' hT₀pos hC k).trans ?_
      rw [pow_succ']
      exact mul_le_mul_right ih _
  set m : ℕ := ⌊X / (K + 1)⌋₊ with hm
  have hmT : ((m * T₀ : ℕ) : ℝ) ≤ X * r ^ 2 := by
    push_cast
    have h1 : (m : ℝ) ≤ X / (K + 1) := Nat.floor_le (by positivity)
    have h2 : (T₀ : ℝ) ≤ (K + 1) * r ^ 2 := by nlinarith [sq_nonneg r]
    calc (m : ℝ) * T₀ ≤ (X / (K + 1)) * ((K + 1) * r ^ 2) :=
          mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
      _ = X * r ^ 2 := by field_simp
  have hsub : {ω | ENNReal.ofReal (X * r ^ 2) <
        ∑' i : ℕ, {ω | y + σ • B (i : ℝ≥0) ω ∈ D}.indicator (1 : Ω → ℝ≥0∞) ω} ⊆
      {ω | occTau B D' T₀ m ω < ⊤} := by
    intro ω hω
    rw [Set.mem_ofPred_eq] at hω ⊢
    rw [occTau_lt_top_iff]
    intro htop
    have hle := tsum_indicator_le (T₀ := T₀) (h := visits B D' ω) htop
    have e : ∑' i : ℕ, {ω | y + σ • B (i : ℝ≥0) ω ∈ D}.indicator (1 : Ω → ℝ≥0∞) ω =
        ∑' i : ℕ, {i | visits B D' ω i}.indicator (1 : ℕ → ℝ≥0∞) i := by
      refine tsum_congr fun i => ?_
      by_cases h : y + σ • B (i : ℝ≥0) ω ∈ D
      · rw [Set.indicator_of_mem (show ω ∈ {ω | y + σ • B (i : ℝ≥0) ω ∈ D} from h),
          Set.indicator_of_mem (show i ∈ {i | visits B D' ω i} from h)]
        rfl
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | y + σ • B (i : ℝ≥0) ω ∈ D} from h),
          Set.indicator_of_notMem (show i ∉ {i | visits B D' ω i} from h)]
    rw [e] at hω
    exact absurd (hω.trans_le hle) (not_lt.2 (by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hmT))
  have hreal : ((1 / 2 : ℝ)) ^ m ≤ 2 * Real.exp (-(cocc d) * X) := by
    have hfl : X / (K + 1) < m + 1 := Nat.lt_floor_add_one _
    have hlog := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    have e1 : ((1 / 2 : ℝ)) ^ m = Real.exp (-(Real.log 2) * m) := by
      have : (1 / 2 : ℝ) = Real.exp (-(Real.log 2)) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      rw [this, ← Real.exp_nat_mul]; congr 1; ring
    have e2 : 2 * Real.exp (-(cocc d) * X) = Real.exp (Real.log 2 + -(cocc d) * X) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
    rw [e1, e2]
    refine Real.exp_le_exp.2 ?_
    have hcX : cocc d * X = Real.log 2 * (X / (K + 1)) := by
      unfold cocc; rw [← hK]; ring
    have hlog2 : 0 < Real.log 2 := hlog
    nlinarith [hcX]
  calc _ ≤ P {ω | occTau B D' T₀ m ω < ⊤} := measure_mono hsub
    _ ≤ (1 / 2) ^ m := hdecay m
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(cocc d) * X)) := by
        have h1 : (1 / 2 : ℝ≥0∞) ^ m = ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := by
          rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
          simp
        rw [h1]
        exact ENNReal.ofReal_le_ofReal hreal

/-- ES22 Lemma 9.3: occupation of a cube at integer times ("in particular `N < ∞` almost surely"). -/
theorem occupation_ae_lt_top [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P)
    (hd : 3 ≤ d) (y x : Fin d → ℝ) {σ r : ℝ} (hσ : 1 ≤ σ) (hr : 1 ≤ r) {D : Set (Fin d → ℝ)}
    (hD : MeasurableSet D) (hDQ : D ⊆ Metric.closedBall x r) :
    ∀ᵐ ω ∂P, ∑' i : ℕ, {ω | y + σ • B (i : ℝ≥0) ω ∈ D}.indicator (1 : Ω → ℝ≥0∞) ω < ⊤ := by
  have hlim : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (2 * Real.exp (-(cocc d) * n)))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => 2 * Real.exp (-(cocc d) * n)) Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun n : ℕ => -(cocc d) * (n : ℝ)) Filter.atTop Filter.atBot :=
        Filter.Tendsto.const_mul_atTop_of_neg (by linarith [cocc_pos d]) tendsto_natCast_atTop_atTop
      simpa using (Real.tendsto_exp_atBot.comp h2).const_mul 2
    simpa using ENNReal.tendsto_ofReal h1
  have hP : P {ω | ∑' i : ℕ, {ω | y + σ • B (i : ℝ≥0) ω ∈ D}.indicator (1 : Ω → ℝ≥0∞) ω = ⊤} ≤ 0 := by
    refine ge_of_tendsto' hlim fun n => ?_
    refine le_trans (measure_mono ?_) (occupation_le hB hd y x hσ hr hD hDQ (X := n)
      (Nat.cast_nonneg n))
    intro ω hω
    rw [Set.mem_ofPred_eq] at hω ⊢
    rw [hω]
    exact ENNReal.ofReal_lt_top
  rw [ae_iff]
  have h0 : P {ω | ¬ ∑' i : ℕ, {ω | y + σ • B (i : ℝ≥0) ω ∈ D}.indicator
      (1 : Ω → ℝ≥0∞) ω < ⊤} = 0 := by
    refine le_antisymm ?_ zero_le
    refine le_trans (measure_mono ?_) hP
    intro ω h
    exact not_lt_top_iff.1 h
  exact h0

end ElboimSly.Brownian
