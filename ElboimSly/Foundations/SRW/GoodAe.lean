/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.GoodProb
public import Mathlib

/-!
# The good event has probability one

Good event and path properties, `P(G) = 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

theorem extPoissonMeasure_Ioi_one_le (r : ℝ≥0) :
    extPoissonMeasure r (Ioi 1) ≤ ENNReal.ofReal ((r : ℝ) ^ 2 / 2) := by
  have h : (Nat.cast : ℕ → ℝ≥0∞) ⁻¹' Ioi 1 = (Nat.cast : ℕ → ℝ≥0∞) ⁻¹' Ici 2 := by
    ext n
    simp only [mem_preimage, mem_Ioi, mem_Ici]
    constructor
    · intro hn
      have : 1 < n := by exact_mod_cast hn
      exact_mod_cast this
    · intro hn
      have : 2 ≤ n := by exact_mod_cast hn
      exact_mod_cast this
  have e1 : extPoissonMeasure r (Ioi 1) = extPoissonMeasure r (Ici 2) := by
    rw [extPoissonMeasure_coe, Measure.map_apply measurable_natCast_ennreal measurableSet_Ioi,
      Measure.map_apply measurable_natCast_ennreal measurableSet_Ici, h]
  rw [e1]
  exact extPoissonMeasure_Ici_two_le r

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {N : Ω → Measure (Dir d × ℝ)} {P : Measure Ω}

/-- Probability that a window of length `h` carries at least two points. -/
theorem prob_window_two_le (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    P {ω | 1 < tot (N ω) (Ioc a b)} ≤
      ENNReal.ofReal (((Fintype.card (Dir d) : ℝ) * (b - a)) ^ 2 / 2) := by
  have hm : MeasurableSet (univ ×ˢ Ioc a b : Set (Dir d × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ioc
  have h1 : {ω | 1 < tot (N ω) (Ioc a b)} = (fun ω => N ω (univ ×ˢ Ioc a b)) ⁻¹' Ioi 1 := rfl
  rw [h1, ← Measure.map_apply (hN.measurable_count hm) measurableSet_Ioi, hN.map_count hm,
    clock_univ_Ioc ha]
  have hx : (Fintype.card (Dir d) : ℝ≥0∞) * ENNReal.ofReal (b - a) =
      ((((Fintype.card (Dir d) : ℝ) * (b - a)).toNNReal : ℝ≥0) : ℝ≥0∞) := by
    show _ = ENNReal.ofReal _
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [hx]
  refine (extPoissonMeasure_Ioi_one_le _).trans ?_
  rw [Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 hab))]

theorem prob_bad_grid (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) {T : ℝ}
    (hT : 0 < T) :
    P {ω | ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
      1 < tot (N ω) (Ioc (((k : ℝ) - 1) * T / n) (k * T / n))} = 0 := by
  set c : ℝ := ((Fintype.card (Dir d) : ℝ) * T) ^ 2 / 2 with hc
  have hbound : ∀ m : ℕ, P {ω | ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
      1 < tot (N ω) (Ioc (((k : ℝ) - 1) * T / n) (k * T / n))} ≤
        ENNReal.ofReal (c * (1 / ((m : ℝ) + 1))) := by
    intro m
    set n : ℕ := m + 1 with hn
    have hnpos : (0 : ℝ) < n := by positivity
    have hsub : {ω | ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
        1 < tot (N ω) (Ioc (((k : ℝ) - 1) * T / n) (k * T / n))} ⊆
        ⋃ k ∈ Finset.Icc 1 n, {ω | 1 < tot (N ω) (Ioc (((k : ℝ) - 1) * T / n) (k * T / n))} := by
      intro ω hω
      obtain ⟨k, hk1, hkn, hk⟩ := hω n (by omega)
      simp only [mem_iUnion]
      exact ⟨k, Finset.mem_Icc.2 ⟨hk1, hkn⟩, hk⟩
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
    have hterm : ∀ k ∈ Finset.Icc 1 n,
        P {ω | 1 < tot (N ω) (Ioc (((k : ℝ) - 1) * T / n) (k * T / n))} ≤
          ENNReal.ofReal (((Fintype.card (Dir d) : ℝ) * (T / n)) ^ 2 / 2) := by
      intro k hk
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
      have h0 : 0 ≤ ((k : ℝ) - 1) * T / n := by
        have : 0 ≤ (k : ℝ) - 1 := by linarith
        positivity
      have hle : ((k : ℝ) - 1) * T / n ≤ k * T / n := by
        apply div_le_div_of_nonneg_right _ hnpos.le; nlinarith
      have hlen : (k : ℝ) * T / n - ((k : ℝ) - 1) * T / n = T / n := by field_simp; ring
      have := prob_window_two_le hN h0 hle
      rwa [hlen] at this
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have : (n + 1 - 1 : ℕ) = n := by omega
    rw [this, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine le_of_eq (congrArg _ ?_)
    have : (n : ℝ) = (m : ℝ) + 1 := by rw [hn]; push_cast; ring
    rw [hc, this]
    field_simp
  have hlim : Filter.Tendsto (fun m : ℕ => ENNReal.ofReal (c * (1 / ((m : ℝ) + 1))))
      Filter.atTop (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
  exact le_antisymm (ge_of_tendsto' hlim hbound) bot_le

/-- Good event and path properties: `P(G) = 1`. -/
theorem ae_good (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) :
    ∀ᵐ ω ∂P, N ω ∈ goodSet d := by
  have h1 : ∀ᵐ ω ∂P, ∀ v : Dir d, ∀ q : ℚ, 0 < q → IsNat (cnt (N ω) v q) := by
    refine ae_all_iff.2 fun v => ae_all_iff.2 fun q => ?_
    by_cases hq : 0 < q
    · have hqr : (0 : ℝ) ≤ 0 := le_rfl
      have := hN.ae_natCast_count (measurableSet_rect v (Ioc 0 (q : ℝ)) measurableSet_Ioc) (by
          rw [clock_single_Ioc v hqr]; exact ENNReal.ofReal_lt_top)
      filter_upwards [this] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hq
  have h2 : ∀ᵐ ω ∂P, ∀ T : ℕ, 1 ≤ T → tot (N ω) (Ioc 0 (T : ℝ)) < ∞ ∧
      ∃ n : ℕ, 1 ≤ n ∧ ∀ k : ℕ, 1 ≤ k ∧ k ≤ n →
        tot (N ω) (Ioc (((k : ℝ) - 1) * T / n) (k * T / n)) ≤ 1 := by
    refine ae_all_iff.2 fun T => ?_
    by_cases hT : 1 ≤ T
    · have hTr : (0 : ℝ) < T := by exact_mod_cast hT
      have hfin := hN.ae_natCast_count (MeasurableSet.univ.prod (measurableSet_Ioc (a := 0) (b := (T : ℝ))))
        (by rw [clock_univ_Ioc le_rfl]; exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ENNReal.ofReal_lt_top)
      have hbad := prob_bad_grid hN hTr
      have hbad' : ∀ᵐ ω ∂P, ¬ ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
          1 < tot (N ω) (Ioc (((k : ℝ) - 1) * T / n) (k * T / n)) := by
        rw [ae_iff]; simpa using hbad
      filter_upwards [hfin, hbad'] with ω hω hb _
      refine ⟨?_, ?_⟩
      · obtain ⟨n, hn⟩ := hω
        show (N ω) (univ ×ˢ Ioc 0 (T : ℝ)) < ∞
        rw [hn]; exact ENNReal.natCast_lt_top n
      · push Not at hb
        obtain ⟨n, hn, hall⟩ := hb
        exact ⟨n, hn, fun k hk => le_of_not_gt (fun h => (hall k hk.1 hk.2).not_gt h) |> fun x => x⟩
    · exact Filter.Eventually.of_forall fun ω h => absurd h hT
  filter_upwards [h1, h2] with ω hω1 hω2
  refine ⟨?_, ?_⟩
  · simp only [mem_iInter, mem_ofPred_eq]
    exact fun v q hq => hω1 v q hq
  · simp only [mem_iInter]
    intro T hT
    refine ⟨(hω2 T hT).1, ?_⟩
    obtain ⟨n, hn, hk⟩ := (hω2 T hT).2
    simp only [mem_iUnion, mem_iInter, mem_ofPred_eq]
    exact ⟨n, hn, hk⟩

end SRW
end ElboimSly
