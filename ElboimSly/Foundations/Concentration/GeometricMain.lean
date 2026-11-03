/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Concentration.GeometricBounds
public import Mathlib

/-!
# Geometric domination of regenerations (c) and (d)

Geometric domination of regenerations. Under the premise `P_T` (`GeoPremise`) with `β ≥ 15`, `T = 4^n`,
`n ≥ 4`: `P(𝔑_t ≥ n³) ≤ e^{-n³}` for `t ∈ [0, 4^{n+1}]` (`geo_count_ge_cube`). If `P_T` holds
for every `T > 0` then `P(t_reg < ∞) ≤ 2β^{-2.4}` and `P(𝔑_∞ ≥ k) = P(t_reg < ∞)^k` (`geo_inf`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

theorem geo_exp_neg_two_ge : 2 / 15 ≤ Real.exp (-2) := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 ≤ 7.5 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]
    nlinarith [Real.exp_pos 1]
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 2)]
  have : (15 / 2 : ℝ) = 7.5 := by norm_num
  rw [inv_div, this]
  exact h2

theorem geo_real_bound (n : ℕ) (hn : 4 ≤ n) (a : ℕ) (ha : a ≤ 4) :
    (((n : ℝ) ^ 3) ^ a) * (Real.exp (-2)) ^ (n ^ 3 - a) ≤ Real.exp (-((n : ℝ) ^ 3)) := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hK : (64 : ℝ) ≤ (n : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hn' 3
    norm_num at this
    exact this
  have h16 : 16 * (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    have : 0 ≤ (n : ℝ) * (((n : ℝ) - 4) * ((n : ℝ) + 4)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    nlinarith
  have han : a ≤ n ^ 3 := by
    have : 4 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
    omega
  have hn1 : (n : ℝ) ≤ Real.exp ((n : ℝ) - 1) := by
    have := Real.add_one_le_exp ((n : ℝ) - 1)
    linarith
  have h1 : ((n : ℝ) ^ 3) ^ a ≤ Real.exp (12 * ((n : ℝ) - 1)) := by
    calc ((n : ℝ) ^ 3) ^ a ≤ ((n : ℝ) ^ 3) ^ 4 :=
          pow_le_pow_right₀ (by nlinarith) ha
      _ = (n : ℝ) ^ 12 := by ring
      _ ≤ (Real.exp ((n : ℝ) - 1)) ^ 12 := pow_le_pow_left₀ (by positivity) hn1 12
      _ = Real.exp (12 * ((n : ℝ) - 1)) := by
          rw [← Real.exp_nat_mul]; norm_num
  have h2 : (Real.exp (-2)) ^ (n ^ 3 - a) ≤ Real.exp (-2 * ((n : ℝ) ^ 3) + 8) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    rw [Nat.cast_sub han]
    push_cast
    have : (a : ℝ) ≤ 4 := by exact_mod_cast ha
    nlinarith
  calc (((n : ℝ) ^ 3) ^ a) * (Real.exp (-2)) ^ (n ^ 3 - a)
      ≤ Real.exp (12 * ((n : ℝ) - 1)) * Real.exp (-2 * ((n : ℝ) ^ 3) + 8) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = Real.exp (12 * ((n : ℝ) - 1) + (-2 * ((n : ℝ) ^ 3) + 8)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-((n : ℝ) ^ 3)) := by
        apply Real.exp_le_exp.2
        nlinarith

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {N : Ω → Measure (ℕ × RingSpace d β)}

/-- **geometric domination of regenerations (c)**: `P(𝔑_t ≥ n³) ≤ e^{-n³}` for `t ∈ [0, 4^{n+1}]`, under `P_{4^n}`,
`β ≥ 15` and `n ≥ 4`. -/
theorem geo_count_ge_cube (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod
      (ringIntensity d β)) P) (hd : 5 ≤ d) (hβ : 15 ≤ β) {n : ℕ} (hn : 4 ≤ n)
    (hP : GeoPremise P N ((4 : ℝ) ^ n)) {t : ℝ} (ht : 0 ≤ t) (ht4 : t ≤ (4 : ℝ) ^ (n + 1)) :
    P {ω | n ^ 3 ≤ ElboimSly.regenCount (geoSlices N ω) t} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 3))) := by
  have hT : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have ha4 : ⌊t / (4 : ℝ) ^ n⌋₊ ≤ 4 := by
    apply Nat.floor_le_of_le
    rw [div_le_iff₀ hT]
    calc t ≤ (4 : ℝ) ^ (n + 1) := ht4
      _ = ((4 : ℕ) : ℝ) * (4 : ℝ) ^ n := by push_cast; ring
  have hak : ⌊t / (4 : ℝ) ^ n⌋₊ ≤ n ^ 3 := by
    have : 4 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
    omega
  set a := ⌊t / (4 : ℝ) ^ n⌋₊ with ha
  have hb := geo_count_le hN hT ht hak
  have hq := geo_q_le hN hd (by linarith) hT hP
  have hq2 : P {ω | ElboimSly.cycTreg (cycSlice 0 (N ω)) ≤ ENNReal.ofReal ((4 : ℝ) ^ n)} ≤
      ENNReal.ofReal (Real.exp (-2)) := by
    refine hq.trans (ENNReal.ofReal_le_ofReal ?_)
    refine (geo_two_rpow_le (by linarith)).trans ?_
    refine le_trans ?_ geo_exp_neg_two_ge
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  refine hb.trans ?_
  have hc : ((n ^ 3).choose a : ℝ≥0∞) ≤ ENNReal.ofReal (((n : ℝ) ^ 3) ^ a) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast Nat.choose_le_pow (n ^ 3) a
  calc ((n ^ 3).choose a : ℝ≥0∞) * _ ^ (n ^ 3 - a)
      ≤ ENNReal.ofReal (((n : ℝ) ^ 3) ^ a) * ENNReal.ofReal (Real.exp (-2)) ^ (n ^ 3 - a) :=
        mul_le_mul' hc (pow_le_pow_left' hq2 _)
    _ = ENNReal.ofReal ((((n : ℝ) ^ 3) ^ a) * (Real.exp (-2)) ^ (n ^ 3 - a)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Real.exp_pos _).le]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (geo_real_bound n hn a ha4)

/-- **geometric domination of regenerations (d)**: if `P_T` holds for every `T > 0`, then
`P(t_reg < ∞) ≤ 2β^{-2.4}`, and `P(𝔑_∞ ≥ k) = P(t_reg < ∞)^k`, where `{𝔑_∞ ≥ k}` is
`{∃ t ≥ 0, 𝔑_t ≥ k}`. -/
theorem geo_inf (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod
      (ringIntensity d β)) P) (hd : 5 ≤ d) (hβ : 1 ≤ β) (hP : ∀ T : ℝ, 0 < T → GeoPremise P N T) :
    P {ω | ElboimSly.cycTreg (cycSlice 0 (N ω)) < ⊤} ≤ ENNReal.ofReal (2 * β ^ (-(2.4 : ℝ))) ∧
    ∀ k : ℕ, P {ω | ∃ t : ℝ, 0 ≤ t ∧ k ≤ ElboimSly.regenCount (geoSlices N ω) t} =
      P {ω | ElboimSly.cycTreg (cycSlice 0 (N ω)) < ⊤} ^ k := by
  have hgood := ae_cycGood hN
  constructor
  · have hU : {ω | ElboimSly.cycTreg (cycSlice 0 (N ω)) < ⊤} =
        ⋃ n : ℕ, {ω | ElboimSly.cycTreg (cycSlice 0 (N ω)) ≤ ENNReal.ofReal ((n : ℝ) + 1)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h.ne
        refine ⟨n, hn.le.trans ?_⟩
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      · rintro ⟨n, hn⟩
        exact hn.trans_lt ENNReal.ofReal_lt_top
    have hmono : Monotone fun n : ℕ =>
        {ω | ElboimSly.cycTreg (cycSlice 0 (N ω)) ≤ ENNReal.ofReal ((n : ℝ) + 1)} :=
      fun m n hmn ω hω => hω.trans (ENNReal.ofReal_le_ofReal (by
        have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith))
    rw [hU, hmono.measure_iUnion]
    exact iSup_le fun n => geo_q_le hN hd hβ (by positivity) (hP _ (by positivity))
  · intro k
    have e1 : {ω | ∃ t : ℝ, 0 ≤ t ∧ k ≤ ElboimSly.regenCount (geoSlices N ω) t} =ᵐ[P]
        ⋂ j ∈ Finset.range k, geoTregFin N j := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [hgood] with ω hω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range, geoTregFin,
        Set.mem_preimage]
      constructor
      · rintro ⟨t, ht, hk⟩ j hj
        have h1 := (le_regenCount_iff (geoSlices N ω) ht k).1 hk
        have h2 : ∑ j ∈ Finset.range k, ElboimSly.cycTreg (cycSlice j (N ω)) <
            ⊤ := lt_of_le_of_lt h1 ENNReal.ofReal_lt_top
        exact ⟨hω j, ENNReal.sum_lt_top.1 h2 j (Finset.mem_range.2 hj)⟩
      · intro h
        have hfin : ElboimSly.regenSigma (geoSlices N ω) k < ⊤ :=
          ENNReal.sum_lt_top.2 fun j hj => (h j (Finset.mem_range.1 hj)).2
        refine ⟨(ElboimSly.regenSigma (geoSlices N ω) k).toReal, ENNReal.toReal_nonneg, ?_⟩
        rw [le_regenCount_iff _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne]
    have e2 : geoTregFin N 0 =ᵐ[P] {ω | ElboimSly.cycTreg (cycSlice 0 (N ω)) < ⊤} := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [hgood] with ω hω
      exact ⟨fun h => h.2, fun h => ⟨hω 0, h⟩⟩
    rw [measure_congr e1, measure_inter_geoTregFin hN, measure_congr e2]

end ElboimSly.Cyclic

end
