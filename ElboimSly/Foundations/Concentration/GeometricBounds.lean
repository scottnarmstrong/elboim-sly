/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Concentration.GeometricEvents
public import Mathlib

/-!
# Geometric domination of regenerations (a) and (b)

Geometric domination of regenerations (a), (b). With `P_T` the premise on `P(W(iβ) = 0)`:

* (a) `q_T := P(t_reg ≤ T) ≤ 2β^{-2.4} ≤ 2/β` (`geo_q_le`);
* (b) `P(𝔑_t ≥ k) ≤ C(k, a) q_T^{k-a} ≤ k^a q_T^{k-a}` for `a = ⌊t/T⌋ ≤ k` (`geo_count_le`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]

/-- The premise `(P_T)` of geometric domination of regenerations: `P(W(iβ) = 0) ≤ (iβ)^{-d/2+0.1}` for every integer
`i ≥ 1` with `iβ ≤ T`, where `W` is the regenerated walk built from the copies `N^k`. -/
def GeoPremise (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β)) (T : ℝ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → (i : ℝ) * β ≤ T →
    P {ω | ElboimSly.regenWalk (geoSlices N ω) ((i : ℝ) * β) = 0} ≤
      ENNReal.ofReal (((i : ℝ) * β) ^ (-(d : ℝ) / 2 + 0.1))

theorem geo_term_le {d : ℕ} (hd : 5 ≤ d) {x : ℝ} (hx : 1 ≤ x) :
    x ^ (-(d : ℝ) / 2 + 0.1) ≤ x ^ (-(2.4 : ℝ)) := by
  refine Real.rpow_le_rpow_of_exponent_le hx ?_
  have : (5 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

theorem geo_nat_rpow_le {i : ℕ} (hi : 1 ≤ i) : (i : ℝ) ^ (-(2.4 : ℝ)) ≤ ((i : ℝ) ^ 2)⁻¹ := by
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  rw [Real.rpow_neg (by linarith)]
  refine inv_anti₀ (by positivity) ?_
  have : (i : ℝ) ^ ((2 : ℕ) : ℝ) ≤ (i : ℝ) ^ (2.4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hi' (by norm_num)
  rwa [Real.rpow_natCast] at this

theorem geo_sum_real {d : ℕ} (hd : 5 ≤ d) {β : ℝ} (hβ : 1 ≤ β) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 m, (((i : ℝ) * β) ^ (-(d : ℝ) / 2 + 0.1)) ≤ 2 * β ^ (-(2.4 : ℝ)) := by
  have hβ0 : 0 < β := by linarith
  have h1 : ∀ i ∈ Finset.Icc 1 m, (((i : ℝ) * β) ^ (-(d : ℝ) / 2 + 0.1)) ≤
      β ^ (-(2.4 : ℝ)) * ((i : ℝ) ^ 2)⁻¹ := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi1
    calc (((i : ℝ) * β) ^ (-(d : ℝ) / 2 + 0.1))
        ≤ ((i : ℝ) * β) ^ (-(2.4 : ℝ)) := geo_term_le hd (by nlinarith)
      _ = (i : ℝ) ^ (-(2.4 : ℝ)) * β ^ (-(2.4 : ℝ)) :=
          Real.mul_rpow (by positivity) hβ0.le
      _ ≤ ((i : ℝ) ^ 2)⁻¹ * β ^ (-(2.4 : ℝ)) :=
          mul_le_mul_of_nonneg_right (geo_nat_rpow_le hi1) (by positivity)
      _ = _ := mul_comm _ _
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  have hI : Finset.Icc 1 m = Finset.Ioo 0 (m + 1) := by ext x; simp; omega
  have h2 : ∑ i ∈ Finset.Ioo 0 (m + 1), (((i : ℝ)) ^ 2)⁻¹ ≤ 2 := by
    have := sum_Ioo_inv_sq_le (α := ℝ) 0 (m + 1)
    simpa using this
  rw [hI, mul_comm 2]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

theorem geo_two_rpow_le {β : ℝ} (hβ : 1 ≤ β) : 2 * β ^ (-(2.4 : ℝ)) ≤ 2 / β := by
  have hβ0 : 0 < β := by linarith
  have : β ^ (-(2.4 : ℝ)) ≤ β ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hβ (by norm_num)
  rw [Real.rpow_neg_one] at this
  rw [div_eq_mul_inv]
  linarith

variable {P : Measure Ω} {N : Ω → Measure (ℕ × RingSpace d β)}

/-- **geometric domination of regenerations (a)**: `q_T = P(t_reg ≤ T) ≤ 2β^{-2.4}`. -/
theorem geo_q_le (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod
      (ringIntensity d β)) P) (hd : 5 ≤ d) (hβ : 1 ≤ β) {T : ℝ} (hT : 0 < T)
    (hP : GeoPremise P N T) :
    P {ω | ElboimSly.cycTreg (cycSlice 0 (N ω)) ≤ ENNReal.ofReal T} ≤
      ENNReal.ofReal (2 * β ^ (-(2.4 : ℝ))) := by
  have hβ0 : 0 < β := Fact.out
  set m := ⌊T / β⌋₊ with hm
  have hsub : {ω | ElboimSly.cycTreg (cycSlice 0 (N ω)) ≤ ENNReal.ofReal T} ≤ᵐ[P]
      ⋃ i ∈ Finset.Icc 1 m, {ω | ElboimSly.regenWalk (geoSlices N ω) ((i : ℝ) * β) = 0} := by
    filter_upwards [ae_cycGood hN] with ω hω hmem
    obtain ⟨i, hi, hz⟩ := exists_regenWalk_zero_of_treg_le (ν := geoSlices N ω) hω hT hmem
    exact Set.mem_biUnion hi hz
  refine (measure_mono_ae hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ i ∈ Finset.Icc 1 m,
      P {ω | ElboimSly.regenWalk (geoSlices N ω) ((i : ℝ) * β) = 0} ≤
        ENNReal.ofReal (((i : ℝ) * β) ^ (-(d : ℝ) / 2 + 0.1)) := by
    intro i hi
    obtain ⟨hi1, him⟩ := Finset.mem_Icc.1 hi
    refine hP i hi1 ?_
    have : (i : ℝ) ≤ T / β := (Nat.cast_le.2 him).trans (Nat.floor_le (by positivity))
    rwa [le_div_iff₀ hβ0] at this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (geo_sum_real hd hβ m)

/-- **geometric domination of regenerations (b)**: `P(𝔑_t ≥ k) ≤ C(k,a) q_T^{k-a}`, `a = ⌊t/T⌋ ≤ k`. -/
theorem geo_count_le (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod
      (ringIntensity d β)) P) {T t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) {k : ℕ} (hak : ⌊t / T⌋₊ ≤ k) :
    P {ω | k ≤ ElboimSly.regenCount (geoSlices N ω) t} ≤
      (k.choose ⌊t / T⌋₊ : ℝ≥0∞) *
        P {ω | ElboimSly.cycTreg (cycSlice 0 (N ω)) ≤ ENNReal.ofReal T} ^ (k - ⌊t / T⌋₊) := by
  set a := ⌊t / T⌋₊ with ha
  have hsub : {ω | k ≤ ElboimSly.regenCount (geoSlices N ω) t} ≤ᵐ[P]
      ⋃ J ∈ Finset.powersetCard (k - a) (Finset.range k), ⋂ j ∈ J, geoTregLe N T j := by
    filter_upwards [ae_cycGood hN] with ω hω hmem
    have h1 := (le_regenCount_iff (geoSlices N ω) ht k).1 hmem
    have h2 : ∑ j ∈ Finset.range k, ElboimSly.cycTreg (cycSlice j (N ω)) ≤ ENNReal.ofReal t := h1
    obtain ⟨J, hJ, hJT⟩ := exists_subset_short (fun j => ElboimSly.cycTreg (cycSlice j (N ω)))
      hT ht h2 hak
    refine Set.mem_biUnion hJ (Set.mem_iInter₂.2 fun j hj => ?_)
    exact ⟨hω j, hJT j hj⟩
  refine (measure_mono_ae hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hq : P (geoTregLe N T 0) ≤
      P {ω | ElboimSly.cycTreg (cycSlice 0 (N ω)) ≤ ENNReal.ofReal T} :=
    measure_mono fun ω hω => hω.2
  have hterm : ∀ J ∈ Finset.powersetCard (k - a) (Finset.range k),
      P (⋂ j ∈ J, geoTregLe N T j) ≤
        P {ω | ElboimSly.cycTreg (cycSlice 0 (N ω)) ≤ ENNReal.ofReal T} ^ (k - a) := by
    intro J hJ
    rw [measure_inter_geoTregLe hN, (Finset.mem_powersetCard.1 hJ).2]
    exact pow_le_pow_left' hq _
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_range, nsmul_eq_mul]
  rw [← Nat.choose_symm hak]

end ElboimSly.Cyclic

end
