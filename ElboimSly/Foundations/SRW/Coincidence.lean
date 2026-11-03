/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.GoodAe
public import ElboimSly.Foundations.PPP.Restriction
public import ElboimSly.Foundations.PPP.Finite
public import Mathlib

/-!
# No jumps at fixed times, no coincidences

No jumps at fixed times, no coincidences.

* `ae_not_isJump`: (a) for fixed `t > 0`, a.s. `t` is not a jump time of the walk, i.e.
  `X(t-) = X(t)`.
* `ae_no_jump_pair`: (b) for countable `Δ`, a.s. there are no jump times `s < s'` with
  `s' - s ∈ Δ`.
* `ae_no_jump_pair_mul`: the special case `Δ = β ℤ_{≥1}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

section Counts

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] {N : Ω → Measure S}
  {μ : Measure S} {P : Measure Ω}

/-- Counts of two disjoint measurable sets are independent. -/
theorem indepFun_count (h : IsPoissonPointProcess N μ P) {A B : Set S} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hd : Disjoint A B) :
    IndepFun (fun ω => N ω A) (fun ω => N ω B) P := by
  have h1 := h.indepFun_restrict hA hB hd
  have e1 : Measurable fun m : Measure S => m A := Measure.measurable_coe hA
  have e2 : Measurable fun m : Measure S => m B := Measure.measurable_coe hB
  have := h1.comp e1 e2
  simpa [Function.comp_def, Measure.restrict_apply_self] using this

/-- Markov's inequality for counts: `P(N(A) ≥ 1) ≤ μ(A)`. -/
theorem prob_one_le_count_le (h : IsPoissonPointProcess N μ P) {A : Set S}
    (hA : MeasurableSet A) : P {ω | 1 ≤ N ω A} ≤ μ A := by
  have := mul_meas_ge_le_lintegral₀ (μ := P) (f := fun ω => N ω A)
    (h.measurable_count hA).aemeasurable 1
  simpa [h.lintegral_count hA] using this

end Counts

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {N : Ω → Measure (Dir d × ℝ)} {P : Measure Ω}

theorem clock_univ_singleton (t : ℝ) :
    clockIntensity (Dir d) (univ ×ˢ ({t} : Set ℝ)) = 0 := by
  unfold clockIntensity
  rw [Measure.prod_prod, Measure.restrict_apply (measurableSet_singleton t)]
  have : volume ({t} ∩ Ioi (0 : ℝ)) = 0 := measure_mono_null inter_subset_left (by simp)
  rw [this, mul_zero]

/-- A fixed time carries no point of the process, almost surely. -/
theorem ae_tot_singleton_eq_zero (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    (t : ℝ) : ∀ᵐ ω ∂P, tot (N ω) {t} = 0 := by
  have hm : MeasurableSet (univ ×ˢ ({t} : Set ℝ) : Set (Dir d × ℝ)) :=
    MeasurableSet.univ.prod (measurableSet_singleton t)
  have h1 := hN.lintegral_count hm
  rw [clock_univ_singleton] at h1
  exact (lintegral_eq_zero_iff (hN.measurable_count hm)).1 h1

/-- No jumps at fixed times, no coincidences (a): for fixed `t > 0`, almost surely `t` is not a jump time
of the walk, that is, the left limit of the walk at `t` equals its value. -/
theorem ae_not_isJump (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) {t : ℝ}
    (_ht : 0 < t) : ∀ᵐ ω ∂P, ¬ IsJump (N ω) t := by
  filter_upwards [ae_tot_singleton_eq_zero hN t] with ω hω hj
  have := hj.one_le_tot
  rw [hω] at this
  exact absurd this (by norm_num)

/-- No jumps at fixed times, no coincidences (a), in the form `X(t-) = X(t)`. -/
theorem ae_walk_leftConst (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) {t : ℝ}
    (ht : 0 < t) :
    ∀ᵐ ω ∂P, ∃ δ > 0, ∀ u ∈ Ico (t - δ) t, walk d (N ω) u = walk d (N ω) t := by
  filter_upwards [ae_not_isJump hN ht] with ω hω
  unfold IsJump at hω
  push Not at hω
  exact hω ht

section Pairs

variable (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)

include hN

theorem prob_pair_term {δ h : ℝ} (hh : 0 < h) (hhδ : h < δ) (k : ℕ) (hk : 1 ≤ k) :
    P ({ω | 1 ≤ tot (N ω) (Ioc (((k : ℝ) - 1) * h) (k * h))} ∩
      {ω | 1 ≤ tot (N ω) (Ioc (((k : ℝ) - 1) * h + δ) (k * h + δ))}) ≤
      ENNReal.ofReal (((Fintype.card (Dir d) : ℝ) * h) ^ 2) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hA : MeasurableSet (univ ×ˢ Ioc (((k : ℝ) - 1) * h) (k * h) : Set (Dir d × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ioc
  have hB : MeasurableSet (univ ×ˢ Ioc (((k : ℝ) - 1) * h + δ) (k * h + δ) :
      Set (Dir d × ℝ)) := MeasurableSet.univ.prod measurableSet_Ioc
  have hd : Disjoint (univ ×ˢ Ioc (((k : ℝ) - 1) * h) (k * h) : Set (Dir d × ℝ))
      (univ ×ˢ Ioc (((k : ℝ) - 1) * h + δ) (k * h + δ)) := by
    refine Set.disjoint_left.2 fun p hp hq => ?_
    simp only [mem_prod, mem_univ, true_and, mem_Ioc] at hp hq
    nlinarith [hp.2, hq.1]
  have hind := indepFun_count hN hA hB hd
  have e : ({ω | 1 ≤ tot (N ω) (Ioc (((k : ℝ) - 1) * h) (k * h))} ∩
      {ω | 1 ≤ tot (N ω) (Ioc (((k : ℝ) - 1) * h + δ) (k * h + δ))}) =
      (fun ω => N ω (univ ×ˢ Ioc (((k : ℝ) - 1) * h) (k * h))) ⁻¹' Ici 1 ∩
      (fun ω => N ω (univ ×ˢ Ioc (((k : ℝ) - 1) * h + δ) (k * h + δ))) ⁻¹' Ici 1 := rfl
  rw [e, hind.measure_inter_preimage_eq_mul _ _ measurableSet_Ici measurableSet_Ici]
  have p1 := prob_one_le_count_le hN hA
  have p2 := prob_one_le_count_le hN hB
  have a0 : (0 : ℝ) ≤ ((k : ℝ) - 1) * h := mul_nonneg (by linarith) hh.le
  have a1 : (0 : ℝ) ≤ ((k : ℝ) - 1) * h + δ := by linarith
  rw [clock_univ_Ioc a0] at p1
  rw [clock_univ_Ioc a1] at p2
  have l1 : (k : ℝ) * h - ((k : ℝ) - 1) * h = h := by ring
  have l2 : (k : ℝ) * h + δ - (((k : ℝ) - 1) * h + δ) = h := by ring
  rw [l1] at p1
  rw [l2] at p2
  have hc : (Fintype.card (Dir d) : ℝ≥0∞) * ENNReal.ofReal h =
      ENNReal.ofReal ((Fintype.card (Dir d) : ℝ) * h) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [hc] at p1 p2
  have : (fun ω => N ω (univ ×ˢ Ioc (((k : ℝ) - 1) * h) (k * h))) ⁻¹' Ici 1 =
      {ω | 1 ≤ N ω (univ ×ˢ Ioc (((k : ℝ) - 1) * h) (k * h))} := rfl
  rw [this]
  have : (fun ω => N ω (univ ×ˢ Ioc (((k : ℝ) - 1) * h + δ) (k * h + δ))) ⁻¹' Ici 1 =
      {ω | 1 ≤ N ω (univ ×ˢ Ioc (((k : ℝ) - 1) * h + δ) (k * h + δ))} := rfl
  rw [this]
  calc _ ≤ ENNReal.ofReal ((Fintype.card (Dir d) : ℝ) * h) *
        ENNReal.ofReal ((Fintype.card (Dir d) : ℝ) * h) := mul_le_mul' p1 p2
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), sq]

/-- The probability that two jumps at distance exactly `δ` occur in `(0,T]`, for a small grid
size `h`. -/
theorem prob_pair_le {δ h T : ℝ} (hh : 0 < h) (hhδ : h < δ) (hT : 0 ≤ T) :
    P {ω | ∃ s s', s ∈ Ioc 0 T ∧ s' ∈ Ioc 0 T ∧ IsJump (N ω) s ∧ IsJump (N ω) s' ∧
        s' - s = δ} ≤
      ENNReal.ofReal ((T / h + 1) * ((Fintype.card (Dir d) : ℝ) * h) ^ 2) := by
  set K : ℕ := ⌈T / h⌉₊ with hK
  have hsub : {ω | ∃ s s', s ∈ Ioc 0 T ∧ s' ∈ Ioc 0 T ∧ IsJump (N ω) s ∧ IsJump (N ω) s' ∧
        s' - s = δ} ⊆ ⋃ k ∈ Finset.Icc 1 K,
      ({ω | 1 ≤ tot (N ω) (Ioc (((k : ℝ) - 1) * h) (k * h))} ∩
      {ω | 1 ≤ tot (N ω) (Ioc (((k : ℝ) - 1) * h + δ) (k * h + δ))}) := by
    rintro ω ⟨s, s', hs, hs', hj, hj', hss⟩
    set k : ℕ := ⌈s / h⌉₊ with hk
    have hsh : 0 < s / h := div_pos hs.1 hh
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by simpa [hk] using hsh)
    have hkK : k ≤ K := Nat.ceil_mono (div_le_div_of_nonneg_right hs.2 hh.le)
    have h1 : s / h ≤ k := Nat.le_ceil _
    have h2 : (k : ℝ) < s / h + 1 := Nat.ceil_lt_add_one hsh.le
    have h3 : s ≤ k * h := by rwa [div_le_iff₀ hh, ] at h1
    have h4 : ((k : ℝ) - 1) * h < s := by
      have : (k : ℝ) - 1 < s / h := by linarith
      rwa [lt_div_iff₀ hh] at this
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, Finset.mem_Icc]
    refine ⟨k, ⟨hk1, hkK⟩, ?_, ?_⟩
    · refine hj.one_le_tot.trans (measure_mono (prod_mono subset_rfl ?_))
      intro x hx
      rw [mem_singleton_iff] at hx
      rw [hx]; exact ⟨h4, h3⟩
    · refine hj'.one_le_tot.trans (measure_mono (prod_mono subset_rfl ?_))
      intro x hx
      rw [mem_singleton_iff] at hx
      rw [hx]
      constructor <;> linarith
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm := fun k (hk : k ∈ Finset.Icc 1 K) =>
    prob_pair_term hN (δ := δ) hh hhδ k (Finset.mem_Icc.1 hk).1
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have : (K + 1 - 1 : ℕ) = K := by omega
  rw [this, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have := Nat.ceil_lt_add_one (a := T / h) (by positivity)
  exact this.le

theorem ae_no_pair_fixed {δ : ℝ} (hδ : 0 < δ) (T : ℕ) :
    ∀ᵐ ω ∂P, ¬ ∃ s s', s ∈ Ioc 0 (T : ℝ) ∧ s' ∈ Ioc 0 (T : ℝ) ∧ IsJump (N ω) s ∧
        IsJump (N ω) s' ∧ s' - s = δ := by
  rw [ae_iff]
  push Not
  set c : ℝ := ((Fintype.card (Dir d) : ℝ)) with hc
  set C : ℝ := c ^ 2 * ((T : ℝ) + δ) * δ with hC
  have hbound : ∀ m : ℕ, P {ω | ∃ s s', s ∈ Ioc 0 (T : ℝ) ∧ s' ∈ Ioc 0 (T : ℝ) ∧
      IsJump (N ω) s ∧ IsJump (N ω) s' ∧ s' - s = δ} ≤
        ENNReal.ofReal (C * (1 / ((m : ℝ) + 1))) := by
    intro m
    have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have hh : 0 < δ / ((m : ℝ) + 2) := div_pos hδ hm2
    have hhδ : δ / ((m : ℝ) + 2) < δ := by
      rw [div_lt_iff₀ hm2]; nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    refine (prob_pair_le hN hh hhδ (Nat.cast_nonneg T)).trans (ENNReal.ofReal_le_ofReal ?_)
    set h : ℝ := δ / ((m : ℝ) + 2) with hh'
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have e1 : (T / h + 1) * (c * h) ^ 2 = c ^ 2 * (T * h + h ^ 2) := by
      field_simp
    rw [e1]
    have e2 : h ≤ δ * (1 / ((m : ℝ) + 1)) := by
      rw [hh', div_eq_mul_one_div]
      refine mul_le_mul_of_nonneg_left ?_ hδ.le
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have e3 : T * h + h ^ 2 ≤ (T + δ) * h := by nlinarith
    calc c ^ 2 * (T * h + h ^ 2) ≤ c ^ 2 * ((T + δ) * h) := by gcongr
      _ ≤ c ^ 2 * ((T + δ) * (δ * (1 / ((m : ℝ) + 1)))) := by gcongr
      _ = C * (1 / ((m : ℝ) + 1)) := by rw [hC]; ring
  have hlim : Filter.Tendsto (fun m : ℕ => ENNReal.ofReal (C * (1 / ((m : ℝ) + 1))))
      Filter.atTop (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
  exact le_antisymm (ge_of_tendsto' hlim hbound) bot_le

/-- No jumps at fixed times, no coincidences (b): for countable `Δ`, almost surely there are no jump times
`s < s'` with `s' - s ∈ Δ`. -/
theorem ae_no_jump_pair {Δ : Set ℝ} (hΔ : Δ.Countable) :
    ∀ᵐ ω ∂P, ∀ s s', IsJump (N ω) s → IsJump (N ω) s' → s < s' → s' - s ∉ Δ := by
  have h1 : ∀ᵐ ω ∂P, ∀ δ : Δ, ∀ T : ℕ, 0 < (δ : ℝ) → ¬ ∃ s s', s ∈ Ioc 0 (T : ℝ) ∧
      s' ∈ Ioc 0 (T : ℝ) ∧ IsJump (N ω) s ∧ IsJump (N ω) s' ∧ s' - s = (δ : ℝ) := by
    have := hΔ.to_subtype
    refine ae_all_iff.2 fun δ => ae_all_iff.2 fun T => ?_
    by_cases hδ : 0 < (δ : ℝ)
    · filter_upwards [ae_no_pair_fixed hN hδ T] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hδ
  filter_upwards [h1] with ω hω s s' hs hs' hss' hmem
  have hpos : 0 < s := hs.1
  obtain ⟨T, hT⟩ := exists_nat_ge s'
  refine hω ⟨s' - s, hmem⟩ T (by linarith) ⟨s, s', ⟨hpos, by linarith⟩,
    ⟨hpos.trans hss', hT⟩, hs, hs', rfl⟩

/-- No jumps at fixed times, no coincidences (b), `β ℤ_{≥1}` form: almost surely no two jumps of the
walk occur at times differing by an element of `β ℤ_{≥1}`. -/
theorem ae_no_jump_pair_mul {β : ℝ} (hβ : 0 < β) :
    ∀ᵐ ω ∂P, ∀ s s', IsJump (N ω) s → IsJump (N ω) s' → ∀ n : ℕ, 1 ≤ n → s' - s ≠ n * β := by
  have hc : ({x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ x = n * β}).Countable :=
    (Set.countable_range (fun n : ℕ => (n : ℝ) * β)).mono (by
      rintro x ⟨n, -, rfl⟩; exact ⟨n, rfl⟩)
  filter_upwards [ae_no_jump_pair hN hc] with ω hω s s' hs hs' n hn heq
  have hlt : s < s' := by
    have : (0 : ℝ) < n * β := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    linarith
  exact hω s s' hs hs' hlt ⟨n, hn, heq⟩

end Pairs

end SRW
end ElboimSly
