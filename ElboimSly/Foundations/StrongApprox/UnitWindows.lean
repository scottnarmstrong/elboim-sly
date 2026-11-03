/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.Poisson
public import ElboimSly.Foundations.SRW.GoodAe
public import ElboimSly.Foundations.SRW.Increments
public import Mathlib

/-!
# Fluctuations of the SRW over short windows

Fluctuations over short windows.  For a Poisson point process `N` with intensity `μ_d`, `T ≥ 0`,
`h > 0`, `a ≥ 0`:
`P(∃ 0 ≤ s ≤ s' ≤ T, s' - s ≤ h, ‖X(s') - X(s)‖₁ ≥ a) ≤ (T/h + 1) exp(4 d h (e - 1) - a)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

open SRW

/-- The Poisson upper tail with the exponential-moment bound `θ = 1`. -/
theorem poisson_ge_le (r : ℝ≥0) (a : ℝ) :
    poissonMeasure r {n : ℕ | a ≤ (n : ℝ)} ≤ ENNReal.ofReal (Real.exp (r * (Real.exp 1 - 1) - a)) := by
  have hP : HasLaw (id : ℕ → ℕ) (poissonMeasure r) (poissonMeasure r) :=
    ⟨aemeasurable_id, Measure.map_id⟩
  have h := poisson_upper_markov hP (θ := 1) zero_le_one (a - r)
  have hset : {ω : ℕ | a - r ≤ ((id ω : ℕ) : ℝ) - r} = {n : ℕ | a ≤ (n : ℝ)} := by
    ext n; simp
  rw [hset] at h
  have h2 : Real.exp (-1 * (a - r)) * Real.exp (r * (Real.exp 1 - 1 - 1)) =
      Real.exp (r * (Real.exp 1 - 1) - a) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2] at h
  calc poissonMeasure r {n : ℕ | a ≤ (n : ℝ)}
      = ENNReal.ofReal ((poissonMeasure r).real {n : ℕ | a ≤ (n : ℝ)}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal h

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {N : Ω → Measure (Dir d × ℝ)} {P : Measure Ω}

/-- The tail of the number of points in a window. -/
theorem prob_window_ge_le (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (a : ℝ) :
    P {ω | ENNReal.ofReal a ≤ N ω (univ ×ˢ Ioc x y)} ≤
      ENNReal.ofReal (Real.exp ((2 * d) * (y - x) * (Real.exp 1 - 1) - a)) := by
  have hm : MeasurableSet (univ ×ˢ Ioc x y : Set (Dir d × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ioc
  have h1 : {ω | ENNReal.ofReal a ≤ N ω (univ ×ˢ Ioc x y)} =
      (fun ω => N ω (univ ×ˢ Ioc x y)) ⁻¹' Ici (ENNReal.ofReal a) := rfl
  rw [h1, ← Measure.map_apply (hN.measurable_count hm) (measurableSet_Ici), hN.map_count hm,
    clock_univ_Ioc hx]
  set r : ℝ≥0 := (((Fintype.card (Dir d) : ℝ) * (y - x)).toNNReal) with hr
  have hx' : (Fintype.card (Dir d) : ℝ≥0∞) * ENNReal.ofReal (y - x) = (r : ℝ≥0∞) := by
    show _ = ENNReal.ofReal _
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [hx', extPoissonMeasure_coe, Measure.map_apply Measurable.of_discrete measurableSet_Ici]
  have hset : (Nat.cast : ℕ → ℝ≥0∞) ⁻¹' Ici (ENNReal.ofReal a) = {n : ℕ | a ≤ (n : ℝ)} := by
    ext n
    simp only [mem_preimage, mem_Ici, mem_ofPred_eq]
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)]
  rw [hset]
  refine (poisson_ge_le r a).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  have hcard : (Fintype.card (Dir d) : ℝ) = 2 * d := by simp [Fintype.card_prod]; ring
  have hrr : (r : ℝ) = (2 * d) * (y - x) := by
    rw [hr, Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 hxy)), hcard]
  rw [hrr]

/-- The `ℓ¹` size of an increment of the walk. -/
noncomputable def incrL1 (d : ℕ) (ν : Measure (Dir d × ℝ)) (s t : ℝ) : ℝ :=
  ∑ i, |((walk d ν t i : ℤ) : ℝ) - ((walk d ν s i : ℤ) : ℝ)|

theorem incrL1_le {ν : Measure (Dir d × ℝ)} (hν : ν ∈ goodSet d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ENNReal.ofReal (incrL1 d ν s t) ≤ tot ν (Ioc s t) := by
  have h := walk_sub_l1_le hν hs hst
  refine le_trans (le_of_eq ?_) h
  unfold incrL1
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : |((walk d ν t i : ℤ) : ℝ) - ((walk d ν s i : ℤ) : ℝ)| =
      (((walk d ν t i - walk d ν s i).natAbs : ℕ) : ℝ) := by
    rw [← Int.cast_sub, Nat.cast_natAbs, Int.cast_abs]
  rw [e, ENNReal.ofReal_natCast]

/-- Fluctuations over short windows. -/
theorem unit_windows (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) {T h : ℝ}
    (hT : 0 ≤ T) (hh : 0 < h) (a : ℝ) :
    P {ω | ∃ s s' : ℝ, 0 ≤ s ∧ s ≤ s' ∧ s' ≤ T ∧ s' - s ≤ h ∧ a ≤ incrL1 d (N ω) s s'} ≤
      ENNReal.ofReal ((T / h + 1) * Real.exp (4 * d * h * (Real.exp 1 - 1) - a)) := by
  set M : ℕ := ⌊T / h⌋₊ with hM
  set W : ℕ → Set Ω := fun k => {ω | ENNReal.ofReal a ≤ N ω (univ ×ˢ Ioc (k * h) ((k + 2) * h))}
    with hW
  have hsub : {ω | ∃ s s' : ℝ, 0 ≤ s ∧ s ≤ s' ∧ s' ≤ T ∧ s' - s ≤ h ∧ a ≤ incrL1 d (N ω) s s'} ⊆
      {ω | N ω ∉ goodSet d} ∪ ⋃ k ∈ Finset.range (M + 1), W k := by
    rintro ω ⟨s, s', hs, hss', hs'T, hh', ha⟩
    by_cases hg : N ω ∈ goodSet d
    · right
      simp only [mem_iUnion]
      set k : ℕ := ⌊s / h⌋₊ with hk
      have hk1 : (k : ℝ) * h ≤ s := by
        have := Nat.floor_le (div_nonneg hs hh.le) (a := s / h)
        rwa [← hk, le_div_iff₀ hh] at this
      have hk2 : s < ((k : ℝ) + 1) * h := by
        have := Nat.lt_floor_add_one (s / h)
        rwa [← hk, div_lt_iff₀ hh] at this
      have hkM : k ≤ M := by
        refine Nat.floor_le_floor ?_
        exact div_le_div_of_nonneg_right (by linarith) hh.le
      refine ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hkM), ?_⟩
      show ENNReal.ofReal a ≤ N ω (univ ×ˢ Ioc (k * h) ((k + 2) * h))
      have hsub' : Ioc s s' ⊆ Ioc (k * h) ((k + 2) * h) :=
        Ioc_subset_Ioc hk1 (by linarith)
      calc ENNReal.ofReal a ≤ ENNReal.ofReal (incrL1 d (N ω) s s') := ENNReal.ofReal_le_ofReal ha
        _ ≤ tot (N ω) (Ioc s s') := incrL1_le hg hs hss'
        _ ≤ N ω (univ ×ˢ Ioc (k * h) ((k + 2) * h)) := measure_mono (prod_mono subset_rfl hsub')
    · exact Or.inl hg
  have hnull : P {ω | N ω ∉ goodSet d} = 0 := by
    have := ae_good hN
    rwa [ae_iff] at this
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  rw [hnull, zero_add]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hW' : ∀ k ∈ Finset.range (M + 1), P (W k) ≤
      ENNReal.ofReal (Real.exp (4 * d * h * (Real.exp 1 - 1) - a)) := by
    intro k _
    have hk0 : (0 : ℝ) ≤ k * h := by positivity
    refine (prob_window_ge_le hN hk0 (by linarith) a).trans (ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 (le_of_eq ?_)))
    ring
  refine (Finset.sum_le_sum hW').trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [ENNReal.ofReal_mul (by positivity)]
  gcongr
  rw [show ((M + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((M : ℝ) + 1) by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one]; simp]
  refine ENNReal.ofReal_le_ofReal ?_
  have : (M : ℝ) ≤ T / h := Nat.floor_le (div_nonneg hT hh.le)
  linarith

end StrongApprox
end ElboimSly
