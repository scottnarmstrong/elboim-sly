/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Lattice auxiliaries for Lemma 7.7 (transition probabilities)

ES22 Lemma 7.7.

* `lattice_ball_finite`, `card_lattice_ball_le`: the lattice points of `ℤ^d` within sup-norm
  distance `R` of a point are finitely many, at most `(2R+1)^d`.
* `measure_add_eq_le`: for independent `ℤ^d`-valued `a, b` with `ℙ(b = x) ≤ q` for all `x`,
  `ℙ(a + b = v) ≤ ℙ(‖b‖ > ρ) + q ℙ(‖a - v‖ ≤ ρ)` (the displayed estimate "by independence and
  (H2)" in ES22 Lemma 7.7).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Step

variable {d : ℕ}

/-- The lattice points within sup-norm distance `R` of `v` lie in a box. -/
theorem lattice_ball_subset_Icc (v : Fin d → ℤ) {R : ℝ} :
    {w : Fin d → ℤ | ‖w - v‖ ≤ R} ⊆
      Set.Icc (v - fun _ => ⌊R⌋ : Fin d → ℤ) (v + fun _ => ⌊R⌋ : Fin d → ℤ) := by
  intro w hw
  have h1 : ∀ i, |((w i : ℝ) - (v i : ℝ))| ≤ R := fun i => by
    have := norm_le_pi_norm (w - v) i
    have h2 : ‖(w - v) i‖ ≤ R := this.trans hw
    simpa [Int.norm_eq_abs] using h2
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h3 := abs_le.1 (h1 i)
    have : -(w i - v i) ≤ ⌊R⌋ := Int.le_floor.2 (by push_cast; linarith [h3.1])
    simp only [Pi.sub_apply]; linarith
  · have h3 := abs_le.1 (h1 i)
    have : w i - v i ≤ ⌊R⌋ := Int.le_floor.2 (by push_cast; linarith [h3.2])
    simp only [Pi.add_apply]; linarith

theorem lattice_ball_finite (v : Fin d → ℤ) (R : ℝ) : {w : Fin d → ℤ | ‖w - v‖ ≤ R}.Finite :=
  (Set.finite_Icc _ _).subset (lattice_ball_subset_Icc v)

/-- The number of lattice points within distance `R` of `v` is at most `(2R+1)^d`. -/
theorem ncard_lattice_ball_le (v : Fin d → ℤ) {R : ℝ} (hR : 0 ≤ R) :
    ((lattice_ball_finite v R).toFinset.card : ℝ) ≤ (2 * R + 1) ^ d := by
  have hsub := Finset.card_le_card
    (show (lattice_ball_finite v R).toFinset ⊆
        Finset.Icc (v - fun _ => ⌊R⌋ : Fin d → ℤ) (v + fun _ => ⌊R⌋ : Fin d → ℤ) from
      fun w hw => by
        simp only [Set.Finite.mem_toFinset] at hw
        exact Finset.mem_Icc.2 (lattice_ball_subset_Icc v hw))
  rw [Pi.card_Icc] at hsub
  have hc : ∀ i : Fin d, (Finset.Icc ((v - fun _ => ⌊R⌋ : Fin d → ℤ) i)
      ((v + fun _ => ⌊R⌋ : Fin d → ℤ) i)).card = (2 * ⌊R⌋ + 1).toNat := fun i => by
    simp only [Int.card_Icc, Pi.sub_apply, Pi.add_apply]
    congr 1; ring
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hsub
  have hfl : (0 : ℤ) ≤ ⌊R⌋ := Int.floor_nonneg.2 hR
  have h2 : (((2 * ⌊R⌋ + 1).toNat : ℕ) : ℝ) ≤ 2 * R + 1 := by
    have : (((2 * ⌊R⌋ + 1).toNat : ℕ) : ℤ) = 2 * ⌊R⌋ + 1 := Int.toNat_of_nonneg (by omega)
    have h3 : (((2 * ⌊R⌋ + 1).toNat : ℕ) : ℝ) = 2 * (⌊R⌋ : ℝ) + 1 := by exact_mod_cast this
    rw [h3]; linarith [Int.floor_le R]
  calc _ ≤ (((2 * ⌊R⌋ + 1).toNat ^ d : ℕ) : ℝ) := by exact_mod_cast hsub
    _ = (((2 * ⌊R⌋ + 1).toNat : ℕ) : ℝ) ^ d := by push_cast; rfl
    _ ≤ (2 * R + 1) ^ d := by gcongr

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Independence step of ES22 Lemma 7.7.** For independent `ℤ^d`-valued `a, b` with
`ℙ(b = x) ≤ q` for every `x`: `ℙ(a + b = v) ≤ ℙ(ρ < ‖b‖) + q ℙ(‖a - v‖ ≤ ρ)`. -/
theorem measure_add_eq_le [IsProbabilityMeasure P] {a b : Ω → Fin d → ℤ} (ha : Measurable a)
    (hab : IndepFun a b P) {q : ℝ≥0∞} (hq : ∀ x, P {ω | b ω = x} ≤ q)
    (v : Fin d → ℤ) (ρ : ℝ) :
    P {ω | a ω + b ω = v} ≤ P {ω | ρ < ‖b ω‖} + q * P {ω | ‖a ω - v‖ ≤ ρ} := by
  classical
  set S := (lattice_ball_finite v ρ).toFinset with hS
  have hsub : {ω | a ω + b ω = v} ⊆
      {ω | ρ < ‖b ω‖} ∪ ⋃ w ∈ S, (a ⁻¹' {w} ∩ b ⁻¹' {v - w}) := by
    intro ω hω
    by_cases hbω : ρ < ‖b ω‖
    · exact Or.inl hbω
    · refine Or.inr (mem_iUnion₂.2 ⟨a ω, ?_, rfl, ?_⟩)
      · simp only [hS, Set.Finite.mem_toFinset]
        have h1 : a ω - v = -b ω := by
          have : a ω + b ω = v := hω
          rw [← this]; abel
        show ‖a ω - v‖ ≤ ρ
        rw [h1, norm_neg]; exact not_lt.1 hbω
      · exact eq_sub_of_add_eq' hω
  have hind : ∀ w ∈ S, P (a ⁻¹' {w} ∩ b ⁻¹' {v - w}) = P (a ⁻¹' {w}) * P (b ⁻¹' {v - w}) :=
    fun w _ => hab.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton _)
      (measurableSet_singleton _)
  have h1 : P (⋃ w ∈ S, (a ⁻¹' {w} ∩ b ⁻¹' {v - w})) ≤ q * P {ω | ‖a ω - v‖ ≤ ρ} := by
    calc P (⋃ w ∈ S, (a ⁻¹' {w} ∩ b ⁻¹' {v - w}))
        ≤ ∑ w ∈ S, P (a ⁻¹' {w} ∩ b ⁻¹' {v - w}) := measure_biUnion_finset_le _ _
      _ = ∑ w ∈ S, P (a ⁻¹' {w}) * P (b ⁻¹' {v - w}) := Finset.sum_congr rfl hind
      _ ≤ ∑ w ∈ S, P (a ⁻¹' {w}) * q := Finset.sum_le_sum fun w _ =>
          by gcongr; exact hq (v - w)
      _ = (∑ w ∈ S, P (a ⁻¹' {w})) * q := (Finset.sum_mul _ _ _).symm
      _ = P (⋃ w ∈ S, a ⁻¹' {w}) * q := by
          congr 1
          refine (measure_biUnion_finset ?_ fun w _ => ha (measurableSet_singleton w)).symm
          intro w _ w' _ hww'
          exact Disjoint.preimage a (disjoint_singleton.2 hww')
      _ ≤ P {ω | ‖a ω - v‖ ≤ ρ} * q := by
          gcongr
          intro ω hω
          obtain ⟨w, hwS, hw⟩ := mem_iUnion₂.1 hω
          have : a ω = w := hw
          simp only [hS, Set.Finite.mem_toFinset] at hwS
          show ‖a ω - v‖ ≤ ρ
          rw [this]; exact hwS
      _ = q * P {ω | ‖a ω - v‖ ≤ ρ} := mul_comm _ _
  calc P {ω | a ω + b ω = v}
      ≤ P ({ω | ρ < ‖b ω‖} ∪ ⋃ w ∈ S, (a ⁻¹' {w} ∩ b ⁻¹' {v - w})) := measure_mono hsub
    _ ≤ P {ω | ρ < ‖b ω‖} + P (⋃ w ∈ S, (a ⁻¹' {w} ∩ b ⁻¹' {v - w})) := measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl h1

end ElboimSly.Paper.Step
