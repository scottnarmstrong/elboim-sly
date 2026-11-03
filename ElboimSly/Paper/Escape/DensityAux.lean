/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Visits
public import Mathlib

/-!
# Auxiliary counting and asymptotics for density of the explored walks around p_i

* `ncard_biUnion_le`: cardinality of a finite union.
* `ncard_nbhd_le`: the `ℓ∞`-unit neighbourhood of a finite set has at most `3^d` times its size.
* `F_mono`: `R ↦ R² (ln R)^m` is nondecreasing on `[1, ∞)`.
* `eventually_log_le`: `(ln x)^m ≤ ε x^a` eventually.
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper

lemma ncard_biUnion_le {α : Type*} (F : Finset ℕ) (A : ℕ → Set α) :
    (⋃ ℓ ∈ F, A ℓ).ncard ≤ ∑ ℓ ∈ F, (A ℓ).ncard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
    rw [Finset.sum_insert ha]
    simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
    refine (Set.ncard_union_le _ _).trans ?_
    exact Nat.add_le_add_left ih _

lemma nbhd_finite {d : ℕ} (X : Set (Fin d → ℤ)) (hX : X.Finite) :
    {y : Fin d → ℤ | ∃ x ∈ X, ‖y - x‖ ≤ 1}.Finite := by
  classical
  have hsub : {y : Fin d → ℤ | ∃ x ∈ X, ‖y - x‖ ≤ 1} ⊆
      (fun p : (Fin d → ℤ) × (Fin d → ℤ) => p.1 + p.2) ''
        (X ×ˢ (↑(ballFin (0 : Fin d → ℤ) 1) : Set (Fin d → ℤ))) := by
    rintro y ⟨x, hx, hy⟩
    refine ⟨(x, y - x), ⟨hx, ?_⟩, by simp⟩
    have := mem_ballFin (x := y - x) (y := 0) (L := 1) (by norm_num) (by simpa using hy)
    simpa using this
  exact ((hX.prod (Finset.finite_toSet _)).image _).subset hsub

lemma ncard_nbhd_le {d : ℕ} (X : Set (Fin d → ℤ)) (hX : X.Finite) :
    {y : Fin d → ℤ | ∃ x ∈ X, ‖y - x‖ ≤ 1}.ncard ≤ 3 ^ d * X.ncard := by
  classical
  have hsub : {y : Fin d → ℤ | ∃ x ∈ X, ‖y - x‖ ≤ 1} ⊆
      (fun p : (Fin d → ℤ) × (Fin d → ℤ) => p.1 + p.2) ''
        (X ×ˢ (↑(ballFin (0 : Fin d → ℤ) 1) : Set (Fin d → ℤ))) := by
    rintro y ⟨x, hx, hy⟩
    refine ⟨(x, y - x), ⟨hx, ?_⟩, by simp⟩
    have := mem_ballFin (x := y - x) (y := 0) (L := 1) (by norm_num) (by simpa using hy)
    simpa using this
  have hfin : (X ×ˢ (↑(ballFin (0 : Fin d → ℤ) 1) : Set (Fin d → ℤ))).Finite :=
    hX.prod (Finset.finite_toSet _)
  calc {y : Fin d → ℤ | ∃ x ∈ X, ‖y - x‖ ≤ 1}.ncard
      ≤ ((fun p : (Fin d → ℤ) × (Fin d → ℤ) => p.1 + p.2) ''
        (X ×ˢ (↑(ballFin (0 : Fin d → ℤ) 1) : Set (Fin d → ℤ)))).ncard :=
        Set.ncard_le_ncard hsub ((hfin).image _)
    _ ≤ (X ×ˢ (↑(ballFin (0 : Fin d → ℤ) 1) : Set (Fin d → ℤ))).ncard :=
        Set.ncard_image_le hfin
    _ = X.ncard * (ballFin (0 : Fin d → ℤ) 1).card := by
        rw [Set.ncard_prod, Set.ncard_coe_finset]
    _ = 3 ^ d * X.ncard := by
        rw [card_ballFin]; simp [mul_comm]

lemma F_mono {m : ℕ} {R R' : ℝ} (h1 : 1 ≤ R) (h : R ≤ R') :
    R ^ 2 * Real.log R ^ m ≤ R' ^ 2 * Real.log R' ^ m := by
  have hl : 0 ≤ Real.log R := Real.log_nonneg h1
  have hll : Real.log R ≤ Real.log R' := Real.log_le_log (by linarith) h
  exact mul_le_mul (pow_le_pow_left₀ (by linarith) h 2) (pow_le_pow_left₀ hl hll m)
    (pow_nonneg hl _) (by positivity)

lemma eventually_log_le (m a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ m ≤ ε * x ^ a := by
  have h := (isLittleO_log_rpow_rpow_atTop m ha).bound hε
  filter_upwards [h, eventually_gt_atTop 1] with x hx hx1
  have h0 : 0 ≤ Real.log x ^ m := Real.rpow_nonneg (Real.log_nonneg hx1.le) _
  have h1 : 0 ≤ x ^ a := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg h1] at hx
  exact hx

end ElboimSly.Paper
