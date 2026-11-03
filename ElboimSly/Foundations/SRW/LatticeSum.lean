/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Exponential lattice sums

Exponential lattice sums.  For `c > 0` and `R ≥ 0`,
`∑_{v ∈ ℤ^d, ‖v‖ ≥ R} e^{-c‖v‖} ≤ C_lat(c,d) e^{-cR/2}` with
`C_lat(c,d) = (4/c)^d d! e^{c/4} / (1 - e^{-c/2})`.  The sum is the (unconditional) `tsum` of a
nonnegative family; the bound is proved on every finite partial sum.
-/

@[expose] public section

open Finset

namespace ElboimSly
namespace SRW

/-- The constant `C_lat(c,d)`. -/
noncomputable def latConst (c : ℝ) (d : ℕ) : ℝ :=
  (4 / c) ^ d * (d.factorial : ℝ) * Real.exp (c / 4) / (1 - Real.exp (-c / 2))

/-- The sup norm of an integer vector, as a natural number. -/
def nrm {d : ℕ} (v : Fin d → ℤ) : ℕ := Finset.univ.sup fun i => (v i).natAbs

theorem norm_coord_eq {d : ℕ} (v : Fin d → ℤ) (i : Fin d) : ‖v i‖ = (((v i).natAbs : ℕ) : ℝ) := by
  rw [Int.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs]

theorem norm_eq_nrm {d : ℕ} (v : Fin d → ℤ) : ‖v‖ = (nrm v : ℝ) := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    intro i
    rw [norm_coord_eq]
    exact_mod_cast Finset.le_sup (f := fun i => (v i).natAbs) (Finset.mem_univ i)
  · have : nrm v ≤ ⌊‖v‖⌋₊ := by
      unfold nrm
      refine Finset.sup_le fun i _ => Nat.le_floor ?_
      rw [← norm_coord_eq]; exact norm_le_pi_norm v i
    exact (Nat.cast_le.2 this).trans (Nat.floor_le (norm_nonneg _))

/-- The integer points of sup norm `k` lie in a box with `(2k+1)^d` points. -/
theorem card_fiber_le {d : ℕ} (S : Finset (Fin d → ℤ)) (k : ℕ) :
    (S.filter fun v => nrm v = k).card ≤ (2 * k + 1) ^ d := by
  have hsub : (S.filter fun v => nrm v = k) ⊆
      Fintype.piFinset fun _ : Fin d => Finset.Icc (-(k : ℤ)) k := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h : (v i).natAbs ≤ k := hv.2 ▸ Finset.le_sup (f := fun i => (v i).natAbs)
      (Finset.mem_univ i)
    omega
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

theorem pow_le_exp_mul {c : ℝ} (hc : 0 < c) (d k : ℕ) :
    ((2 * k + 1 : ℕ) : ℝ) ^ d ≤ (4 / c) ^ d * d.factorial * Real.exp (c / 4) *
      Real.exp (c * k / 2) := by
  have hx : 0 ≤ c / 4 * ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have h := Real.pow_div_factorial_le_exp _ hx d
  rw [div_le_iff₀ (by positivity)] at h
  have e : ((2 * k + 1 : ℕ) : ℝ) ^ d = (4 / c) ^ d * (c / 4 * ((2 * k + 1 : ℕ) : ℝ)) ^ d := by
    rw [← mul_pow]; congr 1; field_simp
  rw [e]
  have e2 : Real.exp (c / 4 * ((2 * k + 1 : ℕ) : ℝ)) = Real.exp (c / 4) * Real.exp (c * k / 2) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  rw [e2] at h
  calc (4 / c) ^ d * (c / 4 * ((2 * k + 1 : ℕ) : ℝ)) ^ d
      ≤ (4 / c) ^ d * (Real.exp (c / 4) * Real.exp (c * k / 2) * d.factorial) := by gcongr
    _ = _ := by ring

/-- Exponential lattice sums. -/
theorem lattice_sum (d : ℕ) {c R : ℝ} (hc : 0 < c) (_hR : 0 ≤ R) :
    ∑' v : Fin d → ℤ, (if R ≤ ‖v‖ then Real.exp (-c * ‖v‖) else 0) ≤
      latConst c d * Real.exp (-c * R / 2) := by
  set q : ℝ := Real.exp (-c / 2) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    have := Real.exp_lt_exp.2 (show -c / 2 < 0 by linarith)
    rw [Real.exp_zero] at this; exact this
  set C0 : ℝ := (4 / c) ^ d * d.factorial * Real.exp (c / 4) with hC0
  have hC0pos : 0 ≤ C0 := by positivity
  have hlat : latConst c d = C0 / (1 - q) := by unfold latConst; rw [hC0]
  set N : ℕ := ⌈R⌉₊ with hN
  have hqN : q ^ N ≤ Real.exp (-c * R / 2) := by
    rw [hq, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have : R ≤ N := Nat.le_ceil R
    nlinarith
  refine tsum_le_of_sum_le' (mul_nonneg (by rw [hlat]; exact div_nonneg hC0pos (by linarith))
    (Real.exp_pos _).le) fun S => ?_
  set K : ℕ := S.sup nrm with hK
  have hmaps : ∀ v ∈ S, nrm v ∈ Finset.range (K + 1) := fun v hv =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := nrm) hv))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- bound each fiber
  have hfib : ∀ k ∈ Finset.range (K + 1),
      ∑ v ∈ S.filter (fun v => nrm v = k), (if R ≤ ‖v‖ then Real.exp (-c * ‖v‖) else 0) ≤
        if N ≤ k then C0 * q ^ k else 0 := by
    intro k _
    by_cases hk : N ≤ k
    · rw [ite_eq_left hk]
      have hkR : R ≤ k := (Nat.le_ceil R).trans (by exact_mod_cast hk)
      have hterm : ∀ v ∈ S.filter (fun v => nrm v = k),
          (if R ≤ ‖v‖ then Real.exp (-c * ‖v‖) else 0) = Real.exp (-c * k) := by
        intro v hv
        have hnv : ‖v‖ = k := by rw [norm_eq_nrm, (Finset.mem_filter.1 hv).2]
        rw [hnv, ite_eq_left hkR]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((S.filter fun v => nrm v = k).card : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) ^ d := by
        exact_mod_cast card_fiber_le S k
      calc ((S.filter fun v => nrm v = k).card : ℝ) * Real.exp (-c * k)
          ≤ ((2 * k + 1 : ℕ) : ℝ) ^ d * Real.exp (-c * k) := by gcongr
        _ ≤ (C0 * Real.exp (c * k / 2)) * Real.exp (-c * k) := by
            gcongr
            have := pow_le_exp_mul hc d k
            rw [hC0]; linarith
        _ = C0 * q ^ k := by
            rw [mul_assoc, ← Real.exp_add, hq, ← Real.exp_nat_mul]
            congr 2; ring
    · rw [ite_eq_right hk]
      refine le_of_eq (Finset.sum_eq_zero fun v hv => ?_)
      have hnv : ‖v‖ = k := by rw [norm_eq_nrm, (Finset.mem_filter.1 hv).2]
      rw [hnv, ite_eq_right]
      intro hRk
      apply hk
      exact Nat.ceil_le.2 hRk
  refine (Finset.sum_le_sum hfib).trans ?_
  have hsum : ∑ k ∈ Finset.range (K + 1), (if N ≤ k then C0 * q ^ k else 0) =
      C0 * ∑ k ∈ Finset.Ico N (K + 1), q ^ k := by
    rw [Finset.mul_sum, ← Finset.sum_filter]
    · congr 1
      ext k; simp [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]; omega
  rw [hsum, hlat]
  have hgeo := geom_sum_Ico_le_of_lt_one hq0.le hq1 (m := N) (n := K + 1)
  calc C0 * ∑ k ∈ Finset.Ico N (K + 1), q ^ k ≤ C0 * (q ^ N / (1 - q)) := by gcongr
    _ = C0 / (1 - q) * q ^ N := by ring
    _ ≤ C0 / (1 - q) * Real.exp (-c * R / 2) := by
        gcongr

end SRW
end ElboimSly
