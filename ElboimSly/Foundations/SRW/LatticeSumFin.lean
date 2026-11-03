/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.LatticeSum
public import Mathlib

/-!
# The lattice sum: finite-sum form and summability

Exponential lattice sums (the finite-sum form behind it), used in SRW content of Lemma 8.2 (b).
-/

@[expose] public section

open Set Filter
open scoped NNReal Real

namespace ElboimSly
namespace SRW

theorem lattice_sum_finset (d : ℕ) {c R : ℝ} (hc : 0 < c) (_hR : 0 ≤ R)
    (S : Finset (Fin d → ℤ)) :
    ∑ v ∈ S, (if R ≤ ‖v‖ then Real.exp (-c * ‖v‖) else 0) ≤
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


theorem summable_lattice (d : ℕ) {c R : ℝ} (hc : 0 < c) (hR : 0 ≤ R) :
    Summable fun v : Fin d → ℤ => (if R ≤ ‖v‖ then Real.exp (-c * ‖v‖) else 0) :=
  summable_of_sum_le (fun v => by split_ifs <;> positivity)
    (fun S => lattice_sum_finset d hc hR S)

end SRW
end ElboimSly
