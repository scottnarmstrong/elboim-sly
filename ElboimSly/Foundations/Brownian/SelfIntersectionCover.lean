/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.SelfIntersectionGood

import Mathlib

/-!
# The volume of the past path near the present

ES22 Claim 9.4, Step 2 (i).

On the good event `G(a)`, the set `S_a = {z : ∃ s' ≤ a, ‖z - B s'‖ ≤ 1 + ρ}` meets the cube of
radius `R/2` around `B a` in a set of volume at most `M (6ρ)^5`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} {B : ℝ≥0 → Ω → R5}

/-- A nearest lattice point of the box. -/
lemma exists_latticePt {t : ℝ} (ht : 1 ≤ t) {y : R5} (hy : ‖y‖ ≤ t) :
    ∃ x ∈ latticeBox t, ‖latticePt x - y‖ ≤ 1 / 2 := by
  refine ⟨fun k => round (y k), ?_, ?_⟩
  · simp only [latticeBox, Fintype.mem_piFinset, Finset.mem_Icc]
    intro k
    have h1 : |y k| ≤ t := (norm_le_pi_norm y k).trans hy
    have h2 : |(round (y k) : ℝ) - y k| ≤ 1 / 2 := by
      rw [abs_sub_comm]; exact abs_sub_round (y k)
    have h3 : |(round (y k) : ℝ)| ≤ 2 * t := by
      calc |(round (y k) : ℝ)| = |((round (y k) : ℝ) - y k) + y k| := by ring_nf
        _ ≤ |(round (y k) : ℝ) - y k| + |y k| := abs_add_le _ _
        _ ≤ 2 * t := by linarith
    have h4 : (0 : ℝ) ≤ 2 * t := by linarith
    have hN : ((⌊2 * t⌋₊ : ℕ) : ℤ) = ⌊2 * t⌋ := Int.natCast_floor_eq_floor h4
    rw [hN]
    constructor
    · have h5 : -(round (y k)) ≤ ⌊2 * t⌋ :=
        Int.le_floor.2 (by push_cast; linarith [(abs_le.1 h3).1])
      omega
    · exact Int.le_floor.2 (by linarith [(abs_le.1 h3).2])
  · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro k
    simpa [latticePt, Real.norm_eq_abs] using abs_sub_round (y k) |>.trans_eq' (by rw [abs_sub_comm])

/-- The past path set `S_a = {z : ∃ s' ≤ a, ‖z - B s'‖ ≤ c}`. -/
def pastSet (B : ℝ≥0 → Ω → R5) (a : ℝ≥0) (c : ℝ) (ω : Ω) : Set R5 :=
  {y | ∃ s' ≤ a, ‖y - B s' ω‖ ≤ c}

/-- ES22 Claim 9.4, Step 2 (i). On the good event, the past path set
meets the cube of radius `R/2` around `B a` in a set of volume at most `M (6ρ)^5`. -/
lemma volume_pastSet_le {a : ℝ≥0} {t ρ R M : ℝ} (ht : 1 ≤ t) (hρ : 1 ≤ ρ) (hR : 2 + 4 * ρ ≤ R)
    {ω : Ω} (hω : ω ∈ good B t ρ (3 * R) M a) :
    volume (pastSet B a (1 + ρ) ω ∩ Metric.closedBall (B a ω) (R / 2)) ≤
      ENNReal.ofReal (M * (6 * ρ) ^ 5) := by
  obtain ⟨x, hx, hxd⟩ := exists_latticePt ht (hω.1.1 a le_rfl)
  set Nset : Finset ℕ := (Finset.range (⌊(a : ℝ)⌋₊ + 1)).filter
    fun i : ℕ => ‖B (i : ℝ≥0) ω - latticePt x‖ ≤ 3 * R with hNset
  have hcard : (Nset.card : ℝ) ≤ M := hω.2 x hx
  have hcover : pastSet B a (1 + ρ) ω ∩ Metric.closedBall (B a ω) (R / 2) ⊆
      ⋃ i ∈ Nset, Metric.closedBall (B (i : ℝ≥0) ω) (1 + 2 * ρ) := by
    rintro y ⟨⟨s', hs', hy⟩, hy2⟩
    rw [Metric.mem_closedBall, dist_eq_norm] at hy2
    set i : ℕ := ⌊(s' : ℝ)⌋₊ with hi
    have hi1 : (i : ℝ) ≤ s' := Nat.floor_le s'.2
    have hi2 : (s' : ℝ) < i + 1 := Nat.lt_floor_add_one _
    have hia : (i : ℝ≥0) ≤ a := le_trans (by exact_mod_cast hi1) hs'
    have hpair : (s', (i : ℝ≥0)) ∈ closePairs (Set.Icc 0 a) 1 := by
      refine ⟨⟨zero_le, hs'⟩, ⟨zero_le, hia⟩, ?_⟩
      rw [NNReal.dist_eq, abs_le]
      push_cast
      constructor <;> linarith
    have hosc : ‖B s' ω - B (i : ℝ≥0) ω‖ ≤ ρ := hω.1.2 _ hpair
    have hyi : ‖y - B (i : ℝ≥0) ω‖ ≤ 1 + 2 * ρ := by
      calc ‖y - B (i : ℝ≥0) ω‖ = ‖(y - B s' ω) + (B s' ω - B (i : ℝ≥0) ω)‖ := by ring_nf
        _ ≤ ‖y - B s' ω‖ + ‖B s' ω - B (i : ℝ≥0) ω‖ := norm_add_le _ _
        _ ≤ 1 + 2 * ρ := by linarith
    have hmem : i ∈ Nset := by
      rw [hNset, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.lt_succ_of_le (Nat.le_floor (by exact_mod_cast hia)), ?_⟩
      calc ‖B (i : ℝ≥0) ω - latticePt x‖
          = ‖(B (i : ℝ≥0) ω - y) + (y - B a ω) + (B a ω - latticePt x)‖ := by ring_nf
        _ ≤ ‖B (i : ℝ≥0) ω - y‖ + ‖y - B a ω‖ + ‖B a ω - latticePt x‖ :=
            (norm_add₃_le)
        _ ≤ 3 * R := by
            rw [norm_sub_rev (B (i : ℝ≥0) ω) y]
            rw [norm_sub_rev (B a ω) (latticePt x)] at *
            linarith
    exact Set.mem_iUnion₂.2 ⟨i, hmem, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hyi⟩
  have hρ0 : 0 ≤ 1 + 2 * ρ := by linarith
  calc _ ≤ volume (⋃ i ∈ Nset, Metric.closedBall (B (i : ℝ≥0) ω) (1 + 2 * ρ)) :=
        measure_mono hcover
    _ ≤ ∑ i ∈ Nset, volume (Metric.closedBall (B (i : ℝ≥0) ω) (1 + 2 * ρ)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _i ∈ Nset, ENNReal.ofReal ((2 * (1 + 2 * ρ)) ^ 5) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.volume_pi_closedBall _ hρ0]; simp
    _ = (Nset.card : ℝ≥0∞) * ENNReal.ofReal ((2 * (1 + 2 * ρ)) ^ 5) := by simp
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal ((6 * ρ) ^ 5) := by
        refine mul_le_mul' ?_ (ENNReal.ofReal_le_ofReal ?_)
        · rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hcard
        · exact pow_le_pow_left₀ (by positivity) (by linarith) 5
    _ = _ := by
        rw [← ENNReal.ofReal_mul (le_trans (Nat.cast_nonneg _) hcard)]

end ElboimSly.Brownian
