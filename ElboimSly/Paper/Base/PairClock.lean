/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenRegionBasic
public import Mathlib

/-!
# Clocks of two walks within one lap

Cyclic walks within one lap (b), (c), "Driven record".

For forward walk data the clock is `c_δ(r) = [q + r] ∈ ℝ/βℤ`.  Within a window of length `L < β`
two clocks with the same phase coincide exactly at equal times (`clock_eq_iff_of_lt`), and two
clocks with phases `q < q'` such that the windows are disjoint modulo `β` never coincide
(`clock_ne_of_disjoint`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

variable {I : Type*} {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
theorem clock_fwd (δ : CycData I d) (h : δ.fwd = true) (r : ℝ≥0) :
    δ.clock β r = ((δ.phase + (r : ℝ) : ℝ) : AddCircle β) := by
  simp [CycData.clock, CycData.sgn, h]

omit [Fact (0 < β)] in
theorem clock_eq_iff_int {δ δ' : CycData I d} (h : δ.fwd = true) (h' : δ'.fwd = true)
    {r r' : ℝ≥0} :
    δ.clock β r = δ'.clock β r' ↔ ∃ k : ℤ, δ'.phase + r' - (δ.phase + r) = k * β := by
  rw [clock_fwd δ h, clock_fwd δ' h', ← sub_eq_zero, ← AddCircle.coe_sub,
    AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨-n, by simp only [zsmul_eq_mul] at hn; push_cast; linarith⟩
  · rintro ⟨n, hn⟩
    exact ⟨-n, by simp only [zsmul_eq_mul]; push_cast; linarith⟩

omit [Fact (0 < β)] in
theorem int_mul_eq_zero_of_abs_lt {x : ℝ} (hβ : 0 < β) (hx : |x| < β) (k : ℤ) (hk : x = k * β) :
    x = 0 := by
  have h1 : |(k : ℝ)| < 1 := by
    have : |x| = |(k : ℝ)| * β := by rw [hk, abs_mul, abs_of_pos hβ]
    rw [this] at hx
    by_contra hcon
    push Not at hcon
    nlinarith
  have : k = 0 := by
    have : |k| < 1 := by exact_mod_cast h1
    rw [abs_lt] at this
    omega
  rw [hk, this]; simp

/-- Within a window of length `L < β`, two clocks with the same phase coincide exactly at equal
times. -/
theorem clock_eq_iff_of_lt {δ δ' : CycData I d} (h : δ.fwd = true) (h' : δ'.fwd = true)
    (hph : δ.phase = δ'.phase) {L : ℝ≥0} (hL : (L : ℝ) < β) {r r' : ℝ≥0} (hr : r ≤ L)
    (hr' : r' ≤ L) : δ.clock β r = δ'.clock β r' ↔ r = r' := by
  have hβ : 0 < β := Fact.out
  rw [clock_eq_iff_int h h']
  constructor
  · rintro ⟨k, hk⟩
    have hr1 : (r : ℝ) ≤ L := by exact_mod_cast hr
    have hr2 : (r' : ℝ) ≤ L := by exact_mod_cast hr'
    have h0 : (r' : ℝ) - r = 0 := by
      refine int_mul_eq_zero_of_abs_lt hβ ?_ k ?_
      · rw [abs_lt]; constructor <;> nlinarith [NNReal.coe_nonneg r, NNReal.coe_nonneg r']
      · rw [← hph] at hk; linarith
    exact_mod_cast (sub_eq_zero.1 h0).symm
  · rintro rfl
    exact ⟨0, by rw [hph]; simp⟩

/-- Clocks of walks started in disjoint windows (modulo `β`) never coincide. -/
theorem clock_ne_of_disjoint {δ δ' : CycData I d} (h : δ.fwd = true) (h' : δ'.fwd = true)
    {L : ℝ≥0} (h1 : δ.phase + L < δ'.phase) (h2 : δ'.phase + L < δ.phase + β) {r r' : ℝ≥0}
    (hr : r ≤ L) (hr' : r' ≤ L) : δ.clock β r ≠ δ'.clock β r' := by
  have hβ : 0 < β := Fact.out
  rw [Ne, clock_eq_iff_int h h']
  rintro ⟨k, hk⟩
  have hr1 : (r : ℝ) ≤ L := by exact_mod_cast hr
  have hr2 : (r' : ℝ) ≤ L := by exact_mod_cast hr'
  have hpos : 0 < (k : ℝ) * β := by
    rw [← hk]; nlinarith [NNReal.coe_nonneg r, NNReal.coe_nonneg r']
  have hlt : (k : ℝ) * β < β := by
    rw [← hk]; nlinarith [NNReal.coe_nonneg r, NNReal.coe_nonneg r']
  have hk1 : (0 : ℝ) < k := by
    by_contra hh; push Not at hh; nlinarith
  have hk2 : (k : ℝ) < 1 := by
    by_contra hh; push Not at hh; nlinarith
  have : 0 < k := by exact_mod_cast hk1
  have : k < 1 := by exact_mod_cast hk2
  omega

end ElboimSly.Paper

end
