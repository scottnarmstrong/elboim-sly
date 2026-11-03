/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Param
public import ElboimSly.Paper.Escape.C56Det3
public import ElboimSly.Paper.Escape.C56Meas
public import Mathlib

/-!
# Consequences of `G_i`

ES22 Claim 5.6.  On `G_i`: `ζ_0 < β`; `W_v(s) ≠ v` for `s ∈ [β, ζ_i]`; the time `ζ_i` is
relaxed with respect to `W_v|[ζ_{i-1}, ·]`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper ElboimSly.Brownian ElboimSly.Cyclic

variable {k : ℕ}

theorem es56B_zero_lt {β t : ℝ} (hβ : (2 : ℝ) ^ 40 ≤ β) (ht : Real.sqrt β ≤ t) :
    es56B t (escPhaseM β t) 0 < β := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hsb : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ0
  have h4 := lt_four_pow_m_succ hβ0 ht
  have hs20 : (2 : ℝ) ^ 20 ≤ Real.sqrt β := by
    apply Real.le_sqrt_of_sq_le
    calc ((2 : ℝ) ^ 20) ^ 2 = 2 ^ 40 := by rw [← pow_mul]
      _ ≤ β := hβ
  have hsq : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ0.le
  set m := escPhaseM β t
  unfold es56B
  rw [ite_eq_left (Nat.zero_le _), Nat.sub_zero]
  have hpm : (0 : ℝ) < 4 ^ m := by positivity
  rw [pow_succ] at h4
  have : t < 4 * Real.sqrt β * 4 ^ m := by nlinarith
  have h5 : t / 4 ^ m < 4 * Real.sqrt β := by rw [div_lt_iff₀ hpm]; linarith
  have e : 3 / 5 * t / 4 ^ m = 3 / 5 * (t / 4 ^ m) := by ring
  rw [e]
  nlinarith

/-- Right-constancy of `y` from the `cpathReal`-form. -/
theorem escYv_hrc {β : ℝ} [Fact (0 < β)] {Ω : Type} [MeasurableSpace Ω]
    (N : Ω → Measure (CycS ℕ (k + 2) β)) (v : Fin (k + 2) → ℤ) (ω : Ω) :
    ∀ r, 0 ≤ r → ∀ᶠ u in 𝓝[≥] r, escYv N v ω u = escYv N v ω r := by
  intro r hr
  have h := cpathReal_hrc (escCPath N ω) (le_refl (0 : ℝ)) r hr
  exact h.mono fun u hu => by simp only [escYv, escY_eq_cpathReal, hu]

theorem EscG_ne_v {j : ℕ} {u v z : Fin (k + 2) → ℤ} (hgeom : EscGeom j u v z) {β t : ℝ}
    (hβ : (2 : ℝ) ^ 40 ≤ β) (hβj : β < 4 ^ j) (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (ht2 : t ≤ 4 ^ j)
    (W : ℝ → Fin (k + 2) → ℤ) {i : ℕ} (him : i ≤ 2 * escPhaseM β t)
    (hG : EscG β j u v z t W i) {s : ℝ} (hs : β ≤ s)
    (hsi : s ≤ escZeta β W t (escPhaseM β t) i) : W s ≠ v := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hsβ : Real.sqrt β ≤ t := by
    have h1 : Real.sqrt β ≤ β / 4 := by
      have h2 : (2 : ℝ) ^ 20 ≤ Real.sqrt β := by
        apply Real.le_sqrt_of_sq_le
        calc ((2 : ℝ) ^ 20) ^ 2 = 2 ^ 40 := by rw [← pow_mul]
          _ ≤ β := hβ
      have h3 : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ0.le
      nlinarith
    have h4 : β / 4 ≤ t := by
      have : (4 : ℝ) ^ j = 4 * 4 ^ (j - 1) := by
        have hj := hgeom.hj
        obtain ⟨i0, hi0⟩ : ∃ i0, j = i0 + 1 := ⟨j - 1, by omega⟩
        rw [hi0]; simp [pow_succ]; ring
      linarith
    linarith
  set m := escPhaseM β t with hm
  have hb0 := es56B_zero_lt hβ hsβ
  rcases phase_decomp (fun n => escZeta β W t m n) hsi with h0 | ⟨i'', hi1, hile, hlt, hle⟩
  · have := hG.1.1
    exfalso
    have hz : escZeta β W t m 0 < es56B t m 0 := this
    linarith
  · have hBi := hG.2 i'' hi1 hile
    have hw : ‖escCast (W s) - escCurve j u v z t s‖ ≤ escR t m i'' := hBi.2.1 s hlt.le hle
    have hz1 : escPhaseA t m (i'' - 1) ≤ s :=
      le_trans (escZeta_mem β W ht0.le m (i'' - 1)).1 hlt.le
    have hz2 : s ≤ es56B t m i'' := le_trans hle (escZeta_mem β W ht0.le m i'').2
    have hfar := curve_far_from_v hgeom ht2 ht0 hi1 (by omega) hz1 hz2
    have hR := escR_pos ht0 m i''
    intro hWv
    rw [hWv, norm_sub_rev] at hw
    linarith

/-- On `G_i`, the time `ζ_i` is relaxed with respect to `W_v|[ζ_{i-1}, ·]`. -/
theorem EscG_relaxed {β t : ℝ} (ht : 0 ≤ t) (W : ℝ → Fin (k + 2) → ℤ)
    (hrc : ∀ r, 0 ≤ r → ∀ᶠ u in 𝓝[≥] r, W u = W r) {j : ℕ} {u v z : Fin (k + 2) → ℤ} {i : ℕ}
    (hG : EscG β j u v z t W i) :
    IsRelaxedTimeWrt β W (escZetaPrev β W t (escPhaseM β t) i) (escZeta β W t (escPhaseM β t) i) := by
  set m := escPhaseM β t with hm
  cases i with
  | zero =>
    have hlt : escZeta β W t m 0 < es56B t m 0 := hG.1.1
    have e : escZeta β W t m 0 = escZetaStep β W (escPhaseA t m 0) (es56B t m 0) 0 := rfl
    rw [e] at hlt ⊢
    have := (escZetaStep_relaxed (β := β) (y := W) (lo := escPhaseA t m 0) (hi := es56B t m 0)
      (prev := 0) (fun r hr => hrc r hr) hlt).1
    simpa [escZetaPrev] using this
  | succ i0 =>
    have hBi := hG.2 (i0 + 1) (by omega) le_rfl
    have hlt : escZeta β W t m (i0 + 1) < es56B t m (i0 + 1) := hBi.1
    have e : escZeta β W t m (i0 + 1) = escZetaStep β W (escPhaseA t m (i0 + 1))
        (es56B t m (i0 + 1)) (escZeta β W t m i0) := rfl
    have hprev0 : 0 ≤ escZeta β W t m i0 := escY_zeta_nonneg β W ht m i0
    rw [e] at hlt ⊢
    have := (escZetaStep_relaxed (β := β) (y := W) (lo := escPhaseA t m (i0 + 1))
      (hi := es56B t m (i0 + 1)) (prev := escZeta β W t m i0)
      (fun r hr => hrc r (hprev0.trans hr)) hlt).1
    simpa [escZetaPrev] using this

end ElboimSly.Paper.Escape

end
