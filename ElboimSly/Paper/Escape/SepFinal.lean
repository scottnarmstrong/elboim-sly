/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.SepPos
public import Mathlib

/-!
# Old history is far (old history is far)

Old history is far.  For `β ≥ β_56` (here `2^40 ≤ β < 4^j`), `2 ≤ i ≤ 2m`, on `G_{i-1}`: a
path `Y` on `[ζ_{i-1}, b_i]` with `‖Y(s) - f(s)‖ ≤ R_i` stays at distance `≥ 2` from `W_v(s')` for
`s' ∈ [0, ζ_{i-2}]`, `s - s' ≥ β`.

* `escZeta_mem`: `ζ_k ∈ [a_k, b_k]`.
* `escPhaseM_spec`: `2^m β^{1/4} ≤ √t`.
* `es5_sep`: the statement.
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly.Brownian

variable {k : ℕ}

lemma escA_le_B (t : ℝ) (ht : 0 ≤ t) (m i : ℕ) : escPhaseA t m i ≤ es56B t m i := by
  unfold escPhaseA es56B
  by_cases hi : i ≤ m
  · rw [ite_eq_left hi, ite_eq_left hi]
    have : (0 : ℝ) < 4 ^ (m - i) := by positivity
    rw [div_le_div_iff₀ (by positivity) this]
    nlinarith [mul_nonneg ht this.le]
  · rw [ite_eq_right hi, ite_eq_right hi]
    have : (0 : ℝ) < 4 ^ (i - m) := by positivity
    have e1 : t / (2 * 4 ^ (i - m)) = 5 / 10 * t / 4 ^ (i - m) := by field_simp; ring
    have e2 : 3 / 10 * t / 4 ^ (i - m) ≤ 5 / 10 * t / 4 ^ (i - m) :=
      div_le_div_of_nonneg_right (by linarith) this.le
    linarith

lemma escZetaStep_mem (β : ℝ) (y : ℝ → Fin (k + 2) → ℤ) {lo hi : ℝ} (prev : ℝ) (h : lo ≤ hi) :
    lo ≤ escZetaStep β y lo hi prev ∧ escZetaStep β y lo hi prev ≤ hi := by
  unfold escZetaStep
  by_cases hex : ∃ s ∈ relaxedSet β y prev, lo ≤ s ∧ s < hi
  · rw [ite_eq_left hex]
    obtain ⟨s, hs, hlo, hhi⟩ := hex
    have hne : (relaxedSet β y prev ∩ Set.Ici lo).Nonempty := ⟨s, hs, hlo⟩
    have hbdd : BddBelow (relaxedSet β y prev ∩ Set.Ici lo) := ⟨lo, fun x hx => hx.2⟩
    refine ⟨le_csInf hne fun x hx => hx.2, ?_⟩
    exact (csInf_le hbdd ⟨hs, hlo⟩).trans hhi.le
  · rw [ite_eq_right hex]; exact ⟨h, le_rfl⟩

lemma escZeta_mem (β : ℝ) (y : ℝ → Fin (k + 2) → ℤ) {t : ℝ} (ht : 0 ≤ t) (m i : ℕ) :
    escPhaseA t m i ≤ escZeta β y t m i ∧ escZeta β y t m i ≤ es56B t m i := by
  cases i with
  | zero => exact escZetaStep_mem β y 0 (escA_le_B t ht m 0)
  | succ i => exact escZetaStep_mem β y _ (escA_le_B t ht m (i + 1))

lemma escPhaseM_spec {β t : ℝ} (hβ : 0 < β) (ht : Real.sqrt β ≤ t) :
    (2 : ℝ) ^ escPhaseM β t * Real.sqrt (Real.sqrt β) ≤ Real.sqrt t := by
  have hsb : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hx : 1 ≤ t / Real.sqrt β := by rw [le_div_iff₀ hsb]; linarith
  have hlog : 0 ≤ Real.logb 4 (t / Real.sqrt β) := Real.logb_nonneg (by norm_num) hx
  have h1 : (escPhaseM β t : ℝ) ≤ Real.logb 4 (t / Real.sqrt β) := Nat.floor_le hlog
  have h2 : (4 : ℝ) ^ escPhaseM β t ≤ t / Real.sqrt β := by
    calc (4 : ℝ) ^ escPhaseM β t = (4 : ℝ) ^ (escPhaseM β t : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (4 : ℝ) ^ (Real.logb 4 (t / Real.sqrt β)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = t / Real.sqrt β := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  have h3 : (4 : ℝ) ^ escPhaseM β t * Real.sqrt β ≤ t := by
    rwa [le_div_iff₀ hsb] at h2
  apply Real.le_sqrt_of_sq_le
  have : ((2 : ℝ) ^ escPhaseM β t * Real.sqrt (Real.sqrt β)) ^ 2 =
      4 ^ escPhaseM β t * Real.sqrt β := by
    have h4 : ((2 : ℝ) ^ escPhaseM β t) ^ 2 = 4 ^ escPhaseM β t := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [mul_pow, Real.sq_sqrt hsb.le, h4]
  rw [this]; exact h3

/-- Phase decomposition of `[0, ζ_{i-2}]`. -/
lemma phase_decomp (ζ : ℕ → ℝ) {s' : ℝ} {n : ℕ} (h : s' ≤ ζ n) :
    s' ≤ ζ 0 ∨ ∃ i'', 1 ≤ i'' ∧ i'' ≤ n ∧ ζ (i'' - 1) < s' ∧ s' ≤ ζ i'' := by
  classical
  have hex : ∃ k, s' ≤ ζ k := ⟨n, h⟩
  have hk := Nat.find_spec hex
  have hle : Nat.find hex ≤ n := Nat.find_min' hex h
  by_cases h0 : Nat.find hex = 0
  · left; rw [h0] at hk; exact hk
  · right
    refine ⟨Nat.find hex, by omega, hle, ?_, hk⟩
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    exact not_le.1 this

/-- Old history is far. -/
theorem es5_sep {j : ℕ} {u v z : Fin (k + 2) → ℤ} (h : EscGeom j u v z) {β t : ℝ}
    (hβ : (2 : ℝ) ^ 40 ≤ β) (hβj : β < 4 ^ j) (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (ht2 : t ≤ 4 ^ j)
    (W : ℝ → Fin (k + 2) → ℤ) {i : ℕ} (hi2 : 2 ≤ i) (him : i ≤ 2 * escPhaseM β t)
    (hG : EscG β j u v z t W (i - 1)) (Y : ℝ → Fin (k + 2) → ℤ) {s s' : ℝ}
    (hs1 : escZeta β W t (escPhaseM β t) (i - 1) ≤ s) (hs2 : s ≤ es56B t (escPhaseM β t) i)
    (hs'0 : 0 ≤ s') (hs'1 : s' ≤ escZeta β W t (escPhaseM β t) (i - 2)) (hss : β ≤ s - s')
    (hY : ‖escCast (Y s) - escCurve j u v z t s‖ ≤ escR t (escPhaseM β t) i) :
    2 ≤ ‖escCast (Y s) - escCast (W s')‖ := by
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht1
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
        have hj := h.hj
        obtain ⟨i0, hi0⟩ : ∃ i0, j = i0 + 1 := ⟨j - 1, by omega⟩
        rw [hi0]; simp [pow_succ]; ring
      linarith
    linarith
  have hm := escPhaseM_spec hβ0 hsβ
  set m := escPhaseM β t with hmdef
  have hs1' : escPhaseA t m (i - 1) ≤ s :=
    le_trans (escZeta_mem β W ht.le m (i - 1)).1 hs1
  -- phase decomposition of s'
  rcases phase_decomp (fun n => escZeta β W t m n) hs'1 with h0 | ⟨i'', hi1, hile, hlt, hle⟩
  · exact sep_core_zero h hβ hβj ht2 ht (by omega) him hs1' hs2 (by linarith)
      hY ((hG.1.2.1 s' hs'0 h0).2)
  · have hBi := hG.2 i'' hi1 (by omega)
    have hw : ‖escCast (W s') - escCurve j u v z t s'‖ ≤ escR t m i'' := by
      have := hBi.2.1 s' hlt.le hle
      exact this
    have hz1 : escPhaseA t m (i'' - 1) ≤ s' :=
      le_trans (escZeta_mem β W ht.le m (i'' - 1)).1 hlt.le
    have hz2 : s' ≤ es56B t m i'' := le_trans hle (escZeta_mem β W ht.le m i'').2
    exact sep_core_pos h hβ hβj ht2 ht hm hi1 (by omega) him hs1' hs2 hz1 hz2 hss hY hw

end ElboimSly.Paper
