/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.NoFastMain

/-!
# Auxiliary facts for Claim 6.9

* `exists_le_of_latDist_le`: `d(u, A) ≤ R` for an integer `R` is attained.
* `block_near`: `N(B, 2^k)` is covered by the `3^d` blocks `B + 2^k z`, `z ∈ {-1,0,1}^d`.
* `grid_exists`: a grid of cyclic integer times with spacing `t'_k - 1` covers `[a, a + D)` by
  intervals `[c, c + t'_k)`.
-/

@[expose] public section

open Set

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ}

theorem exists_le_of_latDist_le {A : Set (Fin d → ℤ)} (hA : A.Nonempty) {u : Fin d → ℤ} {R : ℕ}
    (h : latDist u A ≤ R) : ∃ a ∈ A, ‖u - a‖ ≤ R := by
  by_contra hcon
  push Not at hcon
  have : Nonempty A := hA.to_subtype
  have hge : ∀ a : A, (R : ℝ) + 1 ≤ ‖u - (a : Fin d → ℤ)‖ := by
    intro a
    have h1 : (R : ℝ) < ‖u - (a : Fin d → ℤ)‖ := hcon a a.2
    by_contra h2
    push Not at h2
    -- all coordinates have |·| ≤ R, so the norm is ≤ R
    have : ‖u - (a : Fin d → ℤ)‖ ≤ R := by
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro c
      have hc : (|(u - (a : Fin d → ℤ)) c| : ℝ) < R + 1 := by
        have := norm_le_pi_norm (u - (a : Fin d → ℤ)) c
        simp only [Int.norm_eq_abs] at this
        linarith
      have hc' : |(u - (a : Fin d → ℤ)) c| ≤ R := by
        have : |(u - (a : Fin d → ℤ)) c| < R + 1 := by exact_mod_cast hc
        omega
      simpa [Int.norm_eq_abs] using (by exact_mod_cast hc' : (|(u - (a : Fin d → ℤ)) c| : ℝ) ≤ R)
    linarith
  have : (R : ℝ) + 1 ≤ latDist u A := le_ciInf hge
  linarith

/-- The `3^d` blocks `B + 2^k z` cover `N(B, 2^k)`. -/
theorem block_near (k : ℕ) (ι : Fin d → ℤ) {v : Fin d → ℤ}
    (hv : ∃ b ∈ heavyBlock k ι, ‖v - b‖ ≤ (2 : ℝ) ^ k) :
    ∃ z ∈ Fintype.piFinset (fun _ : Fin d => ({-1, 0, 1} : Finset ℤ)),
      v ∈ heavyBlock k (ι + z) := by
  obtain ⟨b, hb, hvb⟩ := hv
  have hq : (0 : ℤ) < 2 ^ k := by positivity
  refine ⟨fun c => v c / 2 ^ k - ι c, ?_, fun c => by simp⟩
  rw [Fintype.mem_piFinset]
  intro c
  have h1 : |v c - b c| ≤ 2 ^ k := by
    have := norm_le_pi_norm (v - b) c
    simp only [Int.norm_eq_abs, Pi.sub_apply] at this
    push_cast at this
    have h2 : (|v c - b c| : ℝ) ≤ (2 : ℝ) ^ k := this.trans hvb
    exact_mod_cast h2
  have h2 := abs_le.1 h1
  have hlo : (b c - 2 ^ k) / 2 ^ k ≤ v c / 2 ^ k := Int.ediv_le_ediv hq (by linarith)
  have hhi : v c / 2 ^ k ≤ (b c + 2 ^ k) / 2 ^ k := Int.ediv_le_ediv hq (by linarith)
  have e1 : (b c - 2 ^ k) / 2 ^ k = b c / 2 ^ k - 1 := by
    have := Int.add_mul_ediv_right (b c) (-1) hq.ne'
    simpa [sub_eq_add_neg] using this
  have e2 : (b c + 2 ^ k) / 2 ^ k = b c / 2 ^ k + 1 := by
    have := Int.add_mul_ediv_right (b c) 1 hq.ne'
    simpa using this
  have e3 : b c / 2 ^ k = ι c := hb c
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- The grid of cyclic integer times `c_m = max (CI ∩ [0, a + m (t'_k - 1)])` covers `[a, a + D)`. -/
theorem grid_exists {β : ℝ} (hβ : 0 < β) {a tk D s : ℝ} (_ha : 0 ≤ a) (htk : 1 < tk)
    (has : a ≤ s) (hsD : s < a + D) :
    ∃ m : ℕ, (m : ℝ) ≤ D / (tk - 1) ∧
      cycFloor β (a + m * (tk - 1)) ≤ s ∧ s < cycFloor β (a + m * (tk - 1)) + tk := by
  have hp : 0 < tk - 1 := by linarith
  set m : ℕ := ⌊(s - a) / (tk - 1)⌋₊ with hm
  have hm0 : (0 : ℝ) ≤ (s - a) / (tk - 1) := div_nonneg (by linarith) hp.le
  have hm1 : (m : ℝ) ≤ (s - a) / (tk - 1) := Nat.floor_le hm0
  have hm2 : (s - a) / (tk - 1) < m + 1 := Nat.lt_floor_add_one _
  have h1 : (m : ℝ) * (tk - 1) ≤ s - a := by
    have := (le_div_iff₀ hp).1 hm1; linarith
  have h2 : s - a < (m + 1) * (tk - 1) := (div_lt_iff₀ hp).1 hm2
  refine ⟨m, ?_, ?_, ?_⟩
  · calc (m : ℝ) ≤ (s - a) / (tk - 1) := hm1
      _ ≤ D / (tk - 1) := by gcongr; linarith
  · have := cycFloor_le (β := β) (x := a + m * (tk - 1)) hβ
    linarith
  · have := lt_cycFloor_add_one (β := β) (x := a + m * (tk - 1)) hβ
    nlinarith

end ElboimSly.Paper
