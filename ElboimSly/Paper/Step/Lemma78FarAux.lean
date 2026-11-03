/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.TauHat
public import ElboimSly.Paper.Heavy.Claim69Aux
public import ElboimSly.Paper.Heavy.Eight1
public import ElboimSly.Paper.Heavy.TwoGap

/-!
# Lemma 7.8, far lemma: auxiliary facts

Components of `τ̂ > T`, monotonicity of `latDist` in the set, and attainment of `latDist` up to 1.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper

variable {d n : ℕ} {β t₀ T : ℝ} {w : ℝ → Fin d → ℤ}

/-- `τ̂(w) > T` gives `T < T(w), τ_fast, τ_jump, τ', τ_bad`. -/
theorem tauHat_lt_parts (h : ENNReal.ofReal T < heavyTauHat d β t₀ n w) :
    ENNReal.ofReal T < cycClosingTime β w ∧ ENNReal.ofReal T < pathTfastCube w n ∧
      ENNReal.ofReal T < pathTjumpCube w n ∧ ENNReal.ofReal T < heavyTauPrime d t₀ n w ∧
      ENNReal.ofReal T < heavyTauBad d β t₀ n w := by
  simp only [heavyTauHat, heavyTauCheck, lt_min_iff] at h
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem exists_close_of_latDist_le {A : Set (Fin d → ℤ)} (hA : A.Nonempty) {u : Fin d → ℤ}
    {r : ℝ} (hr : 0 ≤ r) (h : latDist u A ≤ r) : ∃ a ∈ A, ‖u - a‖ < r + 1 := by
  obtain ⟨a, ha, hn⟩ := exists_le_of_latDist_le hA (u := u) (R := ⌈r⌉₊) (h.trans (Nat.le_ceil r))
  exact ⟨a, ha, lt_of_le_of_lt hn (Nat.ceil_lt_add_one hr)⟩

end ElboimSly.Paper.Step

end
