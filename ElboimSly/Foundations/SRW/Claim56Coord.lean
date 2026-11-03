/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Claim56Fv
public import ElboimSly.Foundations.SRW.Claim56B2m1
public import Mathlib

/-!
# Coordinatewise facts for Claim 5.6, event `𝓑_0`
-/

@[expose] public section

open Set
open scoped NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- The real side length of the box `B^-` in coordinate `i`. -/
noncomputable def claimL (j : ℕ) (i : Fin d) : ℝ := if i.val = 0 then (2 : ℝ) ^ j / 2 else (2 : ℝ) ^ j

theorem claimQ_eq (j : ℕ) (u : Fin d → ℤ) (i : Fin d) :
    claimQ j u i = (u i : ℝ) + claimL j i / 2 := by
  unfold claimQ claimL
  split_ifs <;> ring

theorem claimBox_coord {j : ℕ} (hj : 1 ≤ j) {u v : Fin d → ℤ} (hv : v ∈ claimBox u j) (i : Fin d) :
    (u i : ℝ) ≤ v i ∧ (v i : ℝ) ≤ u i + claimL j i - 1 := by
  have h := hv i
  rw [mem_Icc] at h
  have hsl := sideLen_cast (d := d) j hj i
  unfold claimL
  rw [← hsl]
  constructor
  · exact_mod_cast h.1
  · have : v i ≤ u i + (sideLen d j i : ℕ) - 1 := h.2
    exact_mod_cast this

theorem claimL_le {j : ℕ} (i : Fin d) : claimL j i ≤ (2 : ℝ) ^ j := by
  unfold claimL
  split_ifs
  · have : (0 : ℝ) < 2 ^ j := by positivity
    linarith
  · exact le_rfl

theorem claimL_ge {j : ℕ} (i : Fin d) : (2 : ℝ) ^ j / 2 ≤ claimL j i := by
  unfold claimL
  split_ifs
  · exact le_rfl
  · have : (0 : ℝ) < 2 ^ j := by positivity
    linarith

/-- `f_v(s)_i = v_i + λ (q_i - v_i)`. -/
theorem claimFv_eq (j : ℕ) (u : Fin d → ℤ) (t : ℝ) (v : Fin d → ℤ) (s : ℝ) (i : Fin d) :
    claimFv j u t v s i = v i + √(2 * s / t) * (claimQ j u i - v i) := by
  unfold claimFv; ring

end SRW
end ElboimSly
