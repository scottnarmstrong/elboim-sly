/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib

/-!
# Parameters of the self-intersection claim

ES22 Claim 9.4, "Parameters" and the thresholds (L1)-(L5).

For `ζ ∈ (0, 1/100]` and `t ≥ 1`: `r = t^{ζ/2}`, `R = r^{1+ζ}`, `ρ = r^{1/50}`, `K = r^{2-2ζ}`,
`M = r^{2+3ζ}`, `J = ⌊t^{1-ζ}⌋`, `m_* = t^{1-1.1ζ}`. The structure `SiGood ζ t` collects the
inequalities (L1)-(L5), which hold for all large `t`. This file derives the numerical consequences
used in the assembly.
-/

@[expose] public section

namespace ElboimSly.Brownian

/-- `r = t^{ζ/2}`. -/
noncomputable def siR (ζ t : ℝ) : ℝ := t ^ (ζ / 2)

/-- `K = r^{2-2ζ}`. -/
noncomputable def siK (ζ t : ℝ) : ℝ := siR ζ t ^ (2 - 2 * ζ)

/-- `R = r^{1+ζ}`. -/
noncomputable def siBig (ζ t : ℝ) : ℝ := siR ζ t ^ (1 + ζ)

/-- `ρ = r^{1/50}`. -/
noncomputable def siRho (ζ t : ℝ) : ℝ := siR ζ t ^ ((1 : ℝ) / 50)

/-- `M = r^{2+3ζ}`. -/
noncomputable def siM (ζ t : ℝ) : ℝ := siR ζ t ^ (2 + 3 * ζ)

/-- `J = ⌊t^{1-ζ}⌋`. -/
noncomputable def siJ (ζ t : ℝ) : ℕ := ⌊t ^ (1 - ζ)⌋₊

/-- `m_* = t^{1-1.1ζ}`. -/
noncomputable def siMstar (ζ t : ℝ) : ℝ := t ^ (1 - 11 / 10 * ζ)

/-- The bound `p` of Step 2 for one block. -/
noncomputable def siP (ζ t : ℝ) : ℝ :=
  siR ζ t ^ 2 * ((Real.pi * siK ζ t) ^ (-(5 : ℝ) / 2) * (siM ζ t * (6 * siRho ζ t) ^ 5) +
    10 * Real.exp (-siBig ζ t ^ 2 / (8 * siR ζ t ^ 2))) +
    20 * (⌈siR ζ t ^ 2⌉₊ : ℝ) * Real.exp (-siRho ζ t ^ 2 / 16)

/-- The thresholds (L1)-(L5) of the written proof. -/
structure SiGood (ζ t : ℝ) : Prop where
  L1 : 2 ≤ siK ζ t
  L2 : 2 + 4 * siRho ζ t ≤ siBig ζ t
  L3 : siP ζ t ≤ siR ζ t ^ (-(1 : ℝ) / 2)
  L4 : 4 ≤ t ^ (3 / 20 * ζ)
  L5 : 4 ≤ t ^ (ζ ^ 2 - ζ ^ 3)

section Facts

variable {ζ t : ℝ}

lemma siR_one_le (hζ : 0 < ζ) (ht : 1 ≤ t) : 1 ≤ siR ζ t :=
  Real.one_le_rpow ht (by linarith)

lemma siR_pos (hζ : 0 < ζ) (ht : 1 ≤ t) : 0 < siR ζ t := lt_of_lt_of_le one_pos (siR_one_le hζ ht)

lemma siR_sq (ht : 1 ≤ t) : siR ζ t ^ 2 = t ^ ζ := by
  unfold siR
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  congr 1; push_cast; ring

lemma siRho_one_le (hζ : 0 < ζ) (ht : 1 ≤ t) : 1 ≤ siRho ζ t :=
  Real.one_le_rpow (siR_one_le hζ ht) (by norm_num)

lemma siK_eq (ht : 1 ≤ t) : siK ζ t = t ^ (ζ * (1 - ζ)) := by
  unfold siK siR
  rw [← Real.rpow_mul (by linarith)]
  congr 1; ring

lemma siK_nonneg (hζ : 0 < ζ) (ht : 1 ≤ t) : 0 ≤ siK ζ t :=
  Real.rpow_nonneg (siR_pos hζ ht).le _

lemma siM_nonneg (hζ : 0 < ζ) (ht : 1 ≤ t) : 0 ≤ siM ζ t :=
  Real.rpow_nonneg (siR_pos hζ ht).le _

lemma siJ_le (ht : 1 ≤ t) : (siJ ζ t : ℝ) ≤ t ^ (1 - ζ) :=
  Nat.floor_le (Real.rpow_nonneg (by linarith) _)

lemma lt_siJ_add_one (ζ t : ℝ) : t ^ (1 - ζ) < (siJ ζ t : ℝ) + 1 := Nat.lt_floor_add_one _

lemma rpow_mono_exp {t a b : ℝ} (ht : 1 ≤ t) (h : a ≤ b) : t ^ a ≤ t ^ b :=
  Real.rpow_le_rpow_of_exponent_le ht h

/-- `J K ≤ t^{1-ζ²}`. -/
lemma siJ_mul_siK_le (ht : 1 ≤ t) :
    (siJ ζ t : ℝ) * siK ζ t ≤ t ^ (1 - ζ ^ 2) := by
  rw [siK_eq ht]
  calc (siJ ζ t : ℝ) * t ^ (ζ * (1 - ζ)) ≤ t ^ (1 - ζ) * t ^ (ζ * (1 - ζ)) :=
        mul_le_mul_of_nonneg_right (siJ_le ht) (Real.rpow_nonneg (by linarith) _)
    _ = t ^ (1 - ζ ^ 2) := by
        rw [← Real.rpow_add (by linarith)]
        congr 1; ring

/-- The three error terms are each at most a quarter of `t^{1-ζ³}`. -/
lemma err_le (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 100) (ht : 1 ≤ t) (h5 : 4 ≤ t ^ (ζ ^ 2 - ζ ^ 3)) :
    t ^ (1 - ζ ^ 2) + t ^ (1 - 11 / 10 * ζ + ζ) + t ^ ζ ≤ 3 / 4 * t ^ (1 - ζ ^ 3) := by
  have hq : t ^ (1 - ζ ^ 2) ≤ 1 / 4 * t ^ (1 - ζ ^ 3) := by
    have : t ^ (1 - ζ ^ 3) = t ^ (1 - ζ ^ 2) * t ^ (ζ ^ 2 - ζ ^ 3) := by
      rw [← Real.rpow_add (by linarith)]; congr 1; ring
    rw [this]
    have h0 : 0 ≤ t ^ (1 - ζ ^ 2) := Real.rpow_nonneg (by linarith) _
    nlinarith
  have h2 : t ^ (1 - 11 / 10 * ζ + ζ) ≤ t ^ (1 - ζ ^ 2) :=
    rpow_mono_exp ht (by nlinarith)
  have h3 : t ^ ζ ≤ t ^ (1 - ζ ^ 2) := rpow_mono_exp ht (by nlinarith)
  linarith

/-- `(e - 1) · r^{-1/2} · J ≤ m_*/2`. -/
lemma pJ_le (hζ : 0 < ζ) (ht : 1 ≤ t) (hζ1 : ζ ≤ 1 / 100) (h4 : 4 ≤ t ^ (3 / 20 * ζ)) :
    (Real.exp 1 - 1) * siR ζ t ^ (-(1 : ℝ) / 2) * (siJ ζ t : ℝ) ≤ siMstar ζ t / 2 := by
  have he : Real.exp 1 - 1 ≤ 2 := by linarith [Real.exp_one_lt_d9]
  have hr : siR ζ t ^ (-(1 : ℝ) / 2) = t ^ (-(ζ / 4)) := by
    unfold siR
    rw [← Real.rpow_mul (by linarith)]
    congr 1; ring
  have hJ := siJ_le (ζ := ζ) ht
  have hpJ : siR ζ t ^ (-(1 : ℝ) / 2) * (siJ ζ t : ℝ) ≤ t ^ (1 - 5 / 4 * ζ) := by
    rw [hr]
    calc t ^ (-(ζ / 4)) * (siJ ζ t : ℝ) ≤ t ^ (-(ζ / 4)) * t ^ (1 - ζ) :=
          mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg (by linarith) _)
      _ = t ^ (1 - 5 / 4 * ζ) := by
          rw [← Real.rpow_add (by linarith)]; congr 1; ring
  have hm : siMstar ζ t = t ^ (1 - 5 / 4 * ζ) * t ^ (3 / 20 * ζ) := by
    unfold siMstar
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  have h0 : 0 ≤ t ^ (1 - 5 / 4 * ζ) := Real.rpow_nonneg (by linarith) _
  have hnn : 0 ≤ siR ζ t ^ (-(1 : ℝ) / 2) * (siJ ζ t : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (siR_pos hζ ht).le _) (Nat.cast_nonneg _)
  rw [mul_assoc, hm]
  nlinarith

end Facts

end ElboimSly.Brownian
