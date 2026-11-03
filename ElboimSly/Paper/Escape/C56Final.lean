/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Small
public import ElboimSly.Paper.Escape.C56Chain
public import ElboimSly.Paper.Escape.Gamma
public import Mathlib

/-!
# ES22 Claim 5.6: the arithmetic of the final bound

ES22 Claim 5.6, "Conclusion", properties of γ (c).
-/

@[expose] public section

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper ElboimSly.SRW ElboimSly.Brownian

/-- `(c0/2)(c1/2) ≥ k0 β^{-D}` for `τ ∈ [√β, 4√β]`. -/
theorem product_lower (d : ℕ) {β τ : ℝ} (hβ : 1 ≤ β) (hτ1 : Real.sqrt β ≤ τ)
    (hτ2 : τ ≤ 4 * Real.sqrt β) :
    escK0 d * β ^ (-escD d) ≤
      cBox ^ (201 * d) / (2 * Real.sqrt τ) ^ (201 * d * CBox) / 2 *
        (cBox ^ d / (3 * Real.sqrt τ) ^ (d * CBox) / 2) := by
  have hβ0 : 0 < β := by linarith
  have hsb : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ0
  have hτ0 : 0 < τ := lt_of_lt_of_le hsb hτ1
  set q := Real.sqrt (Real.sqrt β) with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 hsb
  have hq2 : q ^ 2 = Real.sqrt β := Real.sq_sqrt hsb.le
  have hq4 : q ^ 4 = β := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, hq2, Real.sq_sqrt hβ0.le]
  have hτq : Real.sqrt τ ≤ 2 * q := by
    calc Real.sqrt τ ≤ Real.sqrt (4 * Real.sqrt β) := Real.sqrt_le_sqrt hτ2
      _ = 2 * q := by
        rw [Real.sqrt_mul (by norm_num)]
        have : Real.sqrt 4 = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        rw [this]
  have hst : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
  have hc := cBox_pos
  set C := CBox with hC
  have hA : (2 * Real.sqrt τ) ^ (201 * d * C) ≤ (4 * q) ^ (201 * d * C) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hB : (3 * Real.sqrt τ) ^ (d * C) ≤ (6 * q) ^ (d * C) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have h1 : cBox ^ (201 * d) / (4 * q) ^ (201 * d * C) ≤
      cBox ^ (201 * d) / (2 * Real.sqrt τ) ^ (201 * d * C) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hA
  have h2 : cBox ^ d / (6 * q) ^ (d * C) ≤ cBox ^ d / (3 * Real.sqrt τ) ^ (d * C) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hB
  have h3 : cBox ^ (201 * d) / (4 * q) ^ (201 * d * C) / 2 *
        (cBox ^ d / (6 * q) ^ (d * C) / 2) ≤
      cBox ^ (201 * d) / (2 * Real.sqrt τ) ^ (201 * d * C) / 2 *
        (cBox ^ d / (3 * Real.sqrt τ) ^ (d * C) / 2) := by
    gcongr
  refine le_trans ?_ h3
  -- compute
  have hD : β ^ (-escD d) = ((q ^ (202 * d * C)))⁻¹ := by
    rw [Real.rpow_neg hβ0.le, ← hq4]
    congr 1
    rw [← Real.rpow_natCast q 4, ← Real.rpow_mul hq0.le, ← Real.rpow_natCast q (202 * d * C)]
    congr 1
    unfold escD
    push_cast
    ring
  rw [hD]
  unfold escK0
  have e1 : (4 * q) ^ (201 * d * C) = 4 ^ (201 * d * C) * q ^ (201 * d * C) := mul_pow _ _ _
  have e2 : (6 * q) ^ (d * C) = 6 ^ (d * C) * q ^ (d * C) := mul_pow _ _ _
  have e3 : q ^ (202 * d * C) = q ^ (201 * d * C) * q ^ (d * C) := by ring
  have e4 : cBox ^ (202 * d) = cBox ^ (201 * d) * cBox ^ d := by ring
  rw [e1, e2, e3, e4]
  have hq1 : 0 < q ^ (201 * d * C) := by positivity
  have hq2' : 0 < q ^ (d * C) := by positivity
  have h4 : (0 : ℝ) < 4 ^ (201 * d * C) := by positivity
  have h6 : (0 : ℝ) < 6 ^ (d * C) := by positivity
  have hcc : (0 : ℝ) < cBox ^ (201 * d) := by positivity
  have hcd : (0 : ℝ) < cBox ^ d := by positivity
  generalize cBox ^ (201 * d) = a at *
  generalize cBox ^ d = b at *
  generalize (4 : ℝ) ^ (201 * d * C) = A at *
  generalize (6 : ℝ) ^ (d * C) = B at *
  generalize q ^ (201 * d * C) = X at *
  generalize q ^ (d * C) = Y at *
  apply le_of_eq
  field_simp
  norm_num

end ElboimSly.Paper.Escape

end
