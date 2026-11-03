/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.UpPath
public import ElboimSly.Foundations.SRW.EscapeMain
public import Mathlib

/-!
# The confined lower bound: constants and the small case

Confined point-to-point lower bound (constants and the case `L < 50000`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

/-- The constant `c_E` of escape from the boundary. -/
noncomputable def cE : ℝ := Real.exp (-2) / ((72 : ℕ).factorial * 1100)

/-- The constant `K = 5120^2`. -/
def boxK : ℕ := 5120 ^ 2

/-- The exponent `C_box = 512 + K` of confined point-to-point lower bound. -/
def CBox : ℕ := 512 + boxK

/-- The constant `c_box` of confined point-to-point lower bound. -/
noncomputable def cBox : ℝ :=
  min (cE ^ 2) (Real.exp (-(8 * 10 ^ 10)) * (1 / 16) ^ 50000 / (50000 : ℕ).factorial)

theorem cE_pos : 0 < cE := by unfold cE; positivity

theorem cBox_pos : 0 < cBox := by
  unfold cBox
  exact lt_min (pow_pos cE_pos 2) (by positivity)

theorem kernel1_ge_up (J : Set ℤ) {y z : ℤ} (hyz : y ≤ z) (hJ : Icc y z ⊆ J) (r : ℝ≥0) :
    po r (z - y).toNat * po r 0 ≤ kernel1 J r y z := by
  have hY := srwZ_isSRW 1
  have h := hY.prob_gamUp (z - y).toNat r
  refine h.trans ?_
  have hm : ∀ ω ∈ {ω | srwZ 1 ω ∈ gamUp (z - y).toNat r},
      ω ∈ {ω | srwZ 1 ω ∈ kerSet {v : Fin 1 → ℤ | v 0 ∈ J} r (fun _ => y) (fun _ => z)} := by
    intro ω hω
    obtain ⟨h1, h2⟩ := hω
    refine ⟨?_, fun s hs => ?_⟩
    · funext i
      rw [Subsingleton.elim i 0]
      have : srwZ 1 ω r 0 = ((z - y).toNat : ℤ) := h1
      simp only [Pi.add_apply, this]
      omega
    · obtain ⟨a, b⟩ := h2 s hs
      have b' : srwZ 1 ω s 0 ≤ z - y := by
        have : (((z - y).toNat : ℕ) : ℤ) = z - y := Int.toNat_of_nonneg (by omega)
        omega
      show y + srwZ 1 ω s 0 ∈ J
      exact hJ ⟨by omega, by omega⟩
  have := hY.isProbabilityMeasure
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hm)

theorem po_pair_lower {r : ℝ≥0} {k : ℕ} (hk : k ≤ 50000) (hr1 : (1 / 16 : ℝ) ≤ r)
    (hr2 : (r : ℝ) ≤ 4 * 10 ^ 10) :
    Real.exp (-(8 * 10 ^ 10)) * (1 / 16) ^ 50000 / (50000 : ℕ).factorial ≤
      po r k * po r 0 := by
  unfold po
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, mul_one]
  have hr0 : (0 : ℝ) < r := by linarith
  have e1 : Real.exp (-8 * 10 ^ 10 + 0) ≤ Real.exp (-(r : ℝ)) * Real.exp (-(r : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    norm_num; linarith
  have e1' : Real.exp (-(8 * 10 ^ 10)) ≤ Real.exp (-(r : ℝ)) * Real.exp (-(r : ℝ)) := by
    have : -8 * 10 ^ 10 + 0 = -(8 * 10 ^ 10 : ℝ) := by norm_num
    rwa [this] at e1
  have e2 : (1 / 16 : ℝ) ^ 50000 ≤ (r : ℝ) ^ k := by
    calc (1 / 16 : ℝ) ^ 50000 ≤ (1 / 16 : ℝ) ^ k :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ ≤ (r : ℝ) ^ k := by gcongr
  have e3 : ((k.factorial : ℕ) : ℝ) ≤ ((50000 : ℕ).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hk
  have hkf : (0 : ℝ) < k.factorial := by positivity
  have hF : (0 : ℝ) < (50000 : ℕ).factorial := by positivity
  calc Real.exp (-(8 * 10 ^ 10)) * (1 / 16) ^ 50000 / (50000 : ℕ).factorial
      ≤ (Real.exp (-(r : ℝ)) * Real.exp (-(r : ℝ))) * (r : ℝ) ^ k / k.factorial := by
        rw [div_le_div_iff₀ hF hkf]
        have := Real.exp_pos (-(r : ℝ))
        have h4 : 0 ≤ Real.exp (-(8 * 10 ^ 10)) * (1 / 16 : ℝ) ^ 50000 := by positivity
        calc Real.exp (-(8 * 10 ^ 10)) * (1 / 16) ^ 50000 * k.factorial
            ≤ Real.exp (-(8 * 10 ^ 10)) * (1 / 16) ^ 50000 * (50000 : ℕ).factorial := by gcongr
          _ ≤ (Real.exp (-(r : ℝ)) * Real.exp (-(r : ℝ))) * (r : ℝ) ^ k *
              (50000 : ℕ).factorial := by gcongr
    _ = Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / k.factorial * Real.exp (-(r : ℝ)) := by ring

end SRW
end ElboimSly
