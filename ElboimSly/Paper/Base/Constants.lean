/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.ContactMain
public import ElboimSly.Paper.Base.Threshold
public import ElboimSly.Frozen.Defs.IndScale
public import ElboimSly.Frozen.Defs.IndDelta
public import ElboimSly.Foundations.SRW.LatticeSum
public import ElboimSly.Foundations.SRW.Lemma82B
public import ElboimSly.Foundations.SRW.Lemma82C
public import ElboimSly.Foundations.SRW.Lemma82E2
public import ElboimSly.Foundations.Brownian.Occupation
public import ElboimSly.Foundations.Brownian.SelfIntersection
public import ElboimSly.Foundations.StrongApprox.BaseCoupling
public import Mathlib

/-!
# Constants and thresholds of the base

Constants and thresholds of the base (ES22 §8).

Fix `d ≥ 5`.  Put `ζ₈ = δ/2 = 1/(6000 d²)` and `T_n = 2 t'_n`.

* `es8Zeta`, `es8T`; `es8CEsc`, `es8C1` (in `ContactProbB`): `c_esc`, `c₁ = e^{-4d} c_esc`.
* `es8CA = 4d (1 + C_lat(1/6, d))`; `es8Cocc = c_occ(d)`; `es8C94 = C_{9.4}(ζ₈)`.
* `es8K n = ⌊1.9ⁿ/(4n⁵)⌋` (the `k_n`) and `es8Eps d n` (the `ε(n)`).
* Thresholds on `n`: `es8n1` (of ES22 (8.3): base coupling with precision n^10), `lem82nC`, `lem82n2` (of
  SRW content of Lemma 8.2), `14980` (`es8_threshold`), `es8nK` (with `es8nK_spec`, in `ConstantsN`);
  `es8n0` is their maximum with `20, 2d, 77`.
* Thresholds on `β`: `es8BetaCond` (conditions (B1)-(B4)) and `es8Beta0` (in `ConstantsBeta`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Brownian

/-- Constants and thresholds of the base: `ζ₈ = δ / 2 = 1/(6000 d²)`. -/
noncomputable def es8Zeta (d : ℕ) : ℝ := indDelta d / 2

theorem es8Zeta_eq (d : ℕ) : es8Zeta d = 1 / (6000 * (d : ℝ) ^ 2) := by
  unfold es8Zeta indDelta
  rcases eq_or_ne (d : ℝ) 0 with h | h
  · simp [h]
  · field_simp; ring

/-- Constants and thresholds of the base: `T_n = 2 t'_n`, with `t'_n = t_n / n⁴` and `t_n = 4ⁿ t₀`. -/
noncomputable def es8T (t₀ : ℝ) (n : ℕ) : ℝ := 2 * (indScale t₀ n / (n : ℝ) ^ 4)

/-- Constants and thresholds of the base: `C_𝒜(d) = 4d (1 + C_lat(1/6, d))`. -/
noncomputable def es8CA (d : ℕ) : ℝ := 4 * d * (1 + latConst (1 / 6) d)

/-- Constants and thresholds of the base: `c_occ(d)`, the constant of ES22 Lemma 9.3: occupation of a cube at integer times. -/
noncomputable def es8Cocc (d : ℕ) : ℝ := cocc d

open Classical in
/-- Constants and thresholds of the base: `C_{9.4} = C_{9.4}(ζ₈)`, the constant of
ES22 Claim 9.4. -/
noncomputable def es8C94 (d : ℕ) : ℝ :=
  max 0 (if h : 0 < es8Zeta d ∧ es8Zeta d ≤ 1 / 100 then
    Classical.choose (selfIntersection.{0} h.1 h.2) else 0)

theorem es8C94_nonneg (d : ℕ) : 0 ≤ es8C94 d := le_max_left _ _

theorem es8Zeta_pos {d : ℕ} (hd : 1 ≤ d) : 0 < es8Zeta d := by
  rw [es8Zeta_eq]; positivity

theorem es8Zeta_le {d : ℕ} (hd : 1 ≤ d) : es8Zeta d ≤ 1 / 100 := by
  rw [es8Zeta_eq]
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The defining property of `C_{9.4}`. -/
theorem es8C94_spec {d : ℕ} (hd : 1 ≤ d) :
    ∀ {d' : ℕ}, 5 ≤ d' → ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
      [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d' → ℝ)}, IsStandardBrownianMotion d' B P →
      ∀ t : ℝ, 1 ≤ t →
      (Measurable fun ω => nnLebesgue (sepSet B 1 (Real.toNNReal (t ^ es8Zeta d))
        (Real.toNNReal t) ω)) ∧
      P {ω | ENNReal.ofReal (t ^ (1 - es8Zeta d ^ 3)) ≤
        nnLebesgue (sepSet B 1 (Real.toNNReal (t ^ es8Zeta d)) (Real.toNNReal t) ω)} ≤
      ENNReal.ofReal (es8C94 d * Real.exp (-t ^ (es8Zeta d ^ 2 / 4))) := by
  have h : 0 < es8Zeta d ∧ es8Zeta d ≤ 1 / 100 := ⟨es8Zeta_pos hd, es8Zeta_le hd⟩
  intro d' hd' Ω _ P _ B hB t ht
  have key := Classical.choose_spec (selfIntersection.{0} h.1 h.2) hd' hB t ht
  refine ⟨key.1, key.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  unfold es8C94
  rw [dite_eq_left h]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- Constants and thresholds of the base: `k_n = ⌊1.9ⁿ / (4 n⁵)⌋`. -/
noncomputable def es8K (n : ℕ) : ℕ := ⌊(1.9 : ℝ) ^ n / (4 * (n : ℝ) ^ 5)⌋₊

/-- Constants and thresholds of the base: `ε(n) = (1-c₁)^{k_n} + 2(2·4^{n+1}/n⁴ + 1) e^{4d(e-1) - n⁵}
+ e^{-n⁴} + 2^{-n⁴}`. -/
noncomputable def es8Eps (d n : ℕ) : ℝ :=
  (1 - es8C1 d) ^ es8K n +
    2 * (2 * 4 ^ (n + 1) / (n : ℝ) ^ 4 + 1) *
      Real.exp (4 * d * (Real.exp 1 - 1) - (n : ℝ) ^ 5) +
    Real.exp (-(n : ℝ) ^ 4) + ((2 : ℝ) ^ (n ^ 4))⁻¹

/-- Constants and thresholds of the base, (n2): the threshold `n₁(d)` of ES22 (8.3): base coupling with precision n^10. -/
noncomputable def es8n1 (d : ℕ) : ℕ :=
  open Classical in
  if h : 1 ≤ d then Classical.choose (StrongApprox.sa_base_coupling d h) else 0

end ElboimSly.Paper
