/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# The curve of ES22 Claim 5.6

ES22 Claim 5.6: the tube step, uniform over scales, the curve `f` of ES22 §5 and its Lipschitz bounds.

`f(s) = v + √(2s/t)(q - v)` for `s ≤ t/2` and `f(s) = w + √(2(t-s)/t)(q - w)` for `s ≥ t/2`.
-/

@[expose] public section

namespace ElboimSly.Brownian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The curve `f` of ES22 §5. -/
noncomputable def es56F (t : ℝ) (v w q : E) (s : ℝ) : E :=
  if s ≤ t / 2 then v + Real.sqrt (2 * s / t) • (q - v)
  else w + Real.sqrt (2 * (t - s) / t) • (q - w)

lemma sqrt_sub_le {t a x y : ℝ} (ht : 0 < t) (ha : 0 < a) (hx : a ≤ x) (hy : a ≤ y) :
    |Real.sqrt (2 * x / t) - Real.sqrt (2 * y / t)| ≤ |x - y| / Real.sqrt (2 * a * t) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hxa : 0 < 2 * x / t := by positivity
  have hya : 0 < 2 * y / t := by positivity
  have hsx := Real.sqrt_pos.2 hxa
  have hsy := Real.sqrt_pos.2 hya
  have hsa : 0 < Real.sqrt (2 * a / t) := Real.sqrt_pos.2 (by positivity)
  have hmain : |Real.sqrt (2 * x / t) - Real.sqrt (2 * y / t)| ≤
      |2 * x / t - 2 * y / t| / (2 * Real.sqrt (2 * a / t)) := by
    have e : (Real.sqrt (2 * x / t) - Real.sqrt (2 * y / t)) *
        (Real.sqrt (2 * x / t) + Real.sqrt (2 * y / t)) = 2 * x / t - 2 * y / t := by
      have h1 := Real.sq_sqrt hxa.le
      have h2 := Real.sq_sqrt hya.le
      nlinarith
    have hlow : 2 * Real.sqrt (2 * a / t) ≤ Real.sqrt (2 * x / t) + Real.sqrt (2 * y / t) := by
      have h1 : Real.sqrt (2 * a / t) ≤ Real.sqrt (2 * x / t) :=
        Real.sqrt_le_sqrt (by gcongr)
      have h2 : Real.sqrt (2 * a / t) ≤ Real.sqrt (2 * y / t) :=
        Real.sqrt_le_sqrt (by gcongr)
      linarith
    rw [le_div_iff₀ (by positivity), ← e, abs_mul]
    rw [abs_of_pos (by positivity : 0 < Real.sqrt (2 * x / t) + Real.sqrt (2 * y / t))]
    exact mul_le_mul_of_nonneg_left hlow (abs_nonneg _)
  refine hmain.trans (le_of_eq ?_)
  have e1 : 2 * x / t - 2 * y / t = 2 * (x - y) / t := by ring
  have e2 : Real.sqrt (2 * a * t) = t * Real.sqrt (2 * a / t) := by
    rw [show 2 * a * t = t ^ 2 * (2 * a / t) by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq ht.le]
  rw [e1, e2, abs_div, abs_of_pos ht, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  field_simp

lemma es56F_of_le {t : ℝ} {v w q : E} {s : ℝ} (hs : s ≤ t / 2) :
    es56F t v w q s = v + Real.sqrt (2 * s / t) • (q - v) := by
  simp [es56F, hs]

lemma es56F_of_ge {t : ℝ} (ht : 0 < t) {v w q : E} {s : ℝ} (hs : t / 2 ≤ s) :
    es56F t v w q s = w + Real.sqrt (2 * (t - s) / t) • (q - w) := by
  by_cases h : s ≤ t / 2
  · have hs' : s = t / 2 := le_antisymm h hs
    subst hs'
    rw [es56F_of_le le_rfl]
    have h1 : 2 * (t / 2) / t = 1 := by field_simp
    have h2 : 2 * (t - t / 2) / t = 1 := by field_simp; ring
    rw [h1, h2]; simp
  · simp [es56F, h]

/-- Lipschitz bound of the first half of the curve. -/
lemma es56_lip_first {t a h2 ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ) (_hh2 : 0 ≤ h2) (hh2t : h2 ^ 2 ≤ t)
    (ha : ρ ^ 2 ≤ 2 * a) {v w q : E} (hq : ‖q - v‖ ≤ h2) {s s' : ℝ} (hs : a ≤ s) (hs' : a ≤ s')
    (hs1 : s ≤ t / 2) (hs1' : s' ≤ t / 2) :
    ‖es56F t v w q s - es56F t v w q s'‖ ≤ 1 / ρ * |s - s'| := by
  have ha0 : 0 < a := by nlinarith [sq_pos_of_pos hρ]
  rw [es56F_of_le hs1, es56F_of_le hs1']
  have e : v + Real.sqrt (2 * s / t) • (q - v) - (v + Real.sqrt (2 * s' / t) • (q - v)) =
      (Real.sqrt (2 * s / t) - Real.sqrt (2 * s' / t)) • (q - v) := by
    rw [sub_smul]; abel
  rw [e, norm_smul, Real.norm_eq_abs]
  have h1 := sqrt_sub_le ht ha0 hs hs'
  have hS : 0 < Real.sqrt (2 * a * t) := Real.sqrt_pos.2 (by positivity)
  have h3 : h2 * ρ ≤ Real.sqrt (2 * a * t) := by
    apply Real.le_sqrt_of_sq_le
    calc (h2 * ρ) ^ 2 = h2 ^ 2 * ρ ^ 2 := by ring
      _ ≤ t * (2 * a) := mul_le_mul hh2t ha (by positivity) ht.le
      _ = 2 * a * t := by ring
  calc |Real.sqrt (2 * s / t) - Real.sqrt (2 * s' / t)| * ‖q - v‖
      ≤ (|s - s'| / Real.sqrt (2 * a * t)) * h2 := mul_le_mul h1 hq (norm_nonneg _) (by positivity)
    _ ≤ 1 / ρ * |s - s'| := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hS]
        have : 1 / ρ * |s - s'| * Real.sqrt (2 * a * t) = |s - s'| * (Real.sqrt (2 * a * t) / ρ) := by
          ring
        rw [this]
        have h4 : h2 ≤ Real.sqrt (2 * a * t) / ρ := by rw [le_div_iff₀ hρ]; exact h3
        exact mul_le_mul_of_nonneg_left h4 (abs_nonneg _)

/-- Lipschitz bound of the second half of the curve. -/
lemma es56_lip_second {t b h2 ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ) (_hh2 : 0 ≤ h2) (hh2t : h2 ^ 2 ≤ t)
    (hb : ρ ^ 2 ≤ 2 * (t - b)) {v w q : E} (hq : ‖q - w‖ ≤ h2) {s s' : ℝ} (hs : t / 2 ≤ s)
    (hs' : t / 2 ≤ s') (hs1 : s ≤ b) (hs1' : s' ≤ b) :
    ‖es56F t v w q s - es56F t v w q s'‖ ≤ 1 / ρ * |s - s'| := by
  have ha0 : 0 < t - b := by nlinarith [sq_pos_of_pos hρ]
  rw [es56F_of_ge ht hs, es56F_of_ge ht hs']
  have e : w + Real.sqrt (2 * (t - s) / t) • (q - w) - (w + Real.sqrt (2 * (t - s') / t) • (q - w)) =
      (Real.sqrt (2 * (t - s) / t) - Real.sqrt (2 * (t - s') / t)) • (q - w) := by
    rw [sub_smul]; abel
  rw [e, norm_smul, Real.norm_eq_abs]
  have h1 := sqrt_sub_le ht ha0 (x := t - s) (y := t - s') (by linarith) (by linarith)
  have hS : 0 < Real.sqrt (2 * (t - b) * t) := Real.sqrt_pos.2 (by positivity)
  have h3 : h2 * ρ ≤ Real.sqrt (2 * (t - b) * t) := by
    apply Real.le_sqrt_of_sq_le
    calc (h2 * ρ) ^ 2 = h2 ^ 2 * ρ ^ 2 := by ring
      _ ≤ t * (2 * (t - b)) := mul_le_mul hh2t hb (by positivity) ht.le
      _ = 2 * (t - b) * t := by ring
  have habs : |t - s - (t - s')| = |s - s'| := by
    rw [show t - s - (t - s') = -(s - s') by ring, abs_neg]
  rw [habs] at h1
  calc |Real.sqrt (2 * (t - s) / t) - Real.sqrt (2 * (t - s') / t)| * ‖q - w‖
      ≤ (|s - s'| / Real.sqrt (2 * (t - b) * t)) * h2 :=
        mul_le_mul h1 hq (norm_nonneg _) (by positivity)
    _ ≤ 1 / ρ * |s - s'| := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hS]
        have : 1 / ρ * |s - s'| * Real.sqrt (2 * (t - b) * t) =
            |s - s'| * (Real.sqrt (2 * (t - b) * t) / ρ) := by ring
        rw [this]
        have h4 : h2 ≤ Real.sqrt (2 * (t - b) * t) / ρ := by rw [le_div_iff₀ hρ]; exact h3
        exact mul_le_mul_of_nonneg_left h4 (abs_nonneg _)

/-- Lipschitz bound of the curve on `[a, b]`. -/
theorem es56_lip {t a b h2 ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ) (hh2 : 0 ≤ h2) (hh2t : h2 ^ 2 ≤ t)
    (ha : a ≤ t / 2 → ρ ^ 2 ≤ 2 * a) (hb : t / 2 ≤ b → ρ ^ 2 ≤ 2 * (t - b)) {v w q : E}
    (hqv : ‖q - v‖ ≤ h2) (hqw : ‖q - w‖ ≤ h2) {s s' : ℝ} (hs : s ∈ Set.Icc a b)
    (hs' : s' ∈ Set.Icc a b) :
    ‖es56F t v w q s - es56F t v w q s'‖ ≤ 1 / ρ * |s - s'| := by
  wlog hss : s ≤ s' generalizing s s'
  · rw [norm_sub_rev, abs_sub_comm]
    exact this hs' hs (not_le.1 hss).le
  have hq1 : ∀ x y : ℝ, a ≤ x → a ≤ y → x ≤ t / 2 → y ≤ t / 2 →
      ‖es56F t v w q x - es56F t v w q y‖ ≤ 1 / ρ * |x - y| := fun x y hx hy hx' hy' =>
    es56_lip_first ht hρ hh2 hh2t (ha (hx.trans hx')) hqv hx hy hx' hy'
  have hq2 : ∀ x y : ℝ, t / 2 ≤ x → t / 2 ≤ y → x ≤ b → y ≤ b →
      ‖es56F t v w q x - es56F t v w q y‖ ≤ 1 / ρ * |x - y| := fun x y hx hy hx' hy' =>
    es56_lip_second ht hρ hh2 hh2t (hb (hx.trans hx')) hqw hx hy hx' hy'
  by_cases h1 : s' ≤ t / 2
  · exact hq1 s s' hs.1 hs'.1 (hss.trans h1) h1
  · have h1' := not_le.1 h1
    by_cases h2' : t / 2 ≤ s
    · exact hq2 s s' h2' h1'.le hs.2 hs'.2
    · -- `s < t/2 < s'`: split at `t/2`
      have hmid : t / 2 ∈ Set.Icc a b := ⟨by linarith [hs.1, (not_le.1 h2')], by linarith [hs'.2]⟩
      have e1 := hq1 s (t / 2) hs.1 hmid.1 (not_le.1 h2').le le_rfl
      have e2 := hq2 (t / 2) s' le_rfl h1'.le hmid.2 hs'.2
      calc ‖es56F t v w q s - es56F t v w q s'‖
          ≤ ‖es56F t v w q s - es56F t v w q (t / 2)‖ +
            ‖es56F t v w q (t / 2) - es56F t v w q s'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 1 / ρ * |s - t / 2| + 1 / ρ * |t / 2 - s'| := add_le_add e1 e2
        _ = 1 / ρ * |s - s'| := by
            rw [abs_of_nonpos (by linarith [not_le.1 h2']), abs_of_nonpos (by linarith),
              abs_of_nonpos (by linarith [not_le.1 h2'])]
            ring

end ElboimSly.Brownian
