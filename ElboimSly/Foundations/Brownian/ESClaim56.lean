/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Tube
public import ElboimSly.Foundations.Brownian.ESCurve
import Mathlib

/-!
# ES22 Claim 5.6: the tube step, uniform over scales

ES22 Claim 5.6: the tube step, uniform over scales.

The quantity `2^{j-1}` of the written proof enters only through the numbers `h2 = 2^{j-1}` with
`h2² ≤ t` (the hypothesis `4^{j-1} ≤ t`); `t ≤ 4^j` is not used. The exponents `i - m`, `m - i` are
natural numbers: for `i ≤ m` put `k = m - i`, and for `i > m` put `k = i - m`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

/-- ES22 Claim 5.6: the tube step, uniform over scales. `c_56(d) = c_tube(d, 1000)`. -/
noncomputable def c56 (d : ℕ) : ℝ := ctube d 1000

/-- The radius `ρ_i`. -/
noncomputable def es56Rho (t : ℝ) (m i : ℕ) : ℝ :=
  if i ≤ m then Real.sqrt t / 2 ^ (m - i + 5) else Real.sqrt t / 2 ^ (i - m + 3)

/-- The endpoint `b_i`. -/
noncomputable def es56B (t : ℝ) (m i : ℕ) : ℝ :=
  if i ≤ m then 3 / 5 * t / 4 ^ (m - i) else t - 3 / 10 * t / 4 ^ (i - m)

/-- The left end of the range `ℛ_i`. -/
noncomputable def es56Lo (t : ℝ) (m i : ℕ) : ℝ :=
  if i ≤ m then t / (2 * 4 ^ (m - i + 1)) else if i = m + 1 then t / 2 else t - 2 * t / 4 ^ (i - m)

/-- The right end of the range `ℛ_i`. -/
noncomputable def es56Hi (t : ℝ) (m i : ℕ) : ℝ :=
  if i ≤ m then 3 / 5 * t / 4 ^ (m - i + 1) else if i = m + 1 then 3 / 5 * t
  else t - 6 / 5 * t / 4 ^ (i - m)

section B

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
  {B : ℝ≥0 → Ω → (Fin d → ℝ)}

/-- Generic application of the tube lemma on the window `[a, b]`, with `K = 1000`. -/
theorem es56_core [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P) {ρ a b : ℝ}
    (hρ : 0 < ρ) (_ha0 : 0 ≤ a) (hab : a < b) {f : ℝ → Fin d → ℝ}
    (hLip : ∀ s ∈ Set.Icc a b, ∀ s' ∈ Set.Icc a b, ‖f s - f s'‖ ≤ 1 / ρ * |s - s'|)
    (hT1 : ρ ^ 2 / 1000 ≤ b - a) (hT2 : b - a ≤ 1000 * ρ ^ 2) {σ : ℝ} (hσ1 : 1 ≤ σ)
    (hσ2 : σ ≤ 2) {x : Fin d → ℝ} (hx : ‖x - f a‖ ≤ 3 * ρ / 5) :
    ENNReal.ofReal (c56 d) ≤ P {ω | (∀ u : ℝ≥0, (u : ℝ) ≤ b - a →
        ‖x + σ • B u ω - f (a + u)‖ ≤ ρ) ∧
      (∀ u : ℝ≥0, (b - a) / 2 ≤ u → (u : ℝ) ≤ b - a → ‖x + σ • B u ω - f (a + u)‖ ≤ ρ / 5)} := by
  set T : ℝ≥0 := (b - a).toNNReal with hT
  have hTR : (T : ℝ) = b - a := Real.coe_toNNReal _ (by linarith)
  set f' : ℝ → Fin d → ℝ := fun u => f (a + u) with hf'
  have hmem : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) T → a + u ∈ Set.Icc a b := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2, hTR]⟩
  have hLip' : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ v ∈ Set.Icc (0 : ℝ) T,
      ‖f' u - f' v‖ ≤ 1000 / ρ * |u - v| := by
    intro u hu v hv
    have := hLip _ (hmem u hu) _ (hmem v hv)
    refine this.trans ?_
    have e : |a + u - (a + v)| = |u - v| := by congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (by rw [div_le_div_iff_of_pos_right hρ]; norm_num)
      (abs_nonneg _)
  have h := tube_lemma_event (K := 1000) hB (by norm_num) hσ1 hσ2 hρ (T := T) (f := f') (x := x)
    (by rw [hTR]; linarith) (by rw [hTR]; linarith) hLip' (by simpa [hf'] using hx)
  refine le_trans h.2.2 (measure_mono ?_)
  rintro ω ⟨h1, h2⟩
  refine ⟨fun u hu => h1 u (by rw [← NNReal.coe_le_coe, hTR]; exact hu),
    fun u hu hu' => h2 u ?_ (by rw [← NNReal.coe_le_coe, hTR]; exact hu')⟩
  rw [← NNReal.coe_le_coe]
  push_cast
  rw [hTR]; exact hu

end B

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
  {B : ℝ≥0 → Ω → (Fin d → ℝ)}

/-- ES22 Claim 5.6: the tube step, uniform over scales (ES22 Claim 5.6). -/
theorem es56_main [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P) {t h2 : ℝ}
    (ht : 0 < t) (hh2 : 0 ≤ h2) (hh2t : h2 ^ 2 ≤ t) {q v w : Fin d → ℝ} (hqv : ‖q - v‖ ≤ h2)
    (hqw : ‖q - w‖ ≤ h2) {m i : ℕ} (_hi1 : 1 ≤ i) {σ ρ a : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2)
    (hρ1 : 5 / 6 * es56Rho t m i ≤ ρ) (hρ2 : ρ ≤ es56Rho t m i) (ha1 : es56Lo t m i ≤ a)
    (ha2 : a ≤ es56Hi t m i) {x : Fin d → ℝ} (hx : ‖x - es56F t v w q a‖ ≤ 3 * ρ / 5) :
    ENNReal.ofReal (c56 d) ≤ P {ω | (∀ u : ℝ≥0, (u : ℝ) ≤ es56B t m i - a →
        ‖x + σ • B u ω - es56F t v w q (a + u)‖ ≤ ρ) ∧
      (∀ u : ℝ≥0, (es56B t m i - a) / 2 ≤ u → (u : ℝ) ≤ es56B t m i - a →
        ‖x + σ • B u ω - es56F t v w q (a + u)‖ ≤ ρ / 5)} := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hρi : 0 < es56Rho t m i := by
    unfold es56Rho; split_ifs <;> positivity
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity) hρ1
  have hρsq : ρ ^ 2 ≤ es56Rho t m i ^ 2 := pow_le_pow_left₀ hρ.le hρ2 2
  have hρsq' : 25 / 36 * es56Rho t m i ^ 2 ≤ ρ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hρ1 2
    linarith only [this]
  by_cases hi : i ≤ m
  · -- the case `i ≤ m`
    obtain ⟨k, hk⟩ : ∃ k, k = m - i := ⟨_, rfl⟩
    set S : ℝ := 2 ^ k with hS
    have hS1 : 1 ≤ S := one_le_pow₀ (by norm_num)
    have hX : (4 : ℝ) ^ k = S ^ 2 := by
      rw [hS, ← pow_mul, mul_comm, pow_mul]; norm_num
    set y : ℝ := t / S ^ 2 with hy
    have hSpos : 0 < S ^ 2 := by positivity
    have hty : t = y * S ^ 2 := by rw [hy]; field_simp
    have hy0 : 0 < y := by positivity
    have hyt : y ≤ t := by
      rw [hty]
      exact le_mul_of_one_le_right hy0.le (one_le_pow₀ hS1)
    have hrho : es56Rho t m i ^ 2 = y / 1024 := by
      unfold es56Rho; rw [ite_eq_left hi, ← hk, div_pow, Real.sq_sqrt ht.le, pow_add, ← hS]
      rw [hy]; field_simp; ring
    have hb : es56B t m i = 3 / 5 * y := by
      unfold es56B; rw [ite_eq_left hi, ← hk, hX, hy]; ring
    have hlo : y / 8 ≤ a := by
      have : es56Lo t m i = y / 8 := by
        unfold es56Lo; rw [ite_eq_left hi, ← hk, pow_add, hX, hy]; field_simp; ring
      linarith
    have hhi : a ≤ 3 / 20 * y := by
      have : es56Hi t m i = 3 / 20 * y := by
        unfold es56Hi; rw [ite_eq_left hi, ← hk, pow_add, hX, hy]; field_simp; ring
      linarith
    have hr1 : ρ ^ 2 ≤ y / 1024 := hrho ▸ hρsq
    have hr2 : 25 / 36 * (y / 1024) ≤ ρ ^ 2 := hrho ▸ hρsq'
    have hLip : ∀ s ∈ Set.Icc a (es56B t m i), ∀ s' ∈ Set.Icc a (es56B t m i),
        ‖es56F t v w q s - es56F t v w q s'‖ ≤ 1 / ρ * |s - s'| := fun s hs s' hs' =>
      es56_lip ht hρ hh2 hh2t (fun _ => by linarith) (fun _ => by rw [hb]; linarith) hqv hqw hs hs'
    exact es56_core hB hρ (by linarith) (by rw [hb]; linarith) hLip
      (by rw [hb]; linarith) (by rw [hb]; linarith) hσ1 hσ2 hx
  · -- the case `i > m`
    have hi' := not_le.1 hi
    obtain ⟨k, hk⟩ : ∃ k, k = i - m := ⟨_, rfl⟩
    have hk1 : 1 ≤ k := by omega
    set S : ℝ := 2 ^ k with hS
    have hS1 : 1 ≤ S := one_le_pow₀ (by norm_num)
    have hX : (4 : ℝ) ^ k = S ^ 2 := by
      rw [hS, ← pow_mul, mul_comm, pow_mul]; norm_num
    set y : ℝ := t / S ^ 2 with hy
    have hSpos : 0 < S ^ 2 := by positivity
    have hty : t = y * S ^ 2 := by rw [hy]; field_simp
    have hy0 : 0 < y := by positivity
    have hS2 : 2 ≤ S := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk1
    have hS4 : 4 ≤ S ^ 2 :=
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ S ^ 2 := pow_le_pow_left₀ (by norm_num) hS2 2
    have hyt : 4 * y ≤ t := by
      rw [hty]
      linarith only [mul_le_mul_of_nonneg_left hS4 hy0.le]
    have hrho : es56Rho t m i ^ 2 = y / 64 := by
      unfold es56Rho; rw [ite_eq_right hi, ← hk, div_pow, Real.sq_sqrt ht.le, pow_add, ← hS]
      rw [hy]; field_simp; ring
    have hb : es56B t m i = t - 3 / 10 * y := by
      unfold es56B; rw [ite_eq_right hi, ← hk, hX, hy]; ring
    have hr1 : ρ ^ 2 ≤ y / 64 := hrho ▸ hρsq
    have hr2 : 25 / 36 * (y / 64) ≤ ρ ^ 2 := hrho ▸ hρsq'
    have hrange : t / 2 ≤ a ∧ 9 / 10 * y ≤ es56B t m i - a ∧ es56B t m i - a ≤ 17 / 10 * y := by
      by_cases h1 : i = m + 1
      · have hk' : k = 1 := by omega
        have hS' : S = 2 := by rw [hS, hk']; norm_num
        have hy' : t = 4 * y := by rw [hty, hS']; ring
        have hlo : es56Lo t m i = t / 2 := by unfold es56Lo; rw [ite_eq_right hi, ite_eq_left h1]
        have hhi : es56Hi t m i = 3 / 5 * t := by unfold es56Hi; rw [ite_eq_right hi, ite_eq_left h1]
        rw [hb]
        refine ⟨by linarith, by linarith, by linarith⟩
      · have hlo : es56Lo t m i = t - 2 * y := by
          unfold es56Lo; rw [ite_eq_right hi, ite_eq_right h1, ← hk, hX, hy]; field_simp
        have hhi : es56Hi t m i = t - 6 / 5 * y := by
          unfold es56Hi; rw [ite_eq_right hi, ite_eq_right h1, ← hk, hX, hy]; field_simp
        rw [hb]
        refine ⟨by linarith, by linarith, by linarith⟩
    obtain ⟨hr_a, hr_T1, hr_T2⟩ := hrange
    have hLip : ∀ s ∈ Set.Icc a (es56B t m i), ∀ s' ∈ Set.Icc a (es56B t m i),
        ‖es56F t v w q s - es56F t v w q s'‖ ≤ 1 / ρ * |s - s'| := fun s hs s' hs' =>
      es56_lip ht hρ hh2 hh2t (fun _ => by linarith) (fun _ => by rw [hb]; linarith)
        hqv hqw hs hs'
    exact es56_core hB hρ (by linarith) (by linarith) hLip
      (by linarith) (by linarith) hσ1 hσ2 hx

end Main

/-- ES22 Claim 5.6: the tube step, uniform over scales, "Moreover": for `i > m` the second condition covers every `u`
with `a + u ∈ [t - 4^{m-i} t/2, b_i]`. -/
theorem es56_window {t : ℝ} (ht : 0 < t) {m i : ℕ} (hi : m < i) {a : ℝ}
    (ha2 : a ≤ es56Hi t m i) {u : ℝ≥0}
    (hu1 : t - t / (2 * 4 ^ (i - m)) ≤ a + u) (hu2 : a + u ≤ es56B t m i) :
    (es56B t m i - a) / 2 ≤ u ∧ (u : ℝ) ≤ es56B t m i - a := by
  have hi' : ¬ i ≤ m := not_le.2 hi
  obtain ⟨k, hk⟩ : ∃ k, k = i - m := ⟨_, rfl⟩
  have hk1 : 1 ≤ k := by omega
  set S : ℝ := 2 ^ k with hS
  have hS1 : 1 ≤ S := one_le_pow₀ (by norm_num)
  have hX : (4 : ℝ) ^ k = S ^ 2 := by
    rw [hS, ← pow_mul, mul_comm, pow_mul]; norm_num
  set y : ℝ := t / S ^ 2 with hy
  have hSpos : 0 < S ^ 2 := by positivity
  have hty : t = y * S ^ 2 := by rw [hy]; field_simp
  have hy0 : 0 < y := by positivity
  have hS2 : 2 ≤ S := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk1
  have hb : es56B t m i = t - 3 / 10 * y := by
    unfold es56B; rw [ite_eq_right hi', ← hk, hX, hy]; ring
  have hy2 : t / (2 * 4 ^ (i - m)) = y / 2 := by
    rw [← hk, hX, hy]; field_simp
  rw [hy2] at hu1
  have hha : a ≤ t - 7 / 10 * y := by
    by_cases h1 : i = m + 1
    · have hk' : k = 1 := by omega
      have hS' : S = 2 := by rw [hS, hk']; norm_num
      have hy' : t = 4 * y := by rw [hty, hS']; ring
      have : es56Hi t m i = 3 / 5 * t := by unfold es56Hi; rw [ite_eq_right hi', ite_eq_left h1]
      linarith
    · have : es56Hi t m i = t - 6 / 5 * y := by
        unfold es56Hi; rw [ite_eq_right hi', ite_eq_right h1, ← hk, hX, hy]; field_simp
      linarith
  rw [hb] at hu2 ⊢
  constructor <;> linarith

/-- ES22 Claim 5.6: the tube step, uniform over scales, "Transfer to a coupled path", the parameters: for
`ε ∈ [0, ρ_i/20]` and `‖x - f(a)‖ ≤ ρ_i/2`, the radius `ρ = ρ_i - ε` satisfies the hypotheses
of `es56_main`. -/
theorem es56_transfer_params {ρi ε : ℝ} (hρi : 0 < ρi) (hε0 : 0 ≤ ε) (hε : ε ≤ ρi / 20) :
    5 / 6 * ρi ≤ ρi - ε ∧ ρi - ε ≤ ρi ∧ ρi / 2 ≤ 3 * (ρi - ε) / 5 := by
  refine ⟨by linarith, by linarith, by linarith⟩

/-- ES22 Claim 5.6: the tube step, uniform over scales, "Transfer to a coupled path": on the event of `es56_main` with
`ρ = ρ_i - ε`, every path `y` within `ε` of `x + σ B` satisfies the bounds required of the walk. -/
theorem es56_transfer {d : ℕ} {ρi ε ρ : ℝ} (hρ : ρ = ρi - ε) (hε0 : 0 ≤ ε) (hε : ε ≤ ρi / 20)
    {z y : Fin d → ℝ} {c : Fin d → ℝ} (hy : ‖y - z‖ ≤ ε) :
    (‖z - c‖ ≤ ρ → ‖y - c‖ ≤ ρi) ∧ (‖z - c‖ ≤ ρ / 5 → ‖y - c‖ ≤ ρi / 4) := by
  have hyc : ‖y - c‖ ≤ ‖y - z‖ + ‖z - c‖ := by
    calc ‖y - c‖ = ‖(y - z) + (z - c)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  constructor
  · intro h; rw [hρ] at h; linarith
  · intro h; rw [hρ] at h; linarith

end ElboimSly.Brownian
