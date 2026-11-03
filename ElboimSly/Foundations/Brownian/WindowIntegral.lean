/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Window
import Mathlib

/-!
# The window function: integral and expectation bounds

One time window (c), (d).

* `Cwin`: the constant `C_win(d) = 4^d + 4d ∑_{m ≥ 1} (2m+4)^d e^{-m²/2}`, with the sum
  reindexed by `m ↦ m + 1` (so that it runs over `ℕ`);
* `lintegral_winG_le`: (c);
* `lintegral_winG_brownian_le`: (d).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The summand of the constant `C_win`. -/
noncomputable def cwinTerm (d m : ℕ) : ℝ :=
  (2 * ((m + 1 : ℕ) : ℝ) + 4) ^ d * Real.exp (-((m + 1 : ℕ) : ℝ) ^ 2 / 2)

lemma cwinTerm_nonneg (d m : ℕ) : 0 ≤ cwinTerm d m := by unfold cwinTerm; positivity

lemma summable_cwinTerm (d : ℕ) : Summable (cwinTerm d) := by
  have h1 : Summable fun n : ℕ => (n : ℝ) ^ d * Real.exp (-(1 / 2 : ℝ) * n) :=
    Real.summable_pow_mul_exp_neg_nat_mul d (by norm_num)
  have h2 : Summable fun m : ℕ => (((m + 1 : ℕ) : ℝ)) ^ d * Real.exp (-(1 / 2 : ℝ) * ((m + 1 : ℕ) : ℝ)) :=
    (summable_nat_add_iff 1).2 h1
  refine Summable.of_nonneg_of_le (cwinTerm_nonneg d) (fun m => ?_) (h2.mul_left (6 ^ d))
  unfold cwinTerm
  have hn : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  set n : ℝ := ((m + 1 : ℕ) : ℝ)
  have h3 : (2 * n + 4) ^ d ≤ (6 * n) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  have h4 : Real.exp (-n ^ 2 / 2) ≤ Real.exp (-(1 / 2 : ℝ) * n) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith
  calc (2 * n + 4) ^ d * Real.exp (-n ^ 2 / 2)
      ≤ (6 * n) ^ d * Real.exp (-(1 / 2 : ℝ) * n) :=
        mul_le_mul h3 h4 (Real.exp_pos _).le (by positivity)
    _ = 6 ^ d * (n ^ d * Real.exp (-(1 / 2 : ℝ) * n)) := by rw [mul_pow]; ring

/-- One time window (c). The constant `C_win(d)`. -/
noncomputable def Cwin (d : ℕ) : ℝ := 4 ^ d + 4 * d * ∑' m : ℕ, cwinTerm d m

lemma Cwin_nonneg (d : ℕ) : 0 ≤ Cwin d := by
  unfold Cwin
  have : 0 ≤ ∑' m : ℕ, cwinTerm d m := tsum_nonneg (cwinTerm_nonneg d)
  positivity

/-- The shells of the partition of `ℝ^d` used in one time window (c). -/
def winShell (d : ℕ) (r : ℝ) : ℕ → Set (Fin d → ℝ)
  | 0 => {z | ‖z‖ < 2 * r}
  | m + 1 => {z | ((m : ℝ) + 2) * r ≤ ‖z‖ ∧ ‖z‖ < ((m : ℝ) + 3) * r}

lemma measurableSet_winShell (d : ℕ) (r : ℝ) (m : ℕ) : MeasurableSet (winShell d r m) := by
  cases m with
  | zero => exact measurableSet_lt measurable_norm measurable_const
  | succ m =>
    exact (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)

/-- The value of `g` on a shell. -/
noncomputable def winShellVal (d : ℕ) : ℕ → ℝ≥0∞
  | 0 => 1
  | m + 1 => ENNReal.ofReal (4 * d * Real.exp (-((m + 1 : ℕ) : ℝ) ^ 2 / 2))

lemma winG_le_shell {r : ℝ} (hr : 0 < r) (z : Fin d → ℝ) :
    ∃ m, z ∈ winShell d r m ∧ winG d r (r ^ 2) ‖z‖ ≤ winShellVal d m := by
  by_cases hz : ‖z‖ < 2 * r
  · exact ⟨0, hz, winG_le_one _ _ _ _⟩
  · have hz := not_lt.1 hz
    have hn2 : 2 ≤ ⌊‖z‖ / r⌋₊ := Nat.le_floor (by rw [le_div_iff₀ hr]; exact_mod_cast hz)
    obtain ⟨m, hm⟩ : ∃ m, ⌊‖z‖ / r⌋₊ = m + 2 := ⟨⌊‖z‖ / r⌋₊ - 2, by omega⟩
    have h1 : ((m + 2 : ℕ) : ℝ) ≤ ‖z‖ / r := hm ▸ Nat.floor_le (by positivity)
    have h2 : ‖z‖ / r < ((m + 2 : ℕ) : ℝ) + 1 := hm ▸ Nat.lt_floor_add_one _
    rw [le_div_iff₀ hr] at h1
    rw [div_lt_iff₀ hr] at h2
    push_cast at h1 h2
    refine ⟨m + 1, ⟨by linarith, by linarith⟩, ?_⟩
    have hlt : r < ‖z‖ := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    rw [winG_of_lt hlt]
    refine (min_le_right _ _).trans ?_
    unfold winShellVal
    refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.exp_le_exp.2 ?_
    have hm : ((m : ℝ) + 1) * r ≤ ‖z‖ - r := by nlinarith
    have hm0 : 0 ≤ ((m : ℝ) + 1) * r := by positivity
    have hsq : (((m : ℝ) + 1) * r) ^ 2 ≤ (‖z‖ - r) ^ 2 := pow_le_pow_left₀ hm0 hm 2
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg r]

lemma volume_winShell_le (d : ℕ) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    volume (winShell d r m) ≤ ENNReal.ofReal
      ((match m with | 0 => 4 | m + 1 => 2 * ((m : ℝ) + 3)) ^ d * r ^ d) := by
  have hball : ∀ R : ℝ, 0 ≤ R →
      volume (Metric.closedBall (0 : Fin d → ℝ) R) = ENNReal.ofReal ((2 * R) ^ d) := by
    intro R hR
    rw [Real.volume_pi_closedBall _ hR]
    simp
  cases m with
  | zero =>
    refine le_trans (measure_mono (t := Metric.closedBall (0 : Fin d → ℝ) (2 * r)) ?_) ?_
    · intro z hz
      simpa [mem_closedBall_zero_iff] using (le_of_lt hz : ‖z‖ ≤ 2 * r)
    · rw [hball _ (by positivity)]
      refine le_of_eq ?_
      rw [← mul_pow]
      congr 2; ring
  | succ m =>
    refine le_trans (measure_mono (t := Metric.closedBall (0 : Fin d → ℝ) (((m : ℝ) + 3) * r)) ?_) ?_
    · intro z hz
      simpa [mem_closedBall_zero_iff] using (le_of_lt hz.2 : ‖z‖ ≤ ((m : ℝ) + 3) * r)
    · rw [hball _ (by positivity)]
      refine le_of_eq ?_
      rw [← mul_pow]
      congr 2; ring

/-- One time window (c). `∫ g_{r,r²}(‖z‖) dz ≤ C_win r^d`. -/
theorem lintegral_winG_le (d : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ z : Fin d → ℝ, winG d r (r ^ 2) ‖z‖ ≤ ENNReal.ofReal (Cwin d * r ^ d) := by
  have hpt : ∀ z : Fin d → ℝ, winG d r (r ^ 2) ‖z‖ ≤
      ∑' m : ℕ, (winShell d r m).indicator (fun _ => winShellVal d m) z := by
    intro z
    obtain ⟨m, hm, hle⟩ := winG_le_shell hr z
    refine hle.trans ?_
    calc winShellVal d m = (winShell d r m).indicator (fun _ => winShellVal d m) z := by
          rw [Set.indicator_of_mem hm]
      _ ≤ _ := ENNReal.le_tsum (f := fun m => (winShell d r m).indicator (fun _ => winShellVal d m) z) m
  calc ∫⁻ z : Fin d → ℝ, winG d r (r ^ 2) ‖z‖
      ≤ ∫⁻ z : Fin d → ℝ, ∑' m : ℕ, (winShell d r m).indicator (fun _ => winShellVal d m) z :=
        lintegral_mono hpt
    _ = ∑' m : ℕ, winShellVal d m * volume (winShell d r m) := by
        rw [lintegral_tsum fun m => (measurable_const.indicator
          (measurableSet_winShell d r m)).aemeasurable]
        refine tsum_congr fun m => ?_
        rw [lintegral_indicator_const (measurableSet_winShell d r m)]
    _ ≤ ∑' m : ℕ, winShellVal d m * ENNReal.ofReal
          ((match m with | 0 => 4 | m + 1 => 2 * ((m : ℝ) + 3)) ^ d * r ^ d) :=
        ENNReal.tsum_le_tsum fun m => mul_le_mul_right (volume_winShell_le d hr m) _
    _ = ENNReal.ofReal (4 ^ d * r ^ d) + ∑' m : ℕ,
          ENNReal.ofReal (4 * d * r ^ d * cwinTerm d m) := by
        rw [tsum_eq_zero_add' ENNReal.summable]
        congr 1
        · simp [winShellVal]
        · refine tsum_congr fun m => ?_
          simp only [winShellVal, cwinTerm]
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          push_cast
          have : (2 * ((m : ℝ) + 3)) = 2 * ((m : ℝ) + 1) + 4 := by ring
          rw [this]
          ring
    _ = ENNReal.ofReal (Cwin d * r ^ d) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by have := cwinTerm_nonneg d m; positivity)
          ((summable_cwinTerm d).mul_left (4 * d * r ^ d)), ← ENNReal.ofReal_add (by positivity)
          (tsum_nonneg fun m => by have := cwinTerm_nonneg d m; positivity)]
        congr 1
        rw [tsum_mul_left]
        unfold Cwin
        ring

lemma measurable_winG (d : ℕ) (r h : ℝ) : Measurable (winG d r h) := by
  unfold winG
  refine Measurable.ite measurableSet_Iic measurable_const ?_
  exact measurable_const.min (ENNReal.measurable_ofReal.comp (by fun_prop))

lemma measurable_bmDensity (d : ℕ) (t : ℝ≥0) : Measurable (bmDensity d t) := by
  unfold bmDensity
  fun_prop

/-- One time window (d). For `a > 0`,
`E g_{r,r²}(‖y + B(a)‖) ≤ (2π a)^{-d/2} C_win r^d`. -/
theorem lintegral_winG_brownian_le [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)}
    (hB : IsStandardBrownianMotion d B P) {a : ℝ≥0} (ha : a ≠ 0) (y : Fin d → ℝ) {r : ℝ}
    (hr : 0 < r) :
    ∫⁻ ω, winG d r (r ^ 2) ‖y + B a ω‖ ∂P ≤
      ENNReal.ofReal ((2 * Real.pi * a) ^ (-(d : ℝ) / 2) * (Cwin d * r ^ d)) := by
  have hG : Measurable fun z : Fin d → ℝ => winG d r (r ^ 2) ‖y + z‖ :=
    (measurable_winG d r _).comp (measurable_const.add measurable_id).norm
  have hlaw := (hB.hasLaw_eval_density ha).map_eq
  calc ∫⁻ ω, winG d r (r ^ 2) ‖y + B a ω‖ ∂P
      = ∫⁻ z, winG d r (r ^ 2) ‖y + z‖ ∂(P.map (B a)) := by
        rw [lintegral_map hG (hB.measurable a)]
    _ = ∫⁻ z, ENNReal.ofReal (bmDensity d a z) * winG d r (r ^ 2) ‖y + z‖ := by
        rw [hlaw]
        exact lintegral_withDensity_eq_lintegral_mul (μ := volume)
          (f := fun z => ENNReal.ofReal (bmDensity d a z))
          (ENNReal.measurable_ofReal.comp (measurable_bmDensity d a)) hG
    _ ≤ ∫⁻ z, ENNReal.ofReal ((2 * Real.pi * a) ^ (-(d : ℝ) / 2)) *
          winG d r (r ^ 2) ‖y + z‖ := by
        refine lintegral_mono fun z => ?_
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (bmDensity_le_const a z)) _
    _ = ENNReal.ofReal ((2 * Real.pi * a) ^ (-(d : ℝ) / 2)) *
          ∫⁻ z, winG d r (r ^ 2) ‖z‖ := by
        rw [lintegral_const_mul _ hG]
        congr 1
        exact lintegral_add_left_eq_self (μ := (volume : Measure (Fin d → ℝ)))
          (fun z => winG d r (r ^ 2) ‖z‖) y
    _ ≤ ENNReal.ofReal ((2 * Real.pi * a) ^ (-(d : ℝ) / 2)) *
          ENNReal.ofReal (Cwin d * r ^ d) :=
        mul_le_mul_right (lintegral_winG_le d hr) _
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

end ElboimSly.Brownian
