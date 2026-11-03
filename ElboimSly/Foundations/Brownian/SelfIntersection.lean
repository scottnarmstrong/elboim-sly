/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.SelfIntersectionCore
public import ElboimSly.Foundations.Brownian.SelfIntersectionBad
public import ElboimSly.Foundations.Brownian.SelfIntersectionEv

import Mathlib

/-!
# The self-intersection claim (ES22 Claim 9.4)

ES22 Claim 9.4, with the deviation F28
(`ζ ≤ 1/100`).

Let `d ≥ 5`, `ζ ∈ (0, 1/100]`, `B` a standard `d`-dimensional Brownian motion and `t ≥ 1`. Let
`T = {s ∈ [0,t] : ∃ s' ∈ [0, s - t^ζ], ‖B s - B s'‖ ≤ 1}`. Then `ω ↦ |T|` is measurable and
`P (|T| ≥ t^{1-ζ³}) ≤ C exp (-t^{ζ²/4})` with `C = C(ζ)` independent of `d`, `t`, `B` and the
probability space.

* `selfIntersection_five`: the case `d = 5`, from `core_bound` (Steps 1-3), `good_compl_le` (Step 4)
  and `bad_bound`, `siGood_eventually` (Step 5);
* `selfIntersection`: the general case by the reduction to the first five coordinates (Step 0).

The set `T` is `sepSet B 1 (t^ζ) t`; the Lebesgue measure is `nnLebesgue` (the pullback of Lebesgue
measure on `ℝ`), on `ℝ≥0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

universe u

namespace ElboimSly.Brownian

/-- ES22 Claim 9.4, Steps 1-5 for `d = 5`. -/
theorem selfIntersection_five {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 100) :
    ∃ C : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {B : ℝ≥0 → Ω → R5}, IsStandardBrownianMotion 5 B P → ∀ t : ℝ, 1 ≤ t →
      P {ω | ENNReal.ofReal (t ^ (1 - ζ ^ 3)) ≤
        nnLebesgue (sepSet B 1 (Real.toNNReal (t ^ ζ)) (Real.toNNReal t) ω)} ≤
      ENNReal.ofReal (C * Real.exp (-t ^ (ζ ^ 2 / 4))) := by
  obtain ⟨C0, hC0, hbad⟩ := bad_bound hζ hζ1
  obtain ⟨t0, ht0⟩ := eventually_atTop.1 (siGood_eventually hζ hζ1)
  set t1 : ℝ := max t0 1 with ht1
  have ha0 : 0 ≤ ζ ^ 2 / 4 := by positivity
  refine ⟨max C0 (Real.exp (t1 ^ (ζ ^ 2 / 4))), fun {Ω} {mΩ} {P} {hP} {B} hB t ht => ?_⟩
  by_cases htt : t1 ≤ t
  · have hg := ht0 t ((le_max_left _ _).trans htt)
    have hcore := core_bound hB hζ hζ1 ht hg
    have hr1 := siR_one_le hζ ht
    have hρ1 := siRho_one_le hζ ht
    have hRb : 1 ≤ 3 * siBig ζ t := by
      have : 1 ≤ siBig ζ t := Real.one_le_rpow hr1 (by linarith)
      linarith
    have hgood := good_compl_le hB (t := t) (ρ := siRho ζ t) (R₃ := 3 * siBig ζ t)
      (M := siM ζ t) ht (by linarith) hRb (siM_nonneg hζ ht)
      (a := Real.toNNReal (t + 1)) (Real.coe_toNNReal _ (by linarith))
    refine hcore.trans ?_
    calc _ ≤ ENNReal.ofReal (Real.exp (-siMstar ζ t / 2)) +
        (20 * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (t + 1)))) +
          (20 * (⌈t + 1⌉₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-siRho ζ t ^ 2 / 16)) +
          ((latticeBox t).card : ℝ≥0∞) * ENNReal.ofReal
            (2 * Real.exp (-(cocc 5) * (siM ζ t / (3 * siBig ζ t) ^ 2)))) := by
          gcongr
      _ ≤ ENNReal.ofReal (C0 * Real.exp (-t ^ (ζ ^ 2 / 4))) := hbad t ht
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.exp_nonneg _))
  · push Not at htt
    refine (prob_le_one).trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : t ^ (ζ ^ 2 / 4) ≤ t1 ^ (ζ ^ 2 / 4) := Real.rpow_le_rpow (by linarith) htt.le ha0
    have h2 : Real.exp (t1 ^ (ζ ^ 2 / 4)) * Real.exp (-t ^ (ζ ^ 2 / 4)) ≥ 1 := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc (1 : ℝ) ≤ Real.exp (t1 ^ (ζ ^ 2 / 4)) * Real.exp (-t ^ (ζ ^ 2 / 4)) := h2
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)

/-- The first five coordinates of a `d`-dimensional path. -/
def firstFive {Ω : Type*} {d : ℕ} (hd : 5 ≤ d) (B : ℝ≥0 → Ω → (Fin d → ℝ)) : ℝ≥0 → Ω → R5 :=
  fun s ω k => B s ω (Fin.castLE hd k)

lemma sepSet_subset_firstFive {Ω : Type*} {d : ℕ} (hd : 5 ≤ d) (B : ℝ≥0 → Ω → (Fin d → ℝ)) (L t : ℝ≥0)
    (ω : Ω) : sepSet B 1 L t ω ⊆ sepSet (firstFive hd B) 1 L t ω := by
  rintro s ⟨hst, s', hs', hn⟩
  refine ⟨hst, s', hs', le_trans ?_ hn⟩
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro k
  exact norm_le_pi_norm (fun j => ((1 : ℝ) • B s ω - (1 : ℝ) • B s' ω) j) (Fin.castLE hd k)

/-- ES22 Claim 9.4 (ES22 Claim 9.4, with `ζ ≤ 1/100` by F28). -/
theorem selfIntersection {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 100) :
    ∃ C : ℝ, ∀ {d : ℕ}, 5 ≤ d → ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)}, IsStandardBrownianMotion d B P →
      ∀ t : ℝ, 1 ≤ t →
      (Measurable fun ω => nnLebesgue (sepSet B 1 (Real.toNNReal (t ^ ζ)) (Real.toNNReal t) ω)) ∧
      P {ω | ENNReal.ofReal (t ^ (1 - ζ ^ 3)) ≤
        nnLebesgue (sepSet B 1 (Real.toNNReal (t ^ ζ)) (Real.toNNReal t) ω)} ≤
      ENNReal.ofReal (C * Real.exp (-t ^ (ζ ^ 2 / 4))) := by
  obtain ⟨C, hC⟩ := selfIntersection_five.{u} hζ hζ1
  refine ⟨C, fun {d} hd {Ω} {mΩ} {P} {hP} {B} hB t ht => ⟨measurable_sepVol hB 1 _ _, ?_⟩⟩
  have hB5 : IsStandardBrownianMotion 5 (firstFive hd B) P :=
    hB.subvector (ι := Fin.castLE hd) (Fin.castLE_injective hd)
  refine le_trans (measure_mono ?_) (hC hB5 t ht)
  intro ω hω
  exact le_trans hω (measure_mono (sepSet_subset_firstFive hd B _ _ ω))

end ElboimSly.Brownian
