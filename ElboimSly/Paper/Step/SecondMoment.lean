/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Levels
public import ElboimSly.Paper.Step.WalkPathAux
public import ElboimSly.Paper.Step.WienerAux
public import Mathlib

/-!
# Second moment of a truncated endpoint

Second moment of a truncated endpoint (ES22 Lemma 7.3, ES22 §7, and Lemma 7.4, ES22 §7).

Assume `StepRegime d n₁ β n t₀` and `β ≥ 12^16`. For every real `h` with `4^n₁ < h ≤ 4^n` and every
`K ≥ 0`,
`E[1{sup_{s ≤ h} ‖W(s)‖ ≤ K} ‖W(h)‖²] ≤ 6dh + 2h^{2θ_H} + K² e^{-n(h)²}`,
for the regenerated walk of every Poisson environment sequence; the same with `< K`.
The expectation is the lower integral (`∫⁻` of `ofReal`).
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Second moment of a truncated endpoint. -/
theorem step_second_moment_of_ae {n₁ n : ℕ} {t₀ : ℝ} (hR : StepRegime d n₁ β n t₀)
    (hβ : (12 : ℝ) ^ 16 ≤ β) {h : ℝ} (h1 : (4 : ℝ) ^ n₁ < h) (h2 : h ≤ 4 ^ n)
    {K : ℝ} (hK : 0 ≤ K)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β))
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    (hFae : AEMeasurable (fun ω (t : Set.Icc (0 : ℝ≥0) h.toNNReal) =>
      regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ)) P) :
    ∫⁻ ω, {ω | ⨆ r : Set.Icc (0 : ℝ) h,
        ENNReal.ofReal ‖regenWalk (fun k => copyEnv (N ω) k) (r : ℝ)‖ ≤ ENNReal.ofReal K}.indicator
      (fun ω => ENNReal.ofReal (‖regenWalk (fun k => copyEnv (N ω) k) h‖ ^ 2)) ω ∂P ≤
    ENNReal.ofReal (6 * d * h + 2 * h ^ (2 * indThetaH) +
      K ^ 2 * Real.exp (-((stepLevel h : ℝ) ^ 2))) := by
  have hh1 : 1 < h := lt_of_le_of_lt (one_le_pow₀ (by norm_num)) h1
  have hh0 : 0 < h := by linarith
  obtain ⟨-, -, -, -, -, -, -, -, H4⟩ := stepRegime_level hR h1 h2
  obtain ⟨σ, hσ, hC⟩ := H4 Ω P N hN
  obtain ⟨hσ1, hσ2, hσ3⟩ := step_sigma_bounds hβ hh0 hσ
  set T : ℝ≥0 := h.toNNReal with hT
  have hTc : (T : ℝ) = h := Real.coe_toNNReal _ hh0.le
  set ε : ℝ := h ^ indThetaH with hε
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hh0 _
  set η : ℝ := Real.exp (-((stepLevel h : ℝ) ^ 2)) with hη
  set F : Ω → (Set.Icc (0 : ℝ≥0) T → Fin d → ℤ) :=
    fun ω t => regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ) with hF
  obtain ⟨Q, hQp, hQmap, hQW, hQfail⟩ := hC
  -- measurable pieces on the path space
  let A' : Set (Set.Icc (0 : ℝ≥0) T → Fin d → ℤ) := {p | ∀ q ∈ walkCount T, ‖p q‖ ≤ K}
  have hA'm : MeasurableSet A' := by
    have : A' = ⋂ q ∈ walkCount T, {p | ‖p q‖ ≤ K} := by
      ext p; simp [A']
    rw [this]
    refine MeasurableSet.biInter (walkCount_countable T) fun q _ => ?_
    exact measurableSet_le ((measurable_of_countable (fun v : Fin d → ℤ => ‖v‖)).comp
      (measurable_pi_apply q)) measurable_const
  let G : (Set.Icc (0 : ℝ≥0) T → Fin d → ℤ) → ℝ≥0∞ :=
    A'.indicator (fun p => ENNReal.ofReal (‖p (walkTop T)‖ ^ 2))
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ hA'm
    exact ENNReal.measurable_ofReal.comp
      (((measurable_of_countable (fun v : Fin d → ℤ => ‖v‖)).comp
        (measurable_pi_apply (walkTop T))).pow_const 2)
  -- Step 1: compare with G ∘ F
  have hstep1 : ∫⁻ ω, {ω | ⨆ r : Set.Icc (0 : ℝ) h,
        ENNReal.ofReal ‖regenWalk (fun k => copyEnv (N ω) k) (r : ℝ)‖ ≤ ENNReal.ofReal K}.indicator
      (fun ω => ENNReal.ofReal (‖regenWalk (fun k => copyEnv (N ω) k) h‖ ^ 2)) ω ∂P ≤
      ∫⁻ ω, G (F ω) ∂P := by
    refine lintegral_mono fun ω => ?_
    by_cases hω : ω ∈ {ω | ⨆ r : Set.Icc (0 : ℝ) h,
        ENNReal.ofReal ‖regenWalk (fun k => copyEnv (N ω) k) (r : ℝ)‖ ≤ ENNReal.ofReal K}
    · rw [Set.indicator_of_mem hω]
      have hmem : F ω ∈ A' := by
        intro q _
        have hq : ((q : ℝ≥0) : ℝ) ∈ Set.Icc (0 : ℝ) h :=
          ⟨NNReal.coe_nonneg _, by rw [← hTc]; exact_mod_cast q.2.2⟩
        have := (le_iSup (fun r : Set.Icc (0 : ℝ) h =>
          ENNReal.ofReal ‖regenWalk (fun k => copyEnv (N ω) k) (r : ℝ)‖) ⟨_, hq⟩).trans hω
        exact (ENNReal.ofReal_le_ofReal_iff hK).1 this
      simp only [G, Set.indicator_of_mem hmem]
      have : ((walkTop T : ℝ≥0) : ℝ) = h := hTc
      simp only [hF, this]
      exact le_rfl
    · rw [Set.indicator_of_notMem hω]; exact zero_le
  refine hstep1.trans ?_
  -- Step 2: transfer to Q
  have hmeasfst : Measurable (fun p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) => p.1.1) :=
    measurable_subtype_coe.comp measurable_fst
  have hstep2 : ∫⁻ ω, G (F ω) ∂P = ∫⁻ p, G p.1.1 ∂Q := by
    calc ∫⁻ ω, G (F ω) ∂P = ∫⁻ x, G x ∂(P.map F) := (lintegral_map' hGm.aemeasurable hFae).symm
      _ = ∫⁻ x, G x ∂(Q.map (fun p => p.1.1)) := by rw [hQmap]
      _ = ∫⁻ p, G p.1.1 ∂Q := lintegral_map hGm hmeasfst
  rw [hstep2]
  -- Step 3: pointwise bound on Q
  let Fl : Set (WalkPath d T × C(ℝ≥0, Fin d → ℝ)) := {p | ENNReal.ofReal ε ≤
    ⨆ t : Set.Icc (0 : ℝ≥0) T,
      ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • p.2 (t : ℝ≥0)‖}
  have hσ0 : 0 ≤ σ := by linarith
  have hpt : ∀ p : WalkPath d T × C(ℝ≥0, Fin d → ℝ), G p.1.1 ≤
      ENNReal.ofReal (2 * σ ^ 2) * ENNReal.ofReal (‖p.2 T‖ ^ 2) +
        (ENNReal.ofReal (2 * ε ^ 2) + Fl.indicator (fun _ => ENNReal.ofReal (K ^ 2)) p) := by
    intro p
    by_cases hp : p ∈ Fl
    · rw [Set.indicator_of_mem hp]
      refine le_trans ?_ (le_add_of_le_right (le_add_of_le_right le_rfl))
      by_cases hA : p.1.1 ∈ A'
      · simp only [G, Set.indicator_of_mem hA]
        refine ENNReal.ofReal_le_ofReal ?_
        have := hA (walkTop T) (walkTop_mem T)
        have h0 := norm_nonneg (p.1.1 (walkTop T))
        nlinarith
      · simp only [G, Set.indicator_of_notMem hA]; exact zero_le
    · rw [Set.indicator_of_notMem hp, add_zero]
      refine (Set.indicator_le_self _ _ _).trans ?_
      have hlt : ¬ ENNReal.ofReal ε ≤ ⨆ t : Set.Icc (0 : ℝ≥0) T,
          ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • p.2 (t : ℝ≥0)‖ := hp
      rw [not_le] at hlt
      have h3 := (le_iSup (fun t : Set.Icc (0 : ℝ≥0) T =>
          ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • p.2 (t : ℝ≥0)‖)
          (walkTop T)).trans_lt hlt
      have h4 : ‖(fun i => ((p.1.1 (walkTop T) i : ℤ) : ℝ)) - σ • p.2 T‖ < ε :=
        (ENNReal.ofReal_lt_ofReal_iff hε0).1 h3
      have h5 : ‖p.1.1 (walkTop T)‖ ≤ σ * ‖p.2 T‖ + ε := by
        rw [← norm_intCast_pi]
        have := norm_le_norm_add_norm_sub' (fun i => ((p.1.1 (walkTop T) i : ℤ) : ℝ)) (σ • p.2 T)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ0] at this
        linarith
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h0 := norm_nonneg (p.1.1 (walkTop T))
      have h6 := norm_nonneg (p.2 T)
      nlinarith [sq_nonneg (σ * ‖p.2 T‖ - ε)]
  -- Step 4: integrate
  have := hQp
  have hF1ae : AEMeasurable (fun p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) =>
      ENNReal.ofReal (2 * σ ^ 2) * ENNReal.ofReal (‖p.2 T‖ ^ 2)) Q :=
    ((wiener_aemeasurable_norm_sq hQW T).comp_aemeasurable
      measurable_snd.aemeasurable).const_mul _
  have hint1 : ∫⁻ p : WalkPath d T × C(ℝ≥0, Fin d → ℝ),
      ENNReal.ofReal (2 * σ ^ 2) * ENNReal.ofReal (‖p.2 T‖ ^ 2) ∂Q ≤
      ENNReal.ofReal (2 * σ ^ 2) * ENNReal.ofReal (d * T) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    have := lintegral_map' (μ := Q) (f := fun w : C(ℝ≥0, Fin d → ℝ) => ENNReal.ofReal (‖w T‖ ^ 2))
      (g := Prod.snd) (wiener_aemeasurable_norm_sq hQW T) measurable_snd.aemeasurable
    rw [← this]
    exact wiener_lintegral_norm_sq_le hQW T
  have hint3 : ∫⁻ p, Fl.indicator (fun _ => ENNReal.ofReal (K ^ 2)) p ∂Q ≤
      ENNReal.ofReal (K ^ 2) * ENNReal.ofReal η :=
    (lintegral_indicator_const_le _ _).trans (by gcongr)
  calc ∫⁻ p, G p.1.1 ∂Q
      ≤ ∫⁻ p : WalkPath d T × C(ℝ≥0, Fin d → ℝ),
        (ENNReal.ofReal (2 * σ ^ 2) * ENNReal.ofReal (‖p.2 T‖ ^ 2) +
        (ENNReal.ofReal (2 * ε ^ 2) + Fl.indicator (fun _ => ENNReal.ofReal (K ^ 2)) p)) ∂Q :=
        lintegral_mono hpt
    _ = ∫⁻ p : WalkPath d T × C(ℝ≥0, Fin d → ℝ),
          ENNReal.ofReal (2 * σ ^ 2) * ENNReal.ofReal (‖p.2 T‖ ^ 2) ∂Q +
        (ENNReal.ofReal (2 * ε ^ 2) +
          ∫⁻ p, Fl.indicator (fun _ => ENNReal.ofReal (K ^ 2)) p ∂Q) := by
        rw [lintegral_add_left' hF1ae, lintegral_add_left measurable_const]
        simp
    _ ≤ ENNReal.ofReal (2 * σ ^ 2) * ENNReal.ofReal (d * T) +
        (ENNReal.ofReal (2 * ε ^ 2) + ENNReal.ofReal (K ^ 2) * ENNReal.ofReal η) := by
        gcongr
    _ = ENNReal.ofReal (2 * σ ^ 2 * (d * T) + (2 * ε ^ 2 + K ^ 2 * η)) := by
        have hη0 : 0 ≤ η := (Real.exp_pos _).le
        have hk0 : 0 ≤ K ^ 2 * η := mul_nonneg (sq_nonneg K) hη0
        have h2e : 0 ≤ 2 * ε ^ 2 := by positivity
        have e1 : ENNReal.ofReal (2 * ε ^ 2 + K ^ 2 * η) =
            ENNReal.ofReal (2 * ε ^ 2) + ENNReal.ofReal (K ^ 2) * ENNReal.ofReal η := by
          rw [ENNReal.ofReal_add h2e hk0, ENNReal.ofReal_mul (sq_nonneg K)]
        have e2 : ENNReal.ofReal (2 * σ ^ 2 * (d * T) + (2 * ε ^ 2 + K ^ 2 * η)) =
            ENNReal.ofReal (2 * σ ^ 2) * ENNReal.ofReal (d * T) +
              ENNReal.ofReal (2 * ε ^ 2 + K ^ 2 * η) := by
          rw [ENNReal.ofReal_add (by positivity) (add_nonneg h2e hk0),
            ENNReal.ofReal_mul (by positivity)]
        rw [e2, e1]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hεsq : ε ^ 2 = h ^ (2 * indThetaH) := by
          rw [hε, ← Real.rpow_natCast, ← Real.rpow_mul hh0.le]
          norm_num [mul_comm]
        rw [hεsq, hTc]
        have : 2 * σ ^ 2 * (d * h) ≤ 6 * d * h := by
          have hd : (0 : ℝ) ≤ d * h := by positivity
          nlinarith
        linarith

end ElboimSly.Paper
