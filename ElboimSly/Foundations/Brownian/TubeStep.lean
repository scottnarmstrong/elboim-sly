/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Sup
public import ElboimSly.Foundations.Brownian.Measurability
public import ElboimSly.Foundations.Brownian.Freeze
public import ElboimSly.Foundations.Brownian.PathDense
import Mathlib

/-!
# One step of the tube lemma

Tube lemma, basic form, "One step", and one-dimensional Gaussian bounds (c).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

/-- One-dimensional Gaussian bounds (c), with a general bound `M` on `x²` over the interval. -/
lemma gaussian_Icc_ge {v : ℝ≥0} (hv : v ≠ 0) {α α' M : ℝ} (hαα' : α ≤ α')
    (hM : ∀ x ∈ Set.Icc α α', x ^ 2 ≤ M) :
    ENNReal.ofReal ((α' - α) * ((Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-M / (2 * v)))) ≤
      gaussianReal 0 v (Set.Icc α α') := by
  rw [gaussianReal_apply_eq_integral 0 hv]
  refine ENNReal.ofReal_le_ofReal ?_
  have hvpos : (0 : ℝ) < v := by positivity
  have h := setIntegral_ge_of_const_le (μ := volume) (s := Set.Icc α α')
    (c := (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-M / (2 * v))) measurableSet_Icc
    (by simp) (f := gaussianPDFReal 0 v) ?_ (integrable_gaussianPDFReal 0 v).integrableOn
  · simpa [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.2 hαα')] using h
  · intro x hx
    rw [gaussianPDFReal_def]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    simp only [sub_zero]
    have := hM x hx
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The coordinate path set `{w : sup over the countable dense subset of [0,h] of |w| ≤ a,
|w(h) - p| ≤ b}`. -/
def coordSet (h : ℝ≥0) (a b p : ℝ) : Set (ℝ≥0 → ℝ) :=
  {w | (∀ v ∈ denseSub (Set.Icc (0 : ℝ≥0) h), |w v| ≤ a) ∧ |w h - p| ≤ b}

lemma measurableSet_coordSet (h : ℝ≥0) (a b p : ℝ) : MeasurableSet (coordSet h a b p) := by
  have e : coordSet h a b p = (⋂ v ∈ denseSub (Set.Icc (0 : ℝ≥0) h), {w : ℝ≥0 → ℝ | |w v| ≤ a}) ∩
      {w : ℝ≥0 → ℝ | |w h - p| ≤ b} := by
    ext w; simp [coordSet]
  rw [e]
  refine (MeasurableSet.biInter (denseSub_countable _) fun v _ => ?_).inter ?_
  · exact measurableSet_le (by fun_prop : Measurable fun w : ℝ≥0 → ℝ => |w v|) measurable_const
  · exact measurableSet_le (by fun_prop : Measurable fun w : ℝ≥0 → ℝ => |w h - p|) measurable_const

lemma real_arith_step {Λ ρ h : ℝ} (hρ : 0 < ρ) (hh : 0 < h) (hΛ : Λ = ρ ^ 2 / h) (hΛ0 : 16000 ≤ Λ) :
    5 ≤ ρ / 10 * (Real.sqrt (2 * Real.pi * h))⁻¹ := by
  have hπ := Real.pi_lt_d2
  have h1 : 50 * Real.sqrt (2 * Real.pi * h) ≤ ρ := by
    have : (50 * Real.sqrt (2 * Real.pi * h)) ^ 2 ≤ ρ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      rw [hΛ, le_div_iff₀ hh] at hΛ0
      nlinarith [Real.pi_pos]
    exact abs_le_of_sq_le_sq' this hρ.le |>.2
  have hs : 0 < Real.sqrt (2 * Real.pi * h) := Real.sqrt_pos.2 (by positivity)
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  nlinarith

/-- Tube lemma, basic form, "One step": one coordinate. For `|p| ≤ 3ρ/20` and
`ρ²/h ≥ 16000`, the coordinate event `{sup_{v ≤ h} |B^i(v)| ≤ ρ/4, |B^i(h) - p| ≤ ρ/20}` has
probability at least `exp(-(ρ²/h)/50)`. -/
theorem coord_factor_ge [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)}
    (hB : IsStandardBrownianMotion d B P) (i : Fin d) {h : ℝ≥0} (hh : h ≠ 0) {ρ p : ℝ}
    (hρ : 0 < ρ) (hp : |p| ≤ 3 * ρ / 20) (hΛ : 16000 ≤ ρ ^ 2 / h) :
    ENNReal.ofReal (Real.exp (-(ρ ^ 2 / h) / 50)) ≤
      P {ω | (fun t => B t ω i) ∈ coordSet h (ρ / 4) (ρ / 20) p} := by
  have hhpos : (0 : ℝ) < h := by positivity
  set Λ : ℝ := ρ ^ 2 / h with hΛdef
  set X : Set Ω := {ω | |B h ω i - p| ≤ ρ / 20} with hX
  set Y : Set Ω := {ω | ∀ v ∈ denseSub (Set.Icc (0 : ℝ≥0) h), |B v ω i| ≤ ρ / 4} with hY
  have hset : {ω | (fun t => B t ω i) ∈ coordSet h (ρ / 4) (ρ / 20) p} = Y ∩ X := by
    ext ω; simp [coordSet, hX, hY]
  have hlaw := (hB.isPreBrownianReal i).hasLaw_eval h
  have hPX : ENNReal.ofReal (ρ / 10 * (Real.sqrt (2 * Real.pi * h))⁻¹ * Real.exp (-Λ / 50)) ≤ P X := by
    have e : X = (fun ω => B h ω i) ⁻¹' Set.Icc (p - ρ / 20) (p + ρ / 20) := by
      ext ω
      simp only [hX, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, abs_le]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    have hG := gaussian_Icc_ge (v := h) hh (α := p - ρ / 20) (α' := p + ρ / 20)
      (M := (ρ / 5) ^ 2) (by linarith) (by
        intro x hx
        have h1 : |x| ≤ ρ / 5 := by
          rw [abs_le]; constructor <;> [skip; skip] <;>
          · have := (abs_le.1 hp); linarith [hx.1, hx.2]
        nlinarith [abs_nonneg x, sq_abs x])
    rw [e, ← Measure.map_apply (hB.measurable h |>.eval) measurableSet_Icc, hlaw.map_eq]
    refine le_trans (le_of_eq ?_) hG
    congr 1
    have : -((ρ / 5) ^ 2) / (2 * (h : ℝ)) = -Λ / 50 := by
      rw [hΛdef]; field_simp; ring
    rw [this]; ring
  have hPY : P Yᶜ ≤ ENNReal.ofReal (4 * Real.exp (-(ρ / 4) ^ 2 / (2 * h))) := by
    have hsub : Yᶜ ⊆ {ω | ∃ u ≤ h, ρ / 4 ≤ B u ω i} ∪
        {ω | ∃ u ≤ h, ρ / 4 ≤ (fun t ω k => -B t ω k) u ω i} := by
      intro ω hω
      simp only [hY, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨v, hv, hlt⟩ := hω
      have hvh : v ≤ h := (denseSub_subset _ hv).2
      rcases lt_abs.1 hlt with h1 | h1
      · exact Or.inl ⟨v, hvh, h1.le⟩
      · exact Or.inr ⟨v, hvh, by simp only; linarith⟩
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have h1 := hB.sup_coord_le i hh (l := ρ / 4) (by positivity)
    have h2 := hB.neg.sup_coord_le i hh (l := ρ / 4) (by positivity)
    refine (add_le_add h1 h2).trans (le_of_eq ?_)
    rw [← two_mul, ← mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    norm_num
  have hbound : ρ / 10 * (Real.sqrt (2 * Real.pi * h))⁻¹ * Real.exp (-Λ / 50) -
      4 * Real.exp (-(ρ / 4) ^ 2 / (2 * h)) ≥ Real.exp (-Λ / 50) := by
    have h5 := real_arith_step hρ hhpos hΛdef hΛ
    have e : -(ρ / 4) ^ 2 / (2 * (h : ℝ)) = -Λ / 32 := by rw [hΛdef]; field_simp; ring
    have h6 : Real.exp (-Λ / 32) ≤ Real.exp (-Λ / 50) :=
      Real.exp_le_exp.2 (by linarith)
    rw [e]
    nlinarith [Real.exp_pos (-Λ / 50)]
  rw [hset]
  have hle : P X ≤ P (Y ∩ X) + P Yᶜ := by
    refine (measure_mono (fun ω hω => ?_)).trans (measure_union_le _ _)
    by_cases hy : ω ∈ Y
    · exact Or.inl ⟨hy, hω⟩
    · exact Or.inr hy
  have h3 : ENNReal.ofReal (ρ / 10 * (Real.sqrt (2 * Real.pi * h))⁻¹ * Real.exp (-Λ / 50)) ≤
      P (Y ∩ X) + ENNReal.ofReal (4 * Real.exp (-(ρ / 4) ^ 2 / (2 * h))) :=
    hPX.trans (hle.trans (add_le_add le_rfl hPY))
  have h4 : ENNReal.ofReal (ρ / 10 * (Real.sqrt (2 * Real.pi * h))⁻¹ * Real.exp (-Λ / 50)
      - 4 * Real.exp (-(ρ / 4) ^ 2 / (2 * h))) ≤ P (Y ∩ X) := by
    rw [ENNReal.ofReal_sub _ (by positivity)]
    exact tsub_le_iff_right.2 h3
  exact (ENNReal.ofReal_le_ofReal hbound).trans h4

/-- The step set `{(p, w) : sup_{v ≤ h} ‖w(v)‖ ≤ a, ‖w(h) - p‖ ≤ b}` (countable dense subset of
`[0,h]` for the supremum). -/
def stepSet (d : ℕ) (h : ℝ≥0) (a b : ℝ) : Set ((Fin d → ℝ) × PathSpace d) :=
  {q | (∀ v ∈ denseSub (Set.Icc (0 : ℝ≥0) h), ‖q.2 v‖ ≤ a) ∧ ‖q.2 h - q.1‖ ≤ b}

lemma measurableSet_stepSet (d : ℕ) (h : ℝ≥0) (a b : ℝ) : MeasurableSet (stepSet d h a b) := by
  have e : stepSet d h a b =
      (⋂ v ∈ denseSub (Set.Icc (0 : ℝ≥0) h), {q : (Fin d → ℝ) × PathSpace d | ‖q.2 v‖ ≤ a}) ∩
      {q : (Fin d → ℝ) × PathSpace d | ‖q.2 h - q.1‖ ≤ b} := by
    ext q; simp [stepSet]
  rw [e]
  refine (MeasurableSet.biInter (denseSub_countable _) fun v _ => ?_).inter ?_
  · exact measurableSet_le (by fun_prop : Measurable fun q : (Fin d → ℝ) × PathSpace d => ‖q.2 v‖)
      measurable_const
  · exact measurableSet_le
      (by fun_prop : Measurable fun q : (Fin d → ℝ) × PathSpace d => ‖q.2 h - q.1‖) measurable_const

/-- Tube lemma, basic form, "One step". For `‖p‖ ≤ 3ρ/20` and `ρ²/h ≥ 16000`,
`P(B ∈ 𝔄(p)) ≥ exp(-(ρ²/h)/50)^d`. -/
theorem step_ge [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)}
    (hB : IsStandardBrownianMotion d B P) {h : ℝ≥0} (hh : h ≠ 0) {ρ : ℝ} (hρ : 0 < ρ)
    {p : Fin d → ℝ} (hp : ‖p‖ ≤ 3 * ρ / 20) (hΛ : 16000 ≤ ρ ^ 2 / h) :
    ENNReal.ofReal (Real.exp (-(ρ ^ 2 / h) / 50)) ^ d ≤
      P {ω | (p, pathMap B ω) ∈ stepSet d h (ρ / 4) (ρ / 20)} := by
  have hset : {ω | (p, pathMap B ω) ∈ stepSet d h (ρ / 4) (ρ / 20)} =
      ⋂ i : Fin d, {ω | (fun t => B t ω i) ∈ coordSet h (ρ / 4) (ρ / 20) (p i)} := by
    ext ω
    simp only [stepSet, coordSet, Set.mem_ofPred_eq, Set.mem_iInter]
    have hn : ∀ x : Fin d → ℝ, ∀ r : ℝ, 0 ≤ r → (‖x‖ ≤ r ↔ ∀ i, |x i| ≤ r) := by
      intro x r hr
      rw [pi_norm_le_iff_of_nonneg hr]
      simp only [Real.norm_eq_abs]
    constructor
    · rintro ⟨h1, h2⟩ i
      refine ⟨fun v hv => ?_, ?_⟩
      · exact (hn _ _ (by positivity)).1 (h1 v hv) i
      · have := (hn _ _ (by positivity)).1 h2 i
        simpa [pathMap] using this
    · intro H
      refine ⟨fun v hv => (hn _ _ (by positivity)).2 fun i => (H i).1 v hv, ?_⟩
      refine (hn _ _ (by positivity)).2 fun i => ?_
      simpa [pathMap] using (H i).2
  have key := hB.iIndepFun.meas_iInter (μ := P)
    (s := fun i => (fun ω t => B t ω i) ⁻¹' coordSet h (ρ / 4) (ρ / 20) (p i))
    (fun i => ⟨coordSet h (ρ / 4) (ρ / 20) (p i), measurableSet_coordSet _ _ _ _, rfl⟩)
  rw [hset]
  calc ENNReal.ofReal (Real.exp (-(ρ ^ 2 / h) / 50)) ^ d
      = ∏ _i : Fin d, ENNReal.ofReal (Real.exp (-(ρ ^ 2 / h) / 50)) := by simp
    _ ≤ ∏ i : Fin d, P ((fun ω t => B t ω i) ⁻¹' coordSet h (ρ / 4) (ρ / 20) (p i)) :=
        Finset.prod_le_prod fun i _ => coord_factor_ge hB i hh hρ
          (by have := norm_le_pi_norm p i; rw [Real.norm_eq_abs] at this; linarith) hΛ
    _ = _ := key.symm

end ElboimSly.Brownian
