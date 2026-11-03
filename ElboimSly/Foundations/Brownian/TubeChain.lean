/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.TubeStep
public import ElboimSly.Foundations.Brownian.Stopping
import Mathlib

/-!
# The chain of events in the tube lemma

Tube lemma, basic form, "Bookkeeping" and "Chaining".

For a grid step `h`, the events `E_k = ⋂_{j<k} S_j`, where `S_j = {sh_{jh} B ∈ 𝔄(p_j)}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

section Abstract

variable {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}

/-- An abstract measurability statement for the one-step set, for an arbitrary `σ`-algebra `m`
in which the relevant coordinates are measurable. -/
lemma measurableSet_stepEvent {B : ℝ≥0 → Ω → (Fin d → ℝ)} {t h : ℝ≥0} {a b : ℝ}
    (hB : ∀ s ≤ t + h, Measurable (B s)) {q : Ω → (Fin d → ℝ)} (hq : Measurable q) :
    MeasurableSet {ω | (∀ v ∈ denseSub (Set.Icc (0 : ℝ≥0) h), ‖B (t + v) ω - B t ω‖ ≤ a) ∧
      ‖B (t + h) ω - B t ω - q ω‖ ≤ b} := by
  have e : {ω | (∀ v ∈ denseSub (Set.Icc (0 : ℝ≥0) h), ‖B (t + v) ω - B t ω‖ ≤ a) ∧
      ‖B (t + h) ω - B t ω - q ω‖ ≤ b} =
      (⋂ v ∈ denseSub (Set.Icc (0 : ℝ≥0) h), {ω | ‖B (t + v) ω - B t ω‖ ≤ a}) ∩
      {ω | ‖B (t + h) ω - B t ω - q ω‖ ≤ b} := by
    ext ω; simp
  rw [e]
  refine (MeasurableSet.biInter (denseSub_countable _) fun v hv => ?_).inter ?_
  · have hvh : v ≤ h := (denseSub_subset _ hv).2
    have h1 := hB (t + v) (by gcongr)
    have h2 := hB t (le_self_add)
    exact measurableSet_le ((h1.sub h2).norm) measurable_const
  · have h1 := hB (t + h) le_rfl
    have h2 := hB t (le_self_add)
    exact measurableSet_le (((h1.sub h2).sub hq).norm) measurable_const

end Abstract

/-- If a continuous function is `≤ a` on the countable dense subset of an interval, then it is
`≤ a` on the interval. -/
lemma le_on_of_denseSub {J : Set ℝ≥0} (hJ : J.OrdConnected) {g : ℝ≥0 → ℝ} (hg : Continuous g)
    {a : ℝ} (h : ∀ v ∈ denseSub J, g v ≤ a) : ∀ v ∈ J, g v ≤ a := by
  have hcl : IsClosed {t | g t ≤ a} := isClosed_le hg continuous_const
  have : denseSub J ⊆ {t | g t ≤ a} := fun v hv => h v hv
  exact fun v hv => (closure_minimal this hcl) (subset_closure_denseSub hJ hv)

section Chain

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The targets `z_k = (1 - k/12)_+ (x - f(0))` of the bookkeeping. -/
noncomputable def tubeZ (v : Fin d → ℝ) (k : ℕ) : Fin d → ℝ := max (1 - (k : ℝ) / 12) 0 • v

/-- The vector `p_k = z_{k+1} - x - B(u_k) + f(u_{k+1})`, `u_k = k h`. -/
noncomputable def tubeP (B : ℝ≥0 → Ω → (Fin d → ℝ)) (x : Fin d → ℝ) (f : ℝ → Fin d → ℝ) (h : ℝ≥0)
    (k : ℕ) (ω : Ω) : Fin d → ℝ :=
  tubeZ (x - f 0) (k + 1) - x + f (((k + 1 : ℕ) : ℝ≥0) * h : ℝ≥0) - B ((k : ℝ≥0) * h) ω

/-- The event `S_k = {sh_{u_k} B ∈ 𝔄(p_k)}`. -/
def tubeS (B : ℝ≥0 → Ω → (Fin d → ℝ)) (x : Fin d → ℝ) (f : ℝ → Fin d → ℝ) (h : ℝ≥0) (ρ : ℝ)
    (k : ℕ) : Set Ω :=
  {ω | (tubeP B x f h k ω, shiftPath B ((k : ℝ≥0) * h) ω) ∈ stepSet d h (ρ / 4) (ρ / 20)}

/-- The events `E_k = ⋂_{j<k} S_j`. -/
def tubeE (B : ℝ≥0 → Ω → (Fin d → ℝ)) (x : Fin d → ℝ) (f : ℝ → Fin d → ℝ) (h : ℝ≥0) (ρ : ℝ) :
    ℕ → Set Ω
  | 0 => Set.univ
  | k + 1 => tubeE B x f h ρ k ∩ tubeS B x f h ρ k

variable {B : ℝ≥0 → Ω → (Fin d → ℝ)} {x : Fin d → ℝ} {f : ℝ → Fin d → ℝ} {h : ℝ≥0} {ρ : ℝ}

lemma succ_mul_eq (k : ℕ) (h : ℝ≥0) : ((k + 1 : ℕ) : ℝ≥0) * h = (k : ℝ≥0) * h + h := by
  push_cast; ring

lemma measurable_tubeP (_hB : ∀ t, Measurable (B t)) (k : ℕ) :
    Measurable[bmFiltration B ((k : ℝ≥0) * h)] (tubeP B x f h k) := by
  unfold tubeP
  exact Measurable.const_sub (measurable_bmFiltration (B := B) (s := (k : ℝ≥0) * h) le_rfl) _

omit mΩ in
lemma tubeS_eq (k : ℕ) : tubeS B x f h ρ k =
    {ω | (∀ v ∈ denseSub (Set.Icc (0 : ℝ≥0) h),
        ‖B ((k : ℝ≥0) * h + v) ω - B ((k : ℝ≥0) * h) ω‖ ≤ ρ / 4) ∧
      ‖B ((k : ℝ≥0) * h + h) ω - B ((k : ℝ≥0) * h) ω - tubeP B x f h k ω‖ ≤ ρ / 20} := by
  ext ω
  simp [tubeS, stepSet, shiftPath]

lemma measurableSet_tubeS (hB : ∀ t, Measurable (B t)) (k : ℕ) :
    MeasurableSet[bmFiltration B (((k + 1 : ℕ) : ℝ≥0) * h)] (tubeS B x f h ρ k) := by
  rw [tubeS_eq]
  have hm : ∀ s ≤ (k : ℝ≥0) * h + h, Measurable[bmFiltration B (((k + 1 : ℕ) : ℝ≥0) * h)] (B s) :=
    fun s hs => measurable_bmFiltration (by rw [succ_mul_eq]; exact hs)
  have hq : Measurable[bmFiltration B (((k + 1 : ℕ) : ℝ≥0) * h)] (tubeP B x f h k) :=
    Measurable.mono (measurable_tubeP hB k) (bmFiltration_mono B (by rw [succ_mul_eq]; exact le_self_add)) le_rfl
  exact @measurableSet_stepEvent Ω (bmFiltration B (((k + 1 : ℕ) : ℝ≥0) * h)) d B _ h _ _ hm _ hq

lemma measurableSet_tubeE (hB : ∀ t, Measurable (B t)) (k : ℕ) :
    MeasurableSet[bmFiltration B ((k : ℝ≥0) * h)] (tubeE B x f h ρ k) := by
  induction k with
  | zero => exact @MeasurableSet.univ Ω (bmFiltration B ((0 : ℕ) * h))
  | succ k ih =>
    have hmono : bmFiltration B ((k : ℝ≥0) * h) ≤ bmFiltration B (((k + 1 : ℕ) : ℝ≥0) * h) :=
      bmFiltration_mono B (by rw [succ_mul_eq]; exact le_self_add)
    exact @MeasurableSet.inter Ω (bmFiltration B (((k + 1 : ℕ) : ℝ≥0) * h)) _ _
      (hmono _ ih) (measurableSet_tubeS hB k)

/-- Tube lemma, basic form, "Chaining": `P(E_{k+1}) ≥ q P(E_k)`. -/
theorem tubeE_succ_prob [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P)
    (hh : h ≠ 0) (hρ : 0 < ρ) (hΛ : 16000 ≤ ρ ^ 2 / h) (k : ℕ)
    (hp : ∀ ω ∈ tubeE B x f h ρ k, ‖tubeP B x f h k ω‖ ≤ 3 * ρ / 20) :
    ENNReal.ofReal (Real.exp (-(ρ ^ 2 / h) / 50)) ^ d * P (tubeE B x f h ρ k) ≤
      P (tubeE B x f h ρ (k + 1)) := by
  set Φ : (Fin d → ℝ) → PathSpace d → ℝ≥0∞ := fun p w =>
    (stepSet d h (ρ / 4) (ρ / 20)).indicator 1 (p, w) with hΦdef
  have hΦ : Measurable (Function.uncurry Φ) := by
    have : Function.uncurry Φ = (stepSet d h (ρ / 4) (ρ / 20)).indicator 1 := by
      funext ⟨z, w⟩; rfl
    rw [this]
    exact measurable_one.indicator (measurableSet_stepSet d h _ _)
  have hZ := measurable_tubeP (x := x) (f := f) (h := h) hB.measurable k
  have hA := measurableSet_tubeE (x := x) (f := f) (h := h) (ρ := ρ) hB.measurable k
  have key := hB.lintegral_indicator_shift ((k : ℝ≥0) * h) hZ hA hΦ
  have hE1 : MeasurableSet (tubeE B x f h ρ (k + 1)) :=
    bmFiltration_le hB.measurable _ _ (measurableSet_tubeE hB.measurable (k + 1))
  have hlhs : ∫⁻ ω, (tubeE B x f h ρ k).indicator
      (fun ω => Φ (tubeP B x f h k ω) (shiftPath B ((k : ℝ≥0) * h) ω)) ω ∂P =
      P (tubeE B x f h ρ (k + 1)) := by
    rw [← lintegral_indicator_one hE1]
    refine lintegral_congr fun ω => ?_
    by_cases h1 : ω ∈ tubeE B x f h ρ k
    · by_cases h2 : ω ∈ tubeS B x f h ρ k
      · have h3 : ω ∈ tubeE B x f h ρ (k + 1) := ⟨h1, h2⟩
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem h3]
        exact Set.indicator_of_mem (show (tubeP B x f h k ω, shiftPath B ((k : ℝ≥0) * h) ω) ∈
          stepSet d h (ρ / 4) (ρ / 20) from h2) _
      · have h3 : ω ∉ tubeE B x f h ρ (k + 1) := fun hh' => h2 hh'.2
        rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h3]
        exact Set.indicator_of_notMem (show (tubeP B x f h k ω, shiftPath B ((k : ℝ≥0) * h) ω) ∉
          stepSet d h (ρ / 4) (ρ / 20) from h2) _
    · have h3 : ω ∉ tubeE B x f h ρ (k + 1) := fun hh' => h1 hh'.1
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h3]
  have hA' : MeasurableSet (tubeE B x f h ρ k) :=
    bmFiltration_le hB.measurable _ _ hA
  calc _ = ∫⁻ ω, (tubeE B x f h ρ k).indicator
        (fun _ => ENNReal.ofReal (Real.exp (-(ρ ^ 2 / h) / 50)) ^ d) ω ∂P := by
        rw [lintegral_indicator_const hA', mul_comm]
    _ ≤ ∫⁻ ω, (tubeE B x f h ρ k).indicator
        (fun ω => ∫⁻ w, Φ (tubeP B x f h k ω) w ∂(wienerMeasure d)) ω ∂P := by
        refine lintegral_mono fun ω => ?_
        by_cases h1 : ω ∈ tubeE B x f h ρ k
        · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h1]
          have hfib : MeasurableSet (Prod.mk (tubeP B x f h k ω) ⁻¹' stepSet d h (ρ / 4) (ρ / 20)) :=
            measurable_prodMk_left (measurableSet_stepSet d h _ _)
          have e : Φ (tubeP B x f h k ω) = (Prod.mk (tubeP B x f h k ω) ⁻¹'
              stepSet d h (ρ / 4) (ρ / 20)).indicator 1 := by
            funext w; rfl
          rw [e, lintegral_indicator_one hfib, ← hB.map_pathMap_eq_wiener,
            Measure.map_apply hB.measurable_pathMap hfib]
          exact step_ge hB hh hρ (hp ω h1) hΛ
        · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h1]
    _ = _ := by rw [← key, hlhs]

end Chain


end ElboimSly.Brownian
