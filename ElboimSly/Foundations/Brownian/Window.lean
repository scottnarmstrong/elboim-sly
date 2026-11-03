/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Sup
public import ElboimSly.Foundations.Brownian.Density
public import ElboimSly.Foundations.Brownian.Measurability
public import ElboimSly.Foundations.Brownian.Stopping
public import ElboimSly.Foundations.Brownian.HitCalc
import Mathlib

/-!
# One time window

One time window.

* `winG`: the function `g_{r,h}`;
* `window_hit_le`: (a);
* `window_shift_le`: (b);
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- One time window. The function `g_{r,h}(ρ) = 1` for `ρ ≤ r` and
`min 1 (4 d exp(-(ρ-r)²/(2h)))` for `ρ > r`, with values in `[0,1] ⊆ [0,∞]`. -/
noncomputable def winG (d : ℕ) (r h ρ : ℝ) : ℝ≥0∞ :=
  if ρ ≤ r then 1 else min 1 (ENNReal.ofReal (4 * d * Real.exp (-(ρ - r) ^ 2 / (2 * h))))

lemma winG_le_one (d : ℕ) (r h ρ : ℝ) : winG d r h ρ ≤ 1 := by
  unfold winG
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma winG_of_lt {d : ℕ} {r h ρ : ℝ} (hρ : r < ρ) :
    winG d r h ρ = min 1 (ENNReal.ofReal (4 * d * Real.exp (-(ρ - r) ^ 2 / (2 * h)))) := by
  simp [winG, not_le.2 hρ]

lemma ofReal_four_mul (d : ℕ) (x : ℝ) :
    ENNReal.ofReal (4 * d * x) = (4 * d : ℝ≥0∞) * ENNReal.ofReal x := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  simp

/-- One time window (a). -/
theorem window_hit_le [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)}
    (hB : IsStandardBrownianMotion d B P) (z : Fin d → ℝ) (r : ℝ) {h : ℝ≥0} (hh : h ≠ 0) :
    P {ω | ∃ u ≤ h, ‖z + B u ω‖ ≤ r} ≤ winG d r h ‖z‖ := by
  by_cases hz : ‖z‖ ≤ r
  · simp only [winG, hz, ite_true]
    exact prob_le_one
  · have hz := not_le.1 hz
    rw [winG_of_lt hz]
    refine le_min prob_le_one ?_
    have hl : 0 < ‖z‖ - r := sub_pos.2 hz
    rw [ofReal_four_mul]
    refine le_trans (measure_mono ?_) (hB.sup_norm_le hh hl)
    rintro ω ⟨u, huh, hu⟩
    refine ⟨u, huh, ?_⟩
    have := norm_sub_norm_le z (-B u ω)
    rw [norm_neg, sub_neg_eq_add] at this
    linarith

/-- The set of pairs `(z, w)` of a point and a path such that the infimum of `‖w u + z‖` over the
countable dense subset of `[0,h]` is at most `r`. -/
def winSet (d : ℕ) (h : ℝ≥0) (r : ℝ) : Set ((Fin d → ℝ) × PathSpace d) :=
  {p | ⨅ u ∈ denseSub (Set.Icc (0 : ℝ≥0) h), ((‖p.2 u + p.1‖ : ℝ) : EReal) ≤ (r : EReal)}

lemma measurableSet_winSet (d : ℕ) (h : ℝ≥0) (r : ℝ) : MeasurableSet (winSet d h r) := by
  have : Measurable fun p : (Fin d → ℝ) × PathSpace d =>
      ⨅ u ∈ denseSub (Set.Icc (0 : ℝ≥0) h), (((fun q : (Fin d → ℝ) × (Fin d → ℝ) => ‖q.2 + q.1‖)
        (p.1, p.2 u) : ℝ) : EReal) :=
    measurable_biInf_path (denseSub_countable _) (Γ₀ := fun q => ‖q.2 + q.1‖)
      (by fun_prop)
  exact measurableSet_le this measurable_const

lemma mk_mem_winSet_iff {w : PathSpace d} (hw : Continuous w) (z : Fin d → ℝ) (h : ℝ≥0) (r : ℝ) :
    (z, w) ∈ winSet d h r ↔ ∃ u ∈ Set.Icc (0 : ℝ≥0) h, ‖w u + z‖ ≤ r := by
  have := exists_mem_le_iff_iInf_le (J := Set.Icc (0 : ℝ≥0) h) Set.ordConnected_Icc isCompact_Icc
    ⟨0, le_rfl, zero_le⟩ hw (-z) r
  simp only [sub_neg_eq_add] at this
  exact this.symm

/-- One time window (b). -/
theorem window_shift_le [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)}
    (hB : IsStandardBrownianMotion d B P) (a : ℝ≥0) {h : ℝ≥0} (hh : h ≠ 0) (y : Fin d → ℝ)
    (r : ℝ) :
    P {ω | ∃ u, a ≤ u ∧ u ≤ a + h ∧ ‖y + B u ω‖ ≤ r} ≤
      ∫⁻ ω, winG d r h ‖y + B a ω‖ ∂P := by
  let Φ : (Fin d → ℝ) → PathSpace d → ℝ≥0∞ := fun z w => (winSet d h r).indicator 1 (z, w)
  have hΦ : Measurable (Function.uncurry Φ) := by
    have : Function.uncurry Φ = (winSet d h r).indicator 1 := by
      funext ⟨z, w⟩; rfl
    rw [this]
    exact measurable_one.indicator (measurableSet_winSet d h r)
  have hZ : Measurable[bmFiltration B a] (fun ω => y + B a ω) :=
    (measurable_bmFiltration (B := B) le_rfl).const_add y
  have key := hB.lintegral_indicator_shift a hZ (A := Set.univ)
    (@MeasurableSet.univ Ω (bmFiltration B a)) hΦ
  simp only [Set.indicator_univ] at key
  let T : Set Ω := {ω | (y + B a ω, shiftPath B a ω) ∈ winSet d h r}
  have hT : MeasurableSet T :=
    ((measurable_const.add (hB.measurable a)).prodMk (measurable_shiftPath hB.measurable a))
      (measurableSet_winSet d h r)
  have hsub : {ω | ∃ u, a ≤ u ∧ u ≤ a + h ∧ ‖y + B u ω‖ ≤ r} ⊆ T := by
    rintro ω ⟨u, hau, hua, hu⟩
    have hcont : Continuous (shiftPath B a ω) := by
      have := (hB.continuous_zero ω).1
      exact (this.comp (continuous_const.add continuous_id)).sub continuous_const
    show (y + B a ω, shiftPath B a ω) ∈ winSet d h r
    rw [mk_mem_winSet_iff hcont]
    refine ⟨u - a, ⟨zero_le, ?_⟩, ?_⟩
    · exact tsub_le_iff_left.2 hua
    · simp only [shiftPath, add_tsub_cancel_of_le hau]
      convert hu using 2
      abel
  have hTeq : P T = ∫⁻ ω, Φ (y + B a ω) (shiftPath B a ω) ∂P := by
    rw [← lintegral_indicator_one hT]
    rfl
  calc _ ≤ P T := measure_mono hsub
    _ = _ := hTeq
    _ = _ := key
    _ ≤ _ := by
      refine lintegral_mono fun ω => ?_
      have hfib : ∫⁻ w, Φ (y + B a ω) w ∂(wienerMeasure d) =
          wienerMeasure d (Prod.mk (y + B a ω) ⁻¹' winSet d h r) := by
        have : Φ (y + B a ω) = (Prod.mk (y + B a ω) ⁻¹' winSet d h r).indicator 1 := by
          funext w; rfl
        rw [this, lintegral_indicator_one (measurable_prodMk_left (measurableSet_winSet d h r))]
      rw [hfib, ← hB.map_pathMap_eq_wiener,
        Measure.map_apply hB.measurable_pathMap (measurable_prodMk_left (measurableSet_winSet d h r))]
      refine le_trans (measure_mono ?_) (window_hit_le hB (y + B a ω) r hh)
      intro ω' hω'
      have hcont : Continuous (pathMap B ω') := continuous_path hB ω'
      obtain ⟨u, hu, hu'⟩ := (mk_mem_winSet_iff hcont _ h r).1 hω'
      exact ⟨u, hu.2, by simpa only [pathMap, add_comm] using hu'⟩

end ElboimSly.Brownian
