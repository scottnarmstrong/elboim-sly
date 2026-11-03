/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.TubeBasic
import Mathlib

/-!
# The tube lemma

Tube lemma, proved from tube lemma, basic form in
two phases, using the Markov property at time `T/2`.

* `ctube d K = c₀(d,8K) c₀(d,52K)`;
* `tube2Set`: the path set `𝔗`, defined with countable dense time sets;
* `tube_lemma`: `P(B ∈ 𝔗) ≥ c_tube(d,K)`;
* `tube_event_eq`: for continuous paths, membership in `𝔗` is the event of the lemma.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

/-- Tube lemma. `c_tube(d,K) = c₀(d,8K) c₀(d,52K)`. -/
noncomputable def ctube (d : ℕ) (K : ℝ) : ℝ := tubeC0 d (8 * K) * tubeC0 d (52 * K)

/-- Tube lemma. The path set `𝔗`: with `t = T/2`, within `ρ` of `f` on the
countable dense subset of `[0,t]`, and within `ρ/5` of `f` at times `t + v`, `v` in the countable
dense subset of `[0,t]`. -/
def tube2Set (d : ℕ) (σ : ℝ) (x : Fin d → ℝ) (f : ℝ → Fin d → ℝ) (ρ : ℝ) (T : ℝ≥0) :
    Set (PathSpace d) :=
  {w | (∀ u ∈ denseSub (Set.Icc (0 : ℝ≥0) (T / 2)), ‖x + σ • w u - f u‖ ≤ ρ) ∧
    (∀ v ∈ denseSub (Set.Icc (0 : ℝ≥0) (T / 2)),
      ‖x + σ • w (T / 2 + v) - f ((T / 2 + v : ℝ≥0) : ℝ)‖ ≤ ρ / 5)}

lemma measurableSet_tube2Set (d : ℕ) (σ : ℝ) (x : Fin d → ℝ) (f : ℝ → Fin d → ℝ) (ρ : ℝ)
    (T : ℝ≥0) : MeasurableSet (tube2Set d σ x f ρ T) := by
  have e : tube2Set d σ x f ρ T =
      (⋂ u ∈ denseSub (Set.Icc (0 : ℝ≥0) (T / 2)), {w : PathSpace d | ‖x + σ • w u - f u‖ ≤ ρ}) ∩
      (⋂ v ∈ denseSub (Set.Icc (0 : ℝ≥0) (T / 2)),
        {w : PathSpace d | ‖x + σ • w (T / 2 + v) - f ((T / 2 + v : ℝ≥0) : ℝ)‖ ≤ ρ / 5}) := by
    ext w; simp [tube2Set]
  rw [e]
  refine (MeasurableSet.biInter (denseSub_countable _) fun u _ => ?_).inter
    (MeasurableSet.biInter (denseSub_countable _) fun v _ => ?_)
  · exact measurableSet_le
      (by fun_prop : Measurable fun w : PathSpace d => ‖x + σ • w u - f u‖) measurable_const
  · exact measurableSet_le
      (by fun_prop : Measurable fun w : PathSpace d =>
        ‖x + σ • w (T / 2 + v) - f ((T / 2 + v : ℝ≥0) : ℝ)‖) measurable_const

/-- If a function is continuous on a closed interval and `≤ a` on its countable dense subset,
then it is `≤ a` on the interval. -/
lemma le_on_of_denseSub_continuousOn {J : Set ℝ≥0} (hJ : J.OrdConnected) (hJc : IsClosed J)
    {g : ℝ≥0 → ℝ} (hg : ContinuousOn g J) {a : ℝ} (h : ∀ v ∈ denseSub J, g v ≤ a) :
    ∀ v ∈ J, g v ≤ a := by
  have hcl : IsClosed (J ∩ g ⁻¹' Set.Iic a) :=
    hg.preimage_isClosed_of_isClosed hJc isClosed_Iic
  have : denseSub J ⊆ J ∩ g ⁻¹' Set.Iic a := fun v hv => ⟨denseSub_subset J hv, h v hv⟩
  exact fun v hv => ((closure_minimal this hcl) (subset_closure_denseSub hJ hv)).2

lemma cont_aux {d : ℕ} {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) (σ : ℝ) (x : Fin d → ℝ)
    {F : ℝ≥0 → Fin d → ℝ} {J : Set ℝ≥0} (hF : ContinuousOn F J) :
    ContinuousOn (fun u => ‖x + σ • w u - F u‖) J :=
  (((continuous_const.add (hw.const_smul σ)).continuousOn).sub hF).norm

/-- For continuous paths, membership in `𝔗` is the event of tube lemma. -/
theorem mem_tube2Set_iff {d : ℕ} {w : PathSpace d} (hw : Continuous w) (σ : ℝ)
    (x : Fin d → ℝ) {f : ℝ → Fin d → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) {T : ℝ≥0}
    (hfc : ContinuousOn f (Set.Icc (0 : ℝ) T)) :
    w ∈ tube2Set d σ x f ρ T ↔
      (∀ u : ℝ≥0, u ≤ T → ‖x + σ • w u - f u‖ ≤ ρ) ∧
      (∀ u : ℝ≥0, T / 2 ≤ u → u ≤ T → ‖x + σ • w u - f u‖ ≤ ρ / 5) := by
  have hTT : (T / 2 : ℝ≥0) ≤ T := by
    rw [← NNReal.coe_le_coe]; push_cast; linarith [T.2]
  have hcoe : ((T / 2 : ℝ≥0) : ℝ) + ((T / 2 : ℝ≥0) : ℝ) = T := by push_cast; ring
  constructor
  · rintro ⟨H1, H2⟩
    -- continuity of the two comparison functions
    have hc1 : ContinuousOn (fun u : ℝ≥0 => f (u : ℝ)) (Set.Icc 0 (T / 2)) :=
      hfc.comp NNReal.continuous_coe.continuousOn (fun u hu => ⟨u.2, by
        have := hu.2; rw [← NNReal.coe_le_coe] at this; exact this.trans (by exact_mod_cast hTT)⟩)
    have hg1 := cont_aux hw σ x hc1
    have hc2 : ContinuousOn (fun v : ℝ≥0 => f ((T / 2 + v : ℝ≥0) : ℝ)) (Set.Icc 0 (T / 2)) :=
      hfc.comp (NNReal.continuous_coe.comp (continuous_const.add continuous_id)).continuousOn
        (fun v hv => ⟨NNReal.coe_nonneg _, by
          have := hv.2; rw [← NNReal.coe_le_coe] at this; push_cast at this ⊢; linarith⟩)
    have hw2 : Continuous fun v : ℝ≥0 => w (T / 2 + v) := hw.comp (continuous_const.add continuous_id)
    have hg2 := cont_aux hw2 σ x hc2
    have A1 := le_on_of_denseSub_continuousOn Set.ordConnected_Icc isClosed_Icc hg1 H1
    have A2 := le_on_of_denseSub_continuousOn Set.ordConnected_Icc isClosed_Icc hg2 H2
    have second : ∀ u : ℝ≥0, T / 2 ≤ u → u ≤ T → ‖x + σ • w u - f u‖ ≤ ρ / 5 := by
      intro u hu1 hu2
      have hv : u - T / 2 ∈ Set.Icc (0 : ℝ≥0) (T / 2) := by
        refine ⟨zero_le, ?_⟩
        rw [tsub_le_iff_left]
        rw [← NNReal.coe_le_coe]; push_cast
        have := (NNReal.coe_le_coe.2 hu2); linarith
      have := A2 _ hv
      rwa [add_tsub_cancel_of_le hu1] at this
    refine ⟨fun u hu => ?_, second⟩
    by_cases hut : u ≤ T / 2
    · exact A1 u ⟨zero_le, hut⟩
    · exact (second u (not_le.1 hut).le hu).trans (by linarith)
  · rintro ⟨H1, H2⟩
    refine ⟨fun u hu => ?_, fun v hv => ?_⟩
    · have hu' := (denseSub_subset _ hu).2
      exact (H1 u (hu'.trans hTT)).trans (le_refl _)
    · have hv' := (denseSub_subset _ hv).2
      refine H2 _ le_self_add ?_
      rw [← NNReal.coe_le_coe]; push_cast
      have := NNReal.coe_le_coe.2 hv'
      push_cast at this; linarith

section Abstract

variable {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}

lemma measurableSet_pathTube {B : ℝ≥0 → Ω → (Fin d → ℝ)} {t : ℝ≥0}
    (hB : ∀ s ≤ t, Measurable (B s)) (x : Fin d → ℝ) (f : ℝ → Fin d → ℝ) (ρ : ℝ) :
    MeasurableSet {ω | (fun s => B s ω) ∈ tubeSet d x f ρ t} := by
  have e : {ω | (fun s => B s ω) ∈ tubeSet d x f ρ t} =
      (⋂ u ∈ denseSub (Set.Icc (0 : ℝ≥0) t), {ω | ‖x + B u ω - f u‖ ≤ ρ}) ∩
      {ω | ‖x + B t ω - f t‖ ≤ ρ / 10} := by
    ext ω; simp [tubeSet]
  rw [e]
  refine (MeasurableSet.biInter (denseSub_countable _) fun u hu => ?_).inter ?_
  · have := hB u (denseSub_subset _ hu).2
    exact measurableSet_le ((this.const_add x).sub_const _).norm measurable_const
  · have := hB t le_rfl
    exact measurableSet_le ((this.const_add x).sub_const _).norm measurable_const

end Abstract

/-- The set of pairs `(z, w)` with `w ∈ tubeSet d z f ρ T`. -/
def tubeSetJ (d : ℕ) (f : ℝ → Fin d → ℝ) (ρ : ℝ) (T : ℝ≥0) : Set ((Fin d → ℝ) × PathSpace d) :=
  {q | q.2 ∈ tubeSet d q.1 f ρ T}

lemma measurableSet_tubeSetJ (d : ℕ) (f : ℝ → Fin d → ℝ) (ρ : ℝ) (T : ℝ≥0) :
    MeasurableSet (tubeSetJ d f ρ T) := by
  have e : tubeSetJ d f ρ T =
      (⋂ u ∈ denseSub (Set.Icc (0 : ℝ≥0) T),
        {q : (Fin d → ℝ) × PathSpace d | ‖q.1 + q.2 u - f u‖ ≤ ρ}) ∩
      {q : (Fin d → ℝ) × PathSpace d | ‖q.1 + q.2 T - f T‖ ≤ ρ / 10} := by
    ext q; simp [tubeSetJ, tubeSet]
  rw [e]
  refine (MeasurableSet.biInter (denseSub_countable _) fun u _ => ?_).inter ?_
  · exact measurableSet_le
      (by fun_prop : Measurable fun q : (Fin d → ℝ) × PathSpace d => ‖q.1 + q.2 u - f u‖)
      measurable_const
  · exact measurableSet_le
      (by fun_prop : Measurable fun q : (Fin d → ℝ) × PathSpace d => ‖q.1 + q.2 T - f T‖)
      measurable_const

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
  {B : ℝ≥0 → Ω → (Fin d → ℝ)}

lemma norm_scale_eq {σ : ℝ} (hσ : 0 < σ) (x y z : Fin d → ℝ) :
    ‖x + σ • y - z‖ = σ * ‖σ⁻¹ • x + y - σ⁻¹ • z‖ := by
  have : x + σ • y - z = σ • (σ⁻¹ • x + y - σ⁻¹ • z) := by
    rw [smul_sub, smul_add, smul_smul, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul, one_smul]
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hσ]

/-- Tube lemma. -/
theorem tube_lemma [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P) {K : ℝ}
    (hK : 1 ≤ K) {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) {ρ : ℝ} (hρ : 0 < ρ) {T : ℝ≥0}
    (hT1 : ρ ^ 2 / K ≤ T) (hT2 : (T : ℝ) ≤ K * ρ ^ 2) {f : ℝ → Fin d → ℝ} {x : Fin d → ℝ}
    (hf : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ v ∈ Set.Icc (0 : ℝ) T, ‖f u - f v‖ ≤ K / ρ * |u - v|)
    (hx : ‖x - f 0‖ ≤ 3 * ρ / 5) :
    ENNReal.ofReal (ctube d K) ≤ P {ω | pathMap B ω ∈ tube2Set d σ x f ρ T} := by
  have hσ0 : 0 < σ := by linarith
  have hK0 : 0 < K := by linarith
  set t : ℝ≥0 := T / 2 with ht
  have htR : (t : ℝ) = T / 2 := by simp [ht]
  set ρ' : ℝ := ρ / σ with hρ'
  have hρ'0 : 0 < ρ' := by positivity
  have hρ'1 : ρ' ≤ ρ := div_le_self hρ.le hσ1
  have hρ'2 : ρ ≤ 2 * ρ' := by
    rw [hρ', ← mul_div_assoc, le_div_iff₀ hσ0]; nlinarith
  set x' : Fin d → ℝ := σ⁻¹ • x with hx'
  set f' : ℝ → Fin d → ℝ := fun u => σ⁻¹ • f u with hf'
  set f2 : ℝ → Fin d → ℝ := fun u => f' ((t : ℝ) + u) with hf2
  -- Lipschitz constants of `f'`
  have hLf' : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ v ∈ Set.Icc (0 : ℝ) T,
      ‖f' u - f' v‖ ≤ K / ρ * |u - v| := by
    intro u hu v hv
    have : f' u - f' v = σ⁻¹ • (f u - f v) := by simp [hf', smul_sub]
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hσ0)]
    calc _ ≤ 1 * ‖f u - f v‖ := mul_le_mul_of_nonneg_right
          (inv_le_one_of_one_le₀ hσ1) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hf u hu v hv
  have ht0 : (0 : ℝ) ≤ t := t.2
  have htle : (t : ℝ) ≤ T := by linarith [T.2]
  have hρ4 : ρ ^ 2 ≤ 4 * ρ' ^ 2 := by nlinarith
  have hρ2le : ρ' ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hρ'0.le hρ'1 2
  have hT1' : ρ ^ 2 ≤ K * T := by
    have h1 : ρ ^ 2 / K ≤ T := hT1
    rwa [div_le_iff₀ hK0, mul_comm] at h1
  -- Phase 1
  have hP1 : ENNReal.ofReal (tubeC0 d (8 * K)) ≤
      P {ω | pathMap B ω ∈ tubeSet d x' f' ρ' t} := by
    refine tube_basic hB (by linarith) hρ'0 (T := t) ?_ ?_ ?_ ?_
    · rw [htR, div_le_iff₀ (by linarith)]
      nlinarith
    · rw [htR]
      nlinarith
    · intro u hu v hv
      have := hLf' u ⟨hu.1, hu.2.trans htle⟩ v ⟨hv.1, hv.2.trans htle⟩
      refine this.trans ?_
      have hKρ : K / ρ ≤ 8 * K / ρ' := by
        rw [div_le_div_iff₀ hρ hρ'0]
        nlinarith
      exact mul_le_mul_of_nonneg_right hKρ (abs_nonneg _)
    · have : x' - f' 0 = σ⁻¹ • (x - f 0) := by simp [hx', hf', smul_sub]
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hσ0)]
      calc σ⁻¹ * ‖x - f 0‖ ≤ σ⁻¹ * (3 * ρ / 5) := mul_le_mul_of_nonneg_left hx (inv_pos.2 hσ0).le
        _ = 3 * ρ' / 5 := by rw [hρ']; field_simp
  -- Phase 2
  have hPsi : ∀ z : Fin d → ℝ, ‖z - f2 0‖ ≤ 3 * (ρ' / 5) / 5 →
      ENNReal.ofReal (tubeC0 d (52 * K)) ≤
        P {ω | pathMap B ω ∈ tubeSet d z f2 (ρ' / 5) t} := by
    intro z hz
    refine tube_basic hB (by linarith) (by positivity) (T := t) ?_ ?_ ?_ hz
    · rw [htR, div_le_iff₀ (by linarith)]
      nlinarith
    · rw [htR]
      nlinarith
    · intro u hu v hv
      have hu' : (t : ℝ) + u ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hu.1], by linarith [hu.2, htR]⟩
      have hv' : (t : ℝ) + v ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hv.1], by linarith [hv.2, htR]⟩
      have := hLf' _ hu' _ hv'
      refine (this.trans ?_)
      have e : |(t : ℝ) + u - ((t : ℝ) + v)| = |u - v| := by congr 1; ring
      rw [e]
      have hKρ : K / ρ ≤ 52 * K / (ρ' / 5) := by
        rw [div_div_eq_mul_div, div_le_div_iff₀ hρ (by positivity)]
        nlinarith
      exact mul_le_mul_of_nonneg_right hKρ (abs_nonneg _)
  -- Markov property at time `t`
  set S2 : Set ((Fin d → ℝ) × PathSpace d) := tubeSetJ d f2 (ρ' / 5) t with hS2
  set Φ : (Fin d → ℝ) → PathSpace d → ℝ≥0∞ := fun z w => S2.indicator 1 (z, w) with hΦdef
  have hΦ : Measurable (Function.uncurry Φ) := by
    have : Function.uncurry Φ = S2.indicator 1 := by
      funext ⟨z, w⟩; rfl
    rw [this]
    exact measurable_one.indicator (measurableSet_tubeSetJ d f2 _ t)
  set P1 : Set Ω := {ω | pathMap B ω ∈ tubeSet d x' f' ρ' t} with hP1def
  have hA : MeasurableSet[bmFiltration B t] P1 :=
    @measurableSet_pathTube Ω (bmFiltration B t) d B t (fun s hs => measurable_bmFiltration hs)
      x' f' ρ'
  have hZ : Measurable[bmFiltration B t] (fun ω => x' + B t ω) :=
    (measurable_bmFiltration (B := B) le_rfl).const_add x'
  have key := hB.lintegral_indicator_shift t hZ hA hΦ
  have hP1m : MeasurableSet P1 := bmFiltration_le hB.measurable t _ hA
  set T2 : Set Ω := {ω | (x' + B t ω, shiftPath B t ω) ∈ S2} with hT2def
  have hT2m : MeasurableSet T2 :=
    ((measurable_const.add (hB.measurable t)).prodMk (measurable_shiftPath hB.measurable t))
      (measurableSet_tubeSetJ d f2 _ t)
  have hlhs : ∫⁻ ω, P1.indicator (fun ω => Φ (x' + B t ω) (shiftPath B t ω)) ω ∂P =
      P (P1 ∩ T2) := by
    rw [← lintegral_indicator_one (hP1m.inter hT2m)]
    refine lintegral_congr fun ω => ?_
    by_cases h1 : ω ∈ P1
    · by_cases h2 : ω ∈ T2
      · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show ω ∈ P1 ∩ T2 from ⟨h1, h2⟩)]
        exact Set.indicator_of_mem (show (x' + B t ω, shiftPath B t ω) ∈ S2 from h2) _
      · rw [Set.indicator_of_mem h1,
          Set.indicator_of_notMem (show ω ∉ P1 ∩ T2 from fun hh => h2 hh.2)]
        exact Set.indicator_of_notMem (show (x' + B t ω, shiftPath B t ω) ∉ S2 from h2) _
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (fun hh => h1 hh.1)]
  have hrhs : ENNReal.ofReal (tubeC0 d (52 * K)) * P P1 ≤ P (P1 ∩ T2) := by
    rw [← hlhs, key, ← lintegral_indicator_const hP1m]
    refine lintegral_mono fun ω => ?_
    by_cases h1 : ω ∈ P1
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h1]
      have hfib : MeasurableSet (Prod.mk (x' + B t ω) ⁻¹' S2) :=
        measurable_prodMk_left (measurableSet_tubeSetJ d f2 _ t)
      have e : Φ (x' + B t ω) = (Prod.mk (x' + B t ω) ⁻¹' S2).indicator 1 := by
        funext w; rfl
      rw [e, lintegral_indicator_one hfib, ← hB.map_pathMap_eq_wiener,
        Measure.map_apply hB.measurable_pathMap hfib]
      refine hPsi _ ?_
      have h2 := h1.2
      have e2 : f2 0 = f' (t : ℝ) := by simp [hf2]
      rw [e2]
      have h3 : ‖x' + B t ω - f' (t : ℝ)‖ ≤ ρ' / 10 := h2
      exact h3.trans (by linarith)
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h1]
  have hsub : P1 ∩ T2 ⊆ {ω | pathMap B ω ∈ tube2Set d σ x f ρ T} := by
    rintro ω ⟨h1, h2⟩
    refine ⟨fun u hu => ?_, fun v hv => ?_⟩
    · have := h1.1 u hu
      rw [norm_scale_eq hσ0]
      calc σ * ‖σ⁻¹ • x + pathMap B ω u - σ⁻¹ • f u‖ ≤ σ * ρ' :=
            mul_le_mul_of_nonneg_left this hσ0.le
        _ = ρ := by rw [hρ']; field_simp
    · have := h2.1 v hv
      have e : x' + B t ω + shiftPath B t ω v = x' + B (t + v) ω := by
        simp only [shiftPath]; abel
      have h3 : ‖x' + B (t + v) ω - f' ((t : ℝ) + v)‖ ≤ ρ' / 5 := by
        have : ‖x' + B t ω + shiftPath B t ω v - f2 v‖ ≤ ρ' / 5 := this
        rwa [e] at this
      show ‖x + σ • B (T / 2 + v) ω - f ((T / 2 + v : ℝ≥0) : ℝ)‖ ≤ ρ / 5
      have e4 : (T / 2 : ℝ≥0) = t := rfl
      rw [e4, norm_scale_eq hσ0]
      have e5 : (((t + v : ℝ≥0)) : ℝ) = (t : ℝ) + v := by push_cast; ring
      rw [e5]
      calc σ * ‖σ⁻¹ • x + B (t + v) ω - σ⁻¹ • f ((t : ℝ) + v)‖ ≤ σ * (ρ' / 5) :=
            mul_le_mul_of_nonneg_left h3 hσ0.le
        _ = ρ / 5 := by rw [hρ']; field_simp
  calc ENNReal.ofReal (ctube d K)
      = ENNReal.ofReal (tubeC0 d (52 * K)) * ENNReal.ofReal (tubeC0 d (8 * K)) := by
        unfold ctube
        rw [mul_comm, ENNReal.ofReal_mul (by unfold tubeC0; positivity)]
    _ ≤ ENNReal.ofReal (tubeC0 d (52 * K)) * P P1 := mul_le_mul_right hP1 _
    _ ≤ P (P1 ∩ T2) := hrhs
    _ ≤ _ := measure_mono hsub

lemma continuousOn_of_lip {f : ℝ → Fin d → ℝ} {T : ℝ} {L : ℝ}
    (hf : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ v ∈ Set.Icc (0 : ℝ) T, ‖f u - f v‖ ≤ L * |u - v|) :
    ContinuousOn f (Set.Icc (0 : ℝ) T) := by
  refine (LipschitzOnWith.of_dist_le_mul (K := L.toNNReal) fun u hu v hv => ?_).continuousOn
  rw [dist_eq_norm, Real.dist_eq]
  refine (hf u hu v hv).trans ?_
  by_cases hL : 0 ≤ L
  · rw [Real.coe_toNNReal _ hL]
  · have h0 : ‖f u - f v‖ ≤ 0 := by
      have := hf u hu v hv
      nlinarith [abs_nonneg (u - v), not_le.1 hL]
    have h1 : L.toNNReal = 0 := Real.toNNReal_of_nonpos (not_le.1 hL).le
    rw [h1]
    simp
    nlinarith [abs_nonneg (u - v), not_le.1 hL]

/-- Tube lemma, the event form. -/
theorem tube_lemma_event [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P) {K : ℝ}
    (hK : 1 ≤ K) {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) {ρ : ℝ} (hρ : 0 < ρ) {T : ℝ≥0}
    (hT1 : ρ ^ 2 / K ≤ T) (hT2 : (T : ℝ) ≤ K * ρ ^ 2) {f : ℝ → Fin d → ℝ} {x : Fin d → ℝ}
    (hf : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ v ∈ Set.Icc (0 : ℝ) T, ‖f u - f v‖ ≤ K / ρ * |u - v|)
    (hx : ‖x - f 0‖ ≤ 3 * ρ / 5) :
    {ω | (∀ u : ℝ≥0, u ≤ T → ‖x + σ • B u ω - f u‖ ≤ ρ) ∧
        (∀ u : ℝ≥0, T / 2 ≤ u → u ≤ T → ‖x + σ • B u ω - f u‖ ≤ ρ / 5)} =
      pathMap B ⁻¹' tube2Set d σ x f ρ T ∧
    MeasurableSet {ω | (∀ u : ℝ≥0, u ≤ T → ‖x + σ • B u ω - f u‖ ≤ ρ) ∧
        (∀ u : ℝ≥0, T / 2 ≤ u → u ≤ T → ‖x + σ • B u ω - f u‖ ≤ ρ / 5)} ∧
    ENNReal.ofReal (ctube d K) ≤ P {ω | (∀ u : ℝ≥0, u ≤ T → ‖x + σ • B u ω - f u‖ ≤ ρ) ∧
        (∀ u : ℝ≥0, T / 2 ≤ u → u ≤ T → ‖x + σ • B u ω - f u‖ ≤ ρ / 5)} := by
  have hfc := continuousOn_of_lip hf
  have e : {ω | (∀ u : ℝ≥0, u ≤ T → ‖x + σ • B u ω - f u‖ ≤ ρ) ∧
        (∀ u : ℝ≥0, T / 2 ≤ u → u ≤ T → ‖x + σ • B u ω - f u‖ ≤ ρ / 5)} =
      pathMap B ⁻¹' tube2Set d σ x f ρ T := by
    ext ω
    exact (mem_tube2Set_iff (continuous_path hB ω) σ x hρ.le hfc).symm
  refine ⟨e, ?_, ?_⟩
  · rw [e]; exact hB.measurable_pathMap (measurableSet_tube2Set d σ x f ρ T)
  · rw [e]; exact tube_lemma hB hK hσ1 hσ2 hρ hT1 hT2 hf hx

end Main

end ElboimSly.Brownian
