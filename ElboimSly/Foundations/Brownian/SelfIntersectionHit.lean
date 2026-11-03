/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.SelfIntersectionCover
public import ElboimSly.Foundations.Brownian.SelfIntersectionSet
public import ElboimSly.Foundations.Brownian.Freeze
public import ElboimSly.Foundations.Brownian.Density
public import ElboimSly.Foundations.Brownian.Sup

import Mathlib

/-!
# Hitting the past path at one integer time

ES22 Claim 9.4, Step 2 (ii).

Given the history up to time `a` (on the good event), the probability that `B (a + v)` is within
`1 + ρ` of the past path is at most
`(2π v)^{-5/2} M (6ρ)^5 + 10 e^{-(R/2)²/(2v)}`: the first term is the density bound
(density bounds (b)) on the cube of radius `R/2`, the second is the Gaussian tail
(Gaussian maximal bound (b)). The history enters through Markov property at a fixed time (c).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → R5}

/-- Rational times `≤ a`. -/
abbrev RatLe (a : ℝ≥0) : Type := ↥(ratTimes ∩ Set.Iic a)

instance (a : ℝ≥0) : Countable (RatLe a) :=
  (ratTimes_countable.mono Set.inter_subset_left).to_subtype

omit mΩ in
lemma pastSet_eq {ω : Ω} (hc : Continuous fun u => B u ω) (a : ℝ≥0) (c : ℝ) :
    pastSet B a c ω =
      ⋂ n : ℕ, ⋃ q : RatLe a, {y | ‖y - B q.1 ω‖ < c + 1 / ((n : ℝ) + 1)} := by
  ext y
  simp only [pastSet, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
  rw [exists_le_iff_rat hc y a c]
  refine forall_congr' fun n => ?_
  constructor
  · rintro ⟨q, hq, hqa, h⟩
    exact ⟨⟨q, hq, hqa⟩, h⟩
  · rintro ⟨⟨q, hq, hqa⟩, h⟩
    exact ⟨q, hq, hqa, h⟩

omit mΩ in
lemma measurableSet_pastSet {ω : Ω} (hc : Continuous fun u => B u ω) (a : ℝ≥0) (c : ℝ) :
    MeasurableSet (pastSet B a c ω) := by
  rw [pastSet_eq hc]
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q => ?_
  exact (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).measurableSet

/-- The Gaussian estimate for one fibre: the probability that `z + B v` lies in `S`. -/
lemma fiber_le [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion 5 B P) {v : ℝ≥0}
    (hv : v ≠ 0) {S : Set R5} (hS : MeasurableSet S) {z : R5} {R V : ℝ} (hR : 0 < R)
    (hV : volume (S ∩ Metric.closedBall z (R / 2)) ≤ ENNReal.ofReal V) (hV0 : 0 ≤ V) :
    P {ω | z + (1 : ℝ) • B v ω ∈ S} ≤
      ENNReal.ofReal ((2 * Real.pi * v) ^ (-(5 : ℝ) / 2) * V +
        10 * Real.exp (-(R / 2) ^ 2 / (2 * v))) := by
  have hv0 : (0 : ℝ) < v := by positivity
  have hsub : {ω | z + (1 : ℝ) • B v ω ∈ S} ⊆
      {ω | z + (1 : ℝ) • B v ω ∈ S ∩ Metric.closedBall z (R / 2)} ∪
        {ω | R / 2 ≤ ‖B v ω‖} := by
    intro ω hω
    by_cases h : ‖B v ω‖ ≤ R / 2
    · left
      refine ⟨hω, ?_⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa using h
    · right; exact (not_le.1 h).le
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  have h1 := hB.measure_affine_le hv z (σ := 1) one_pos
    (A := S ∩ Metric.closedBall z (R / 2))
    (hS.inter (Metric.isClosed_closedBall (x := z) (ε := R / 2)).measurableSet)
  have h2 := hB.norm_ge_le hv (l := R / 2) (by linarith)
  have e1 : ENNReal.ofReal ((2 * Real.pi * ((1 : ℝ) ^ 2 * v)) ^ (-((5 : ℕ) : ℝ) / 2)) =
      ENNReal.ofReal ((2 * Real.pi * v) ^ (-(5 : ℝ) / 2)) := by
    norm_num
  rw [e1] at h1
  calc _ ≤ ENNReal.ofReal ((2 * Real.pi * v) ^ (-(5 : ℝ) / 2)) * ENNReal.ofReal V +
        (2 * ((5 : ℕ) : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-(R / 2) ^ 2 / (2 * v))) :=
        add_le_add (h1.trans (mul_le_mul' le_rfl hV)) h2
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 2
        have : (2 * ((5 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal 10 := by
          rw [show (10 : ℝ) = 2 * 5 by norm_num, ENNReal.ofReal_mul (by norm_num)]
          simp
        rw [this, ← ENNReal.ofReal_mul (by norm_num)]

/-- The path-space set of `(history, path)` pairs for which `z + w v` is within `c` of the past
path, in the countable form. -/
def hitSet (a v : ℝ≥0) (c : ℝ) : Set ((R5 × (RatLe a → R5)) × PathSpace 5) :=
  ⋂ n : ℕ, ⋃ q : RatLe a, {p | ‖p.1.1 + p.2 v - p.1.2 q‖ < c + 1 / ((n : ℝ) + 1)}

lemma measurableSet_hitSet (a v : ℝ≥0) (c : ℝ) : MeasurableSet (hitSet a v c) := by
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q => ?_
  refine measurableSet_lt ?_ measurable_const
  have h1 : Measurable fun p : (R5 × (RatLe a → R5)) × PathSpace 5 => p.1.1 :=
    measurable_fst.comp measurable_fst
  have h2 : Measurable fun p : (R5 × (RatLe a → R5)) × PathSpace 5 => p.2 v :=
    (measurable_pi_apply v).comp measurable_snd
  have h3 : Measurable fun p : (R5 × (RatLe a → R5)) × PathSpace 5 => p.1.2 q :=
    (measurable_pi_apply q).comp (measurable_snd.comp measurable_fst)
  exact ((h1.add h2).sub h3).norm

/-- ES22 Claim 9.4, Step 2 (ii). For `F ∈ ℱ_a`, the probability that, on
the good event `G(a)`, the point `B (a + v)` is within `1 + ρ` of the past path is at most the
bound `(2π v)^{-5/2} M (6ρ)^5 + 10 e^{-(R/2)²/(2v)}` times `P (G(a) ∩ F)`. -/
theorem hit_le [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion 5 B P) {a v : ℝ≥0}
    (hv : v ≠ 0) {t ρ R M : ℝ} (ht : 1 ≤ t) (hρ : 1 ≤ ρ) (hR : 2 + 4 * ρ ≤ R) (hM : 0 ≤ M)
    {F : Set Ω} (hF : MeasurableSet[bmFiltration B a] F) :
    P ({ω | ∃ s' ≤ a, ‖B (a + v) ω - B s' ω‖ ≤ 1 + ρ} ∩ (good B t ρ (3 * R) M a ∩ F)) ≤
      ENNReal.ofReal ((2 * Real.pi * v) ^ (-(5 : ℝ) / 2) * (M * (6 * ρ) ^ 5) +
        10 * Real.exp (-(R / 2) ^ 2 / (2 * v))) * P (good B t ρ (3 * R) M a ∩ F) := by
  have hR0 : 0 < R := by linarith
  set A : Set Ω := good B t ρ (3 * R) M a ∩ F with hAdef
  have hAF : MeasurableSet[bmFiltration B a] A := @MeasurableSet.inter Ω (bmFiltration B a) _ _ (measurableSet_good hB t ρ (3 * R) M a) hF
  have hA : MeasurableSet A := bmFiltration_le hB.measurable a _ hAF
  have hcont : ∀ ω, Continuous fun u => B u ω := fun ω => (hB.continuous_zero ω).1
  let Z : Ω → R5 × (RatLe a → R5) := fun ω => (B a ω, fun q => B q.1 ω)
  have hZ : Measurable[bmFiltration B a] Z := by
    let _ : MeasurableSpace Ω := bmFiltration B a
    refine Measurable.prodMk (measurable_bmFiltration le_rfl) (measurable_pi_iff.2 fun q => ?_)
    exact measurable_bmFiltration q.2.2
  have hZ' : Measurable Z := hZ.mono (bmFiltration_le hB.measurable a) le_rfl
  let Φ : R5 × (RatLe a → R5) → PathSpace 5 → ℝ≥0∞ := fun e w =>
    (hitSet a v (1 + ρ)).indicator 1 (e, w)
  have hΦ : Measurable (Function.uncurry Φ) := by
    have : Function.uncurry Φ = (hitSet a v (1 + ρ)).indicator 1 := by
      funext ⟨e, w⟩; rfl
    rw [this]
    exact measurable_one.indicator (measurableSet_hitSet a v _)
  have key := hB.lintegral_indicator_shift a hZ hAF hΦ
  have hshift : Measurable (shiftPath B a) := measurable_shiftPath hB.measurable a
  -- the event, in terms of the pair (Z, shift)
  have hev : {ω | ∃ s' ≤ a, ‖B (a + v) ω - B s' ω‖ ≤ 1 + ρ} ∩ A =
      A ∩ (fun ω => (Z ω, shiftPath B a ω)) ⁻¹' hitSet a v (1 + ρ) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    rw [and_comm]
    refine and_congr_right fun _ => ?_
    have hrw := exists_le_iff_rat (hcont ω) (B (a + v) ω) a (1 + ρ)
    rw [hrw]
    simp only [hitSet, Set.mem_iInter, Set.mem_iUnion, Set.mem_ofPred_eq, Z, shiftPath,
      add_sub_cancel]
    refine forall_congr' fun n => ?_
    constructor
    · rintro ⟨q, hq, hqa, h⟩
      exact ⟨⟨q, hq, hqa⟩, h⟩
    · rintro ⟨⟨q, hq, hqa⟩, h⟩
      exact ⟨q, hq, hqa, h⟩
  have hL : P ({ω | ∃ s' ≤ a, ‖B (a + v) ω - B s' ω‖ ≤ 1 + ρ} ∩ A) =
      ∫⁻ ω, A.indicator (fun ω => Φ (Z ω) (shiftPath B a ω)) ω ∂P := by
    rw [hev]
    have hm : MeasurableSet (A ∩ (fun ω => (Z ω, shiftPath B a ω)) ⁻¹' hitSet a v (1 + ρ)) :=
      hA.inter ((hZ'.prodMk hshift) (measurableSet_hitSet a v _))
    rw [← lintegral_indicator_one hm]
    refine lintegral_congr fun ω => ?_
    by_cases h : ω ∈ A
    · by_cases h' : (Z ω, shiftPath B a ω) ∈ hitSet a v (1 + ρ)
      · have : ω ∈ A ∩ (fun ω => (Z ω, shiftPath B a ω)) ⁻¹' hitSet a v (1 + ρ) := ⟨h, h'⟩
        simp [Set.indicator_of_mem this, Set.indicator_of_mem h, Φ, Set.indicator_of_mem h']
      · have : ω ∉ A ∩ (fun ω => (Z ω, shiftPath B a ω)) ⁻¹' hitSet a v (1 + ρ) :=
          fun hh => h' hh.2
        simp [Set.indicator_of_notMem this, Set.indicator_of_mem h, Φ,
          Set.indicator_of_notMem h']
    · have : ω ∉ A ∩ (fun ω => (Z ω, shiftPath B a ω)) ⁻¹' hitSet a v (1 + ρ) :=
        fun hh => h hh.1
      simp [Set.indicator_of_notMem this, Set.indicator_of_notMem h]
  rw [hL, key]
  -- pointwise bound for the inner integral
  set q : ℝ≥0∞ := ENNReal.ofReal ((2 * Real.pi * v) ^ (-(5 : ℝ) / 2) * (M * (6 * ρ) ^ 5) +
        10 * Real.exp (-(R / 2) ^ 2 / (2 * v))) with hq
  calc ∫⁻ ω, A.indicator (fun ω => ∫⁻ w, Φ (Z ω) w ∂wienerMeasure 5) ω ∂P
      ≤ ∫⁻ ω, A.indicator (fun _ => q) ω ∂P := by
        refine lintegral_mono fun ω => ?_
        by_cases hω : ω ∈ A
        · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
          have hgood : ω ∈ good B t ρ (3 * R) M a := hω.1
          have hfib : MeasurableSet (Prod.mk (Z ω) ⁻¹' hitSet a v (1 + ρ)) :=
            measurable_prodMk_left (measurableSet_hitSet a v _)
          have e : (fun w => Φ (Z ω) w) =
              (Prod.mk (Z ω) ⁻¹' hitSet a v (1 + ρ)).indicator 1 := by
            funext w; rfl
          show ∫⁻ w, Φ (Z ω) w ∂wienerMeasure 5 ≤ q
          rw [e, lintegral_indicator_one hfib, ← hB.map_pathMap_eq_wiener,
            Measure.map_apply hB.measurable_pathMap hfib]
          have hset : pathMap B ⁻¹' (Prod.mk (Z ω) ⁻¹' hitSet a v (1 + ρ)) =
              {ω' | B a ω + (1 : ℝ) • B v ω' ∈ pastSet B a (1 + ρ) ω} := by
            ext ω'
            rw [pastSet_eq (hcont ω)]
            simp only [Set.mem_preimage, hitSet, Set.mem_iInter, Set.mem_iUnion, Set.mem_ofPred_eq,
              Z, pathMap, one_smul]
          rw [hset]
          exact fiber_le hB hv (measurableSet_pastSet (hcont ω) a _) hR0
            (volume_pastSet_le ht hρ hR hgood) (by positivity)
        · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
    _ = q * P A := by
        rw [lintegral_indicator_const hA, mul_comm]

end ElboimSly.Brownian
