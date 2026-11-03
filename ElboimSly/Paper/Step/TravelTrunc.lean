/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.NaturalCouplingLaw
public import ElboimSly.Paper.Step.RegenMeas
public import ElboimSly.Paper.Step.Symmetry
public import ElboimSly.Paper.Step.SecondMomentFree
public import ElboimSly.Foundations.Cyclic.CycFar
public import ElboimSly.Foundations.Cyclic.CycFarRc
public import Mathlib

/-!
# The truncated endpoint of a block (path-space facts)

ES22 Lemma 7.3; ES22 Lemma 7.4 (truncation step): `𝒜 := {sup_{s≤h} ‖W(s)‖ < K}` and
`X := 𝟙_𝒜 W(h)`.

`truncEnd h K` is the functional `w ↦ 𝟙{w ∉ farSet K h} w(h)` on path space; the supremum is over
the countable set `checkTimes h` (rational times and `h`), which is the whole interval for
right-continuous paths (`exists_check_of_rc`). It is measurable, bounded by `K`, and odd.
For the regenerated path `ppPath N` of a Poisson environment, `ppLaw` is the law of the path
stopped at `h`; it is invariant under `w ↦ -w` (lattice symmetry of the regenerated walk), gives the tail bound of
`cyc_far` and the second-moment bound of second moment of a truncated endpoint.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ}

/-- Negation as a lattice automorphism. -/
def latticeNeg (d : ℕ) : Interchange.LatticeAut d where
  toEquiv := Equiv.neg _
  adj u v := by
    unfold LatticeAdj
    refine Iff.of_eq (congrArg (· = 1) (Finset.sum_congr rfl fun j _ => ?_))
    simp only [Equiv.neg_apply, Pi.neg_apply]
    rw [← abs_neg]; congr 1; ring

/-- Pointwise negation of a path. -/
def negPath (w : ℝ≥0 → Fin d → ℤ) : ℝ≥0 → Fin d → ℤ := fun t => -w t

theorem measurable_negPath : Measurable (negPath (d := d)) :=
  measurable_pi_iff.2 fun t => (measurable_of_countable (fun v : Fin d → ℤ => -v)).comp
    (measurable_pi_apply t)

/-- The truncated endpoint `𝟙{sup_{s ≤ h} ‖w(s)‖ < K} w(h)` (supremum over `checkTimes h`). -/
noncomputable def truncEnd (h : ℝ≥0) (K : ℝ) (w : ℝ≥0 → Fin d → ℤ) : Fin d → ℤ :=
  Set.indicator ((farSet K h)ᶜ) (fun w => w h) w

theorem measurable_truncEnd (h : ℝ≥0) (K : ℝ) : Measurable (truncEnd (d := d) h K) :=
  (measurable_pi_apply h).indicator (measurableSet_farSet K h).compl

theorem norm_truncEnd_le {h : ℝ≥0} {K : ℝ} (hK : 0 ≤ K) (w : ℝ≥0 → Fin d → ℤ) :
    ‖truncEnd h K w‖ ≤ K := by
  by_cases hw : w ∈ farSet K h
  · simp [truncEnd, hw, hK]
  · have : ‖w h‖ < K := by
      by_contra hcon
      exact hw (mem_iUnion₂.2 ⟨h, Or.inl rfl, not_lt.1 hcon⟩)
    simpa [truncEnd, hw] using this.le

theorem truncEnd_neg (h : ℝ≥0) (K : ℝ) (w : ℝ≥0 → Fin d → ℤ) :
    truncEnd h K (negPath w) = -truncEnd h K w := by
  have : negPath w ∈ farSet K h ↔ w ∈ farSet K h := by
    constructor <;> intro hm <;> obtain ⟨q, hq, hk⟩ := mem_iUnion₂.1 hm <;>
      exact mem_iUnion₂.2 ⟨q, hq, by simpa [negPath] using hk⟩
  by_cases hw : w ∈ farSet K h
  · simp [truncEnd, hw, this.2 hw]
  · simp [truncEnd, hw, this, negPath]

theorem checkTimes_le {h q : ℝ≥0} (hq : q ∈ checkTimes h) : q ≤ h := by
  rcases hq with rfl | ⟨h', -⟩
  · exact le_rfl
  · exact h'

theorem stopPath_mem_farSet (h : ℝ≥0) (K : ℝ) (w : ℝ≥0 → Fin d → ℤ) :
    SRW.stopPath h w ∈ farSet K h ↔ w ∈ farSet K h := by
  simp only [farSet, mem_iUnion]
  refine exists_congr fun q => exists_congr fun hq => ?_
  simp [SRW.stopPath, min_eq_left (checkTimes_le hq)]

theorem truncEnd_stop (h : ℝ≥0) (K : ℝ) (w : ℝ≥0 → Fin d → ℤ) :
    truncEnd h K (SRW.stopPath h w) = truncEnd h K w := by
  by_cases hw : w ∈ farSet K h
  · simp [truncEnd, hw, (stopPath_mem_farSet h K w).2 hw]
  · simp [truncEnd, hw, (stopPath_mem_farSet h K w).not.2 hw, SRW.stopPath]

section PPP

variable {β : ℝ} [Fact (0 < β)] {Ωe : Type} [MeasurableSpace Ωe] {Pe : Measure Ωe}
  {N : Ωe → Measure (ℕ × RingSpace d β)}

/-- The regenerated path of a Poisson environment sequence. -/
noncomputable def ppPath (N : Ωe → Measure (ℕ × RingSpace d β)) (ω : Ωe) :
    ℝ≥0 → Fin d → ℤ := fun t => regenWalk (fun k => copyEnv (N ω) k) (t : ℝ)

/-- The law of the regenerated path stopped at `h`. -/
noncomputable def ppLaw (Pe : Measure Ωe) (N : Ωe → Measure (ℕ × RingSpace d β)) (h : ℝ≥0) :
    Measure (ℝ≥0 → Fin d → ℤ) := (Pe.map (ppPath N)).map (SRW.stopPath h)

theorem aemeasurable_ppPath
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe) :
    AEMeasurable (ppPath N) Pe := aemeasurable_regenWalk_path hN

/-- The law of the stopped regenerated path is invariant under `w ↦ -w`
(lattice symmetry of the regenerated walk). -/
theorem ppLaw_neg
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (h : ℝ≥0) : (ppLaw Pe N h).map negPath = ppLaw Pe N h := by
  have hae := aemeasurable_ppPath hN
  have key := step_symmetry_law hN (latticeNeg d) (by simp [latticeNeg])
  have e1 : (Pe.map (ppPath N)).map negPath = Pe.map (ppPath N) := by
    rw [AEMeasurable.map_map_of_aemeasurable measurable_negPath.aemeasurable hae]
    exact key
  have hcomm : (negPath ∘ SRW.stopPath h) = (SRW.stopPath h ∘ negPath (d := d)) := by
    funext w t; simp [negPath, SRW.stopPath]
  unfold ppLaw
  rw [Measure.map_map measurable_negPath (SRW.measurable_stopPath h), hcomm,
    ← Measure.map_map (SRW.measurable_stopPath h) measurable_negPath, e1]

/-- An odd function integrates to zero against a negation-invariant law. -/
theorem integral_eq_zero_of_odd {Q : Measure (ℝ≥0 → Fin d → ℤ)} (hQ : Q.map negPath = Q)
    (F : (ℝ≥0 → Fin d → ℤ) → ℝ) (hF : Measurable F) (hodd : ∀ w, F (negPath w) = -F w) :
    ∫ w, F w ∂Q = 0 := by
  have h1 : ∫ w, F w ∂Q = ∫ w, F (negPath w) ∂Q := by
    conv_lhs => rw [← hQ]
    exact integral_map measurable_negPath.aemeasurable hF.aestronglyMeasurable
  have h2 : ∫ w, F (negPath w) ∂Q = -∫ w, F w ∂Q := by
    simp [hodd, integral_neg]
  linarith

/-- The tail of the stopped path being far, from the unstopped event. -/
theorem ppLaw_tail
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (h : ℝ≥0) (K : ℝ) :
    ppLaw Pe N h (farSet K h) ≤
      Pe {ω | ∃ s : ℝ≥0, s ≤ h ∧ K ≤ ‖regenWalk (fun k => copyEnv (N ω) k) (s : ℝ)‖} := by
  have hae := aemeasurable_ppPath hN
  unfold ppLaw
  rw [Measure.map_apply (SRW.measurable_stopPath h) (measurableSet_farSet K h)]
  have : SRW.stopPath h ⁻¹' farSet (d := d) K h = farSet K h := by
    ext w; exact stopPath_mem_farSet h K w
  rw [this, Measure.map_apply_of_aemeasurable hae (measurableSet_farSet K h)]
  refine measure_mono fun ω hω => ?_
  obtain ⟨q, hq, hKq⟩ := mem_iUnion₂.1 hω
  exact ⟨q, checkTimes_le hq, hKq⟩

theorem ppLaw_eq
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (h : ℝ≥0) : ppLaw Pe N h = Pe.map (fun ω => SRW.stopPath h (ppPath N ω)) :=
  AEMeasurable.map_map_of_aemeasurable (SRW.measurable_stopPath h).aemeasurable
    (aemeasurable_ppPath hN)

/-- **Second moment of the truncated endpoint** (second moment of a truncated endpoint). -/
theorem ppLaw_second_moment {n₁ n : ℕ} {t₀ : ℝ} (hR : StepRegime d n₁ β n t₀)
    (hβ : (12 : ℝ) ^ 16 ≤ β) {h : ℝ} (h1 : (4 : ℝ) ^ n₁ < h) (h2 : h ≤ 4 ^ n) {K : ℝ}
    (hK : 0 ≤ K)
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe) :
    ∫ w, ‖truncEnd h.toNNReal K w‖ ^ 2 ∂ppLaw Pe N h.toNNReal ≤
      6 * d * h + 2 * h ^ (2 * indThetaH) + K ^ 2 * Real.exp (-((stepLevel h : ℝ) ^ 2)) := by
  have hh1 : 1 < h := lt_of_le_of_lt (one_le_pow₀ (by norm_num)) h1
  have hh0 : 0 < h := by linarith
  set T : ℝ≥0 := h.toNNReal with hT
  have hTc : (T : ℝ) = h := Real.coe_toNNReal h hh0.le
  have hae := aemeasurable_ppPath hN
  have hmeasF : Measurable fun w : ℝ≥0 → Fin d → ℤ =>
      ENNReal.ofReal (‖truncEnd T K w‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_of_countable (fun v : Fin d → ℤ => ‖v‖ ^ 2)).comp (measurable_truncEnd T K))
  have hst : AEMeasurable (fun ω => SRW.stopPath T (ppPath N ω)) Pe :=
    (SRW.measurable_stopPath T).comp_aemeasurable hae
  have hlin : ∫⁻ w, ENNReal.ofReal (‖truncEnd T K w‖ ^ 2) ∂ppLaw Pe N T ≤
      ENNReal.ofReal (6 * d * h + 2 * h ^ (2 * indThetaH) +
        K ^ 2 * Real.exp (-((stepLevel h : ℝ) ^ 2))) := by
    rw [ppLaw_eq hN, lintegral_map' hmeasF.aemeasurable hst]
    refine le_trans (lintegral_mono_ae ?_) (step_second_moment hR hβ h1 h2 hK Ωe Pe N hN)
    filter_upwards [Cyclic.ae_cycGood hN] with ω hω
    simp only [truncEnd_stop]
    by_cases hw : ppPath N ω ∈ farSet K T
    · simp [truncEnd, hw]
    · have hsup : ∀ r : Set.Icc (0 : ℝ) h,
          ENNReal.ofReal ‖regenWalk (fun k => copyEnv (N ω) k) (r : ℝ)‖ ≤ ENNReal.ofReal K := by
        intro r
        refine ENNReal.ofReal_le_ofReal ?_
        by_contra hcon
        rw [not_le] at hcon
        have hr0 : (0 : ℝ) ≤ r := r.2.1
        set s : ℝ≥0 := (r : ℝ).toNNReal
        have hsc : (s : ℝ) = r := Real.coe_toNNReal _ hr0
        have hsT : s ≤ T := by
          rw [← NNReal.coe_le_coe, hsc, hTc]; exact r.2.2
        have hrc : ∀ u : ℝ≥0, ∀ᶠ v : ℝ≥0 in 𝓝[≥] u, ppPath N ω v = ppPath N ω u := fun u => by
          simp only [copyEnv_eq_cycSlice, ppPath]
          exact regenWalk_rc hω u
        obtain ⟨q, hq, hKq⟩ := exists_check_of_rc hrc hsT (P := fun v => K ≤ ‖v‖)
          (by simpa [ppPath, hsc] using hcon.le)
        exact hw (mem_iUnion₂.2 ⟨q, hq, hKq⟩)
      have hle : (⨆ r : Set.Icc (0 : ℝ) h,
          ENNReal.ofReal ‖regenWalk (fun k => copyEnv (N ω) k) (r : ℝ)‖) ≤ ENNReal.ofReal K :=
        iSup_le hsup
      have : ω ∈ {ω | ⨆ r : Set.Icc (0 : ℝ) h,
          ENNReal.ofReal ‖regenWalk (fun k => copyEnv (N ω) k) (r : ℝ)‖ ≤ ENNReal.ofReal K} := hle
      rw [Set.indicator_of_mem this]
      simp [truncEnd, hw, ppPath, hTc]
  have hB : 0 ≤ 6 * (d : ℝ) * h + 2 * h ^ (2 * indThetaH) +
      K ^ 2 * Real.exp (-((stepLevel h : ℝ) ^ 2)) := by positivity
  have hint := integral_eq_lintegral_of_nonneg_ae
    (μ := ppLaw Pe N T) (f := fun w => ‖truncEnd T K w‖ ^ 2)
    (Filter.Eventually.of_forall fun w => by positivity)
    (measurable_of_countable (fun v : Fin d → ℤ => ‖v‖ ^ 2) |>.comp
      (measurable_truncEnd T K) |>.aestronglyMeasurable)
  rw [hint]
  exact ENNReal.toReal_le_of_le_ofReal hB hlin

end PPP

end ElboimSly.Paper.Step
