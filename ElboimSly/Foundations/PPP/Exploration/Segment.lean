/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ThmStop
import Mathlib

/-!
# Segment probes

Segment probes on E×mathbbT_β and E×mathbbR (a), the abstract change of variables.

On `S = E × X` with `μ = # ⊗ λ`, a *segment probe* is given by a finite set `A ⊆ E`, parametrized
segments `s ↦ x_e(s)` with measurable left inverses `s_e`, a horizon `h` and a mask `Z`:
`R(e, y) = s_e(y)` if `e ∈ A`, `y = x_e(s)` with `s ∈ (0, h]` and `(e, y) ∉ Z`, and `R = ∞` otherwise.
The hypothesis `cv` is the change of variables `∫_{x_e((0,h])} ψ dλ = ∫_{(0,h]} w_e(s) ψ(x_e s) ds`;
it is proved for `X = ℝ` (`λ = Leb|_I`, `w = 1_I ∘ x_e`) and `X = 𝕋` in `SegmentSpaces`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {E X : Type*} [MeasurableSpace E] [MeasurableSpace X]

/-- The image `x_e((0, h])`, described through the left inverse. -/
def segImg (x : E → ℝ → X) (sinv : E → X → ℝ) (h : ℝ≥0) (e : E) : Set X :=
  {y | 0 < sinv e y ∧ sinv e y ≤ h ∧ x e (sinv e y) = y}

open scoped Classical in
/-- Segment probes on E×mathbbT_β and E×mathbbR: the entrance time `R` of a segment probe with mask `Z`. -/
noncomputable def segR (A : Finset E) (x : E → ℝ → X) (sinv : E → X → ℝ) (h : ℝ≥0)
    (Z : Set (E × X)) (p : E × X) : ℝ≥0∞ :=
  if p.1 ∈ A ∧ p.2 ∈ segImg x sinv h p.1 ∧ p ∉ Z then ENNReal.ofReal (sinv p.1 p.2) else ⊤

/-- The weight `f(e, s) = w_e(s) 1{(e, x_e(s)) ∉ Z}`. -/
noncomputable def segF (x : E → ℝ → X) (w : E → ℝ → ℝ≥0∞) (Z : Set (E × X)) (e : E) (s : ℝ) :
    ℝ≥0∞ := open scoped Classical in if (e, x e s) ∈ Z then 0 else w e s

/-- Hypotheses on a segment family. -/
structure SegSetup (lam : Measure X) (A : Finset E) (x : E → ℝ → X) (sinv : E → X → ℝ) (h : ℝ≥0)
    (w : E → ℝ → ℝ≥0∞) : Prop where
  meas_x : ∀ e, Measurable (x e)
  meas_s : ∀ e, Measurable (sinv e)
  meas_w : ∀ e, Measurable (w e)
  w_le : ∀ e s, w e s ≤ 1
  left : ∀ e ∈ A, ∀ s ∈ Set.Ioc (0 : ℝ) h, sinv e (x e s) = s
  graph : ∀ e, MeasurableSet {y | x e (sinv e y) = y}
  cv : ∀ e ∈ A, ∀ ψ : X → ℝ≥0∞, Measurable ψ →
    ∫⁻ y in segImg x sinv h e, ψ y ∂lam = ∫⁻ s in Set.Ioc (0 : ℝ) h, w e s * ψ (x e s)

variable {lam : Measure X} {A : Finset E} {x : E → ℝ → X} {sinv : E → X → ℝ} {h : ℝ≥0}
  {w : E → ℝ → ℝ≥0∞} (hS : SegSetup lam A x sinv h w)

include hS

omit [MeasurableSpace E] in
theorem measurableSet_segImg (e : E) : MeasurableSet (segImg x sinv h e) := by
  have : segImg x sinv h e = {y | 0 < sinv e y} ∩ {y | sinv e y ≤ h} ∩ {y | x e (sinv e y) = y} := by
    ext y; simp [segImg, and_assoc]
  rw [this]
  exact ((measurableSet_lt measurable_const (hS.meas_s e)).inter
    (measurableSet_le (hS.meas_s e) measurable_const)).inter (hS.graph e)

variable [Countable E] [MeasurableSingletonClass E] {Z : Set (E × X)} (hZ : MeasurableSet Z)

include hZ

theorem measurable_segR : Measurable (segR A x sinv h Z) := by
  classical
  refine measurable_from_prod_countable_right fun e => ?_
  have hset : MeasurableSet {y | e ∈ A ∧ y ∈ segImg x sinv h e ∧ (e, y) ∉ Z} := by
    by_cases he : e ∈ A
    · have : {y | e ∈ A ∧ y ∈ segImg x sinv h e ∧ (e, y) ∉ Z} =
          segImg x sinv h e \ Prod.mk e ⁻¹' Z := by
        ext y; simp [he]
      rw [this]
      exact (measurableSet_segImg hS e).diff (measurable_prodMk_left hZ)
    · simp [he]
  have : (fun y => segR A x sinv h Z (e, y)) = fun y =>
      if y ∈ {y | e ∈ A ∧ y ∈ segImg x sinv h e ∧ (e, y) ∉ Z} then ENNReal.ofReal (sinv e y)
        else ⊤ := rfl
  rw [this]
  exact Measurable.ite hset (ENNReal.measurable_ofReal.comp (hS.meas_s e)) measurable_const

omit hS hZ in
omit [MeasurableSpace E] [MeasurableSpace X] [Countable E] [MeasurableSingletonClass E] in
theorem segR_le_iff {r : ℝ≥0} {Z : Set (E × X)} (p : E × X) :
    segR A x sinv h Z p ≤ r ↔
      (p.1 ∈ A ∧ p.2 ∈ segImg x sinv h p.1 ∧ p ∉ Z) ∧ sinv p.1 p.2 ≤ r := by
  classical
  unfold segR
  by_cases hc : p.1 ∈ A ∧ p.2 ∈ segImg x sinv h p.1 ∧ p ∉ Z
  · rw [ite_eq_left hc]
    simp only [hc, true_and]
    rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top]
    simp
  · rw [ite_eq_right hc]
    simp [hc]

theorem lintegral_segR [SFinite lam] {r : ℝ≥0} (hr : r ≤ h) {Φ : E × X → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    ∫⁻ p in {p | segR A x sinv h Z p ≤ r}, Φ p ∂((Measure.count : Measure E).prod lam) =
      ∑ e ∈ A, ∫⁻ s in Set.Ioc (0 : ℝ) r, segF x w Z e s * Φ (e, x e s) := by
  classical
  have hmR := measurable_segR hS hZ
  have hD : MeasurableSet {p : E × X | segR A x sinv h Z p ≤ r} :=
    measurableSet_le hmR measurable_const
  have hmI : Measurable ({p : E × X | segR A x sinv h Z p ≤ r}.indicator Φ) := hΦ.indicator hD
  rw [← lintegral_indicator hD, lintegral_prod _ hmI.aemeasurable, lintegral_count]
  rw [tsum_eq_sum (s := A)]
  · refine Finset.sum_congr rfl fun e he => ?_
    -- the integrand in `y`
    let ψ : X → ℝ≥0∞ := fun y => if sinv e y ≤ r ∧ (e, y) ∉ Z then Φ (e, y) else 0
    have hψ : Measurable ψ := by
      refine Measurable.ite ?_ (hΦ.comp measurable_prodMk_left) measurable_const
      exact (measurableSet_le (hS.meas_s e) measurable_const).inter
        (measurable_prodMk_left hZ).compl
    have e1 : (fun y => {p : E × X | segR A x sinv h Z p ≤ r}.indicator Φ (e, y)) =
        (segImg x sinv h e).indicator ψ := by
      funext y
      by_cases hy : y ∈ segImg x sinv h e
      · simp only [Set.indicator, Set.mem_ofPred_eq, segR_le_iff, ψ, hy, he, true_and]
        by_cases h1 : sinv e y ≤ r <;> by_cases h2 : (e, y) ∈ Z <;> simp [h1, h2]
      · simp only [Set.indicator, Set.mem_ofPred_eq, segR_le_iff, hy]
        simp
    rw [e1, lintegral_indicator (measurableSet_segImg hS e), hS.cv e he ψ hψ]
    have e2 : ∀ s ∈ Set.Ioc (0 : ℝ) h, w e s * ψ (x e s) =
        (Set.Ioc (0 : ℝ) r).indicator (fun s => segF x w Z e s * Φ (e, x e s)) s := by
      intro s hs
      have hl := hS.left e he s hs
      by_cases hsr : s ≤ r
      · have hsm : s ∈ Set.Ioc (0 : ℝ) r := ⟨hs.1, hsr⟩
        rw [Set.indicator_of_mem hsm]
        by_cases hz : (e, x e s) ∈ Z
        · simp [ψ, segF, hz]
        · simp [ψ, segF, hz, hl, hsr]
      · have hsm : s ∉ Set.Ioc (0 : ℝ) r := fun h' => hsr h'.2
        rw [Set.indicator_of_notMem hsm]
        simp [ψ, hl, hsr]
    rw [setLIntegral_congr_fun measurableSet_Ioc e2, setLIntegral_indicator measurableSet_Ioc]
    have hsub : Set.Ioc (0 : ℝ) r ⊆ Set.Ioc (0 : ℝ) h :=
      Set.Ioc_subset_Ioc_right (by exact_mod_cast hr)
    rw [Set.inter_eq_left.2 hsub]
  · intro e he
    have : (fun y => {p : E × X | segR A x sinv h Z p ≤ r}.indicator Φ (e, y)) = fun _ => 0 := by
      funext y
      simp [Set.indicator, segR_le_iff, he]
    rw [this]; simp

omit hZ in
omit [Countable E] [MeasurableSingletonClass E] in
theorem measurable_segF (e : E) (hZ : MeasurableSet Z) : Measurable (segF x w Z e) := by
  classical
  have : segF x w Z e = fun s => if s ∈ (fun s => (e, x e s)) ⁻¹' Z then 0 else w e s := rfl
  rw [this]
  exact Measurable.ite ((measurable_const.prodMk (hS.meas_x e)) hZ) measurable_const (hS.meas_w e)

omit hS hZ in
omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
theorem segF_le_one (hS : SegSetup lam A x sinv h w) (e : E) (s : ℝ) : segF x w Z e s ≤ 1 := by
  classical
  unfold segF
  split_ifs
  · exact zero_le
  · exact hS.w_le e s

/-- `m(r) = ∫_0^r a(s) ds`, `a(s) = ∑_{e ∈ A} f(e, s)`. -/
noncomputable def segM (A : Finset E) (x : E → ℝ → X) (w : E → ℝ → ℝ≥0∞) (Z : Set (E × X))
    (r : ℝ) : ℝ≥0∞ := ∫⁻ s in Set.Ioc (0 : ℝ) r, ∑ e ∈ A, segF x w Z e s

/-- Segment probes on E×mathbbT_β and E×mathbbR (a): `μ(D(r)) = m(r)`. -/
theorem measure_segR_le [SFinite lam] {r : ℝ≥0} (hr : r ≤ h) :
    ((Measure.count : Measure E).prod lam) {p | segR A x sinv h Z p ≤ r} = segM A x w Z r := by
  have := lintegral_segR hS hZ hr (Φ := fun _ => 1) measurable_const
  rw [setLIntegral_one] at this
  rw [this, segM, lintegral_finsetSum _ (fun e _ => measurable_segF hS e hZ)]
  simp

/-- Segment probes on E×mathbbT_β and E×mathbbR (a): `(R, h)` is a probe. -/
theorem isProbe_segR [SFinite lam] [NullSingletonClass lam] [MeasurableSingletonClass X] :
    IsProbe ((Measure.count : Measure E).prod lam) (segR A x sinv h Z) h := by
  classical
  refine ⟨measurable_segR hS hZ, ?_, fun r hr => ?_⟩
  · have hm := measure_segR_le hS hZ (le_refl h)
    show _ < ∞
    have e : probeRegion (segR A x sinv h Z) (h : ℝ≥0∞) =
        {p | segR A x sinv h Z p ≤ (h : ℝ≥0∞)} := rfl
    rw [e, hm, segM]
    calc ∫⁻ s in Set.Ioc (0 : ℝ) h, ∑ e ∈ A, segF x w Z e s
        ≤ ∫⁻ s in Set.Ioc (0 : ℝ) h, (A.card : ℝ≥0∞) := by
          refine lintegral_mono fun s => ?_
          calc ∑ e ∈ A, segF x w Z e s ≤ ∑ e ∈ A, (1 : ℝ≥0∞) :=
                Finset.sum_le_sum fun e _ => segF_le_one hS e s
            _ = A.card := by simp
      _ < ∞ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (by simp)
  · have hsub : {p : E × X | segR A x sinv h Z p = (r : ℝ≥0∞)} ⊆
        ⋃ e ∈ A, ({e} : Set E) ×ˢ ({x e r} : Set X) := by
      intro p hp
      simp only [Set.mem_ofPred_eq] at hp
      by_cases hc : p.1 ∈ A ∧ p.2 ∈ segImg x sinv h p.1 ∧ p ∉ Z
      · simp only [segR, ite_eq_left hc] at hp
        have hs : sinv p.1 p.2 = r := by
          have h0 : 0 < sinv p.1 p.2 := hc.2.1.1
          have := congrArg ENNReal.toReal hp
          rw [ENNReal.toReal_ofReal h0.le] at this
          simpa using this
        simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
        refine ⟨p.1, hc.1, rfl, ?_⟩
        have := hc.2.1.2.2
        rw [hs] at this
        exact this.symm
      · simp only [segR, ite_eq_right hc] at hp
        exact absurd hp (by simp)
    refine measure_mono_null hsub ?_
    refine (measure_biUnion_null_iff (A.countable_toSet)).2 fun e _ => ?_
    rw [Measure.prod_prod]
    simp
theorem mass_segR [SFinite lam] {r : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ h) :
    probeMass ((Measure.count : Measure E).prod lam) (segR A x sinv h Z) (ENNReal.ofReal r) =
      segM A x w Z r := by
  have h1 := measure_segR_le hS hZ (r := r.toNNReal) (by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal r hr0]; exact hrh)
  have e : (ENNReal.ofReal r) = ((r.toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [probeMass, probeRegion, e]
  have : {p : E × X | segR A x sinv h Z p ≤ ((r.toNNReal : ℝ≥0) : ℝ≥0∞)} =
      {p | segR A x sinv h Z p ≤ r.toNNReal} := rfl
  show ((Measure.count : Measure E).prod lam) {p | segR A x sinv h Z p ≤ r.toNNReal} = _
  rw [h1, Real.coe_toNNReal r hr0]

/-- Segment probes on E×mathbbT_β and E×mathbbR (a): the first-point kernel of a segment probe. -/
theorem lintegral_segKernel [SFinite lam] [NullSingletonClass lam] [MeasurableSingletonClass X]
    {g : Outcome (E × X) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ o, g o ∂(probeKernel ((Measure.count : Measure E).prod lam) (segR A x sinv h Z) h) =
      expNeg (segM A x w Z h) * g ((h : ℝ≥0∞), 0) +
        ∑ e ∈ A, ∫⁻ s in Set.Ioc (0 : ℝ) h, segF x w Z e s *
          (expNeg (segM A x w Z s) * g (ENNReal.ofReal s, Measure.dirac (e, x e s))) := by
  classical
  have hmR := measurable_segR hS hZ
  rw [lintegral_probeKernel _ _ _ hmR hg]
  have hmh : probeMass ((Measure.count : Measure E).prod lam) (segR A x sinv h Z) h =
      segM A x w Z h := by
    have := mass_segR hS hZ (r := h) h.2 le_rfl
    simpa using this
  rw [hmh]
  congr 1
  have hΦ : Measurable fun p : E × X => expNeg (probeMass ((Measure.count : Measure E).prod lam)
      (segR A x sinv h Z) (segR A x sinv h Z p)) *
        g (segR A x sinv h Z p, Measure.dirac p) :=
    (measurable_expNeg_mass_comp _ _ hmR).mul (hg.comp (hmR.prodMk Measure.measurable_dirac))
  have := lintegral_segR hS hZ (le_refl h) hΦ
  have e0 : probeRegion (segR A x sinv h Z) (h : ℝ≥0∞) =
      {p | segR A x sinv h Z p ≤ h} := rfl
  rw [e0, this]
  refine Finset.sum_congr rfl fun e he => ?_
  refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  by_cases hz : (e, x e s) ∈ Z
  · simp [segF, hz]
  · have hl := hS.left e he s ⟨hs.1, hs.2⟩
    have hR : segR A x sinv h Z (e, x e s) = ENNReal.ofReal s := by
      have hc : (e, x e s).1 ∈ A ∧ (e, x e s).2 ∈ segImg x sinv h (e, x e s).1 ∧
          (e, x e s) ∉ Z := ⟨he, ⟨by simpa [hl] using hs.1, by simpa [hl] using hs.2,
            by simp [hl]⟩, hz⟩
      simp only [segR, ite_eq_left hc]
      simp [hl]
    have hm : probeMass ((Measure.count : Measure E).prod lam) (segR A x sinv h Z)
        (ENNReal.ofReal s) = segM A x w Z s := mass_segR hS hZ hs.1.le hs.2
    simp only [hR, hm]

end ElboimSly
