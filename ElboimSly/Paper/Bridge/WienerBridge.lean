/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Defs
public import ElboimSly.Frozen.Defs.AdmitsBMCoupling
public import ElboimSly.Frozen.Defs.IsWienerMeasure
public import ElboimSly.Frozen.Defs.WalkPath
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# The Wiener-measure / standard-Brownian-motion bridge (audit finding X1)

The Brownian API (`IsStandardBrownianMotion`) demands `B 0 = 0` at every `ω`, while the frozen
`IsWienerMeasure` and `AdmitsBMCoupling` only give `w 0 = 0` almost surely. This file converts in
both directions.

* `isStandardBrownianMotion_zeroMod_of_isWienerMeasure_map`: the modification
  `zeroMod Wb t ω = if Wb ω 0 = 0 then Wb ω t else 0` of a path with Wiener law is a standard
  Brownian motion, almost surely equal to `Wb`.
* `isWienerMeasure_map_pathC`: the path law of a standard Brownian motion is Wiener measure.
* `AdmitsBMCoupling` transfer: `exists_standardBrownianMotion_of_admitsBMCoupling`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly
namespace Bridge

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The modification of a `C(ℝ≥0, ℝᵈ)`-valued random path that is set to `0` where it does not
start at `0`. -/
noncomputable def zeroMod (Wb : Ω → C(ℝ≥0, Fin d → ℝ)) (t : ℝ≥0) (ω : Ω) : Fin d → ℝ :=
  if Wb ω 0 = 0 then Wb ω t else 0

omit [MeasurableSpace Ω] in
lemma zeroMod_eq_of_zero {Wb : Ω → C(ℝ≥0, Fin d → ℝ)} {ω : Ω} (h : Wb ω 0 = 0) (t : ℝ≥0) :
    zeroMod Wb t ω = Wb ω t := by
  simp [zeroMod, h]

lemma measurableSet_start_zero {Wb : Ω → C(ℝ≥0, Fin d → ℝ)} (hWb : Measurable Wb) :
    MeasurableSet {ω | Wb ω 0 = 0} :=
  (measurableSet_singleton (0 : Fin d → ℝ)).preimage
    ((ContinuousMap.measurable_eval (0 : ℝ≥0)).comp hWb)

lemma measurable_zeroMod {Wb : Ω → C(ℝ≥0, Fin d → ℝ)} (hWb : Measurable Wb) (t : ℝ≥0) :
    Measurable (zeroMod Wb t) :=
  Measurable.ite (measurableSet_start_zero hWb) ((ContinuousMap.measurable_eval t).comp hWb)
    measurable_const

private lemma isProbabilityMeasure_of_map {Q : Measure Ω} {Wb : Ω → C(ℝ≥0, Fin d → ℝ)}
    (hWb : Measurable Wb) (hW : IsWienerMeasure d (Q.map Wb)) : IsProbabilityMeasure Q := by
  refine ⟨?_⟩
  have := hW.1.measure_univ
  rwa [Measure.map_apply hWb MeasurableSet.univ, Set.preimage_univ] at this

/-- Almost surely the path starts at `0`. -/
lemma ae_start_zero {Q : Measure Ω} {Wb : Ω → C(ℝ≥0, Fin d → ℝ)}
    (hWb : Measurable Wb) (hW : IsWienerMeasure d (Q.map Wb)) : ∀ᵐ ω ∂Q, Wb ω 0 = 0 := by
  have h : ∀ i, ∀ᵐ w ∂(Q.map Wb), w 0 i = 0 := fun i => (hW.2.1 i).eval_zero_ae_eq_zero
  have h2 : ∀ᵐ w ∂(Q.map Wb), w 0 = 0 := by
    filter_upwards [ae_all_iff.2 h] with w hw using funext hw
  exact ae_of_ae_map hWb.aemeasurable h2

/-- **(H4) to Brownian API.** If the path `Wb` has Wiener law under `Q`, the modification
`zeroMod Wb` is a standard Brownian motion under `Q`, and `Wb ω = zeroMod Wb · ω` for `Q`-a.e. `ω`. -/
theorem isStandardBrownianMotion_zeroMod_of_isWienerMeasure_map {Q : Measure Ω}
    {Wb : Ω → C(ℝ≥0, Fin d → ℝ)} (hWb : Measurable Wb) (hW : IsWienerMeasure d (Q.map Wb)) :
    IsStandardBrownianMotion d (zeroMod Wb) Q ∧ ∀ᵐ ω ∂Q, ∀ t, zeroMod Wb t ω = Wb ω t := by
  have hQ := isProbabilityMeasure_of_map hWb hW
  have h0 := ae_start_zero hWb hW
  have hae : ∀ᵐ ω ∂Q, ∀ t, zeroMod Wb t ω = Wb ω t := by
    filter_upwards [h0] with ω hω t using zeroMod_eq_of_zero hω t
  have hcoord : ∀ i, Measurable (fun (w : C(ℝ≥0, Fin d → ℝ)) (t : ℝ≥0) => w t i) := fun i =>
    measurable_pi_iff.2 fun t =>
      (measurable_pi_apply i).comp (ContinuousMap.measurable_eval t)
  have hpre : ∀ i, IsPreBrownianReal (fun t ω => Wb ω t i) Q := by
    intro i
    refine ⟨fun I => ?_⟩
    have hg : Measurable (fun (w : C(ℝ≥0, Fin d → ℝ)) => I.restrict (fun t => w t i)) :=
      measurable_pi_iff.2 fun t => (measurable_pi_apply i).comp (ContinuousMap.measurable_eval _)
    refine ⟨(hg.comp hWb).aemeasurable, ?_⟩
    have := ((hW.2.1 i).hasLaw I).map_eq
    rw [Measure.map_map hg hWb] at this
    exact this
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hae⟩
  · exact measurable_zeroMod hWb
  · intro ω
    by_cases h : Wb ω 0 = 0
    · refine ⟨?_, by simp [zeroMod, h]⟩
      have : (fun t => zeroMod Wb t ω) = fun t => Wb ω t := funext (zeroMod_eq_of_zero h)
      rw [this]; exact (Wb ω).continuous
    · have : (fun t => zeroMod Wb t ω) = fun _ => 0 := funext fun t => by simp [zeroMod, h]
      rw [this]; exact ⟨continuous_const, by simp [zeroMod, h]⟩
  · intro i
    refine (hpre i).congr fun t => ?_
    filter_upwards [hae] with ω hω using by simp [hω t]
  · have hind : iIndepFun (fun i ω t => Wb ω t i) Q := by
      have h := hW.2.2
      have hBi : ∀ i, AEMeasurable (fun ω (t : ℝ≥0) => Wb ω t i) Q := fun i =>
        ((hcoord i).comp hWb).aemeasurable
      rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hcoord i).aemeasurable)] at h
      rw [iIndepFun_iff_map_fun_eq_pi_map hBi]
      have hall : Measurable (fun (w : C(ℝ≥0, Fin d → ℝ)) (i : Fin d) (t : ℝ≥0) => w t i) :=
        measurable_pi_iff.2 hcoord
      rw [Measure.map_map hall hWb] at h
      have e2 : ∀ i, Measure.map (fun ω t => Wb ω t i) Q =
          Measure.map (fun (w : C(ℝ≥0, Fin d → ℝ)) t => w t i) (Measure.map Wb Q) :=
        fun i => (Measure.map_map (hcoord i) hWb).symm
      rw [show (fun ω i t => Wb ω t i) = (fun w i t => w t i) ∘ Wb from rfl]
      exact h.trans (congrArg Measure.pi (funext fun i => (e2 i).symm))
    refine hind.congr fun i => ?_
    filter_upwards [hae] with ω hω using funext fun t => by simp [hω t]

/-- **Standard Brownian motion to Wiener measure.** The path law of a standard Brownian motion on
a probability space is Wiener measure. -/
theorem isWienerMeasure_map_pathC {B : ℝ≥0 → Ω → (Fin d → ℝ)} {P : Measure Ω}
    [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P) :
    IsWienerMeasure d
      (P.map fun ω => (⟨fun t => B t ω, (hB.continuous_zero ω).1⟩ : C(ℝ≥0, Fin d → ℝ))) := by
  let F : Ω → C(ℝ≥0, Fin d → ℝ) := fun ω => ⟨fun t => B t ω, (hB.continuous_zero ω).1⟩
  have hF : Measurable F := ContinuousMap.measurable_iff_eval.2 fun t => hB.measurable t
  have hcoord : ∀ i, Measurable (fun (w : C(ℝ≥0, Fin d → ℝ)) (t : ℝ≥0) => w t i) := fun i =>
    measurable_pi_iff.2 fun t =>
      (measurable_pi_apply i).comp (ContinuousMap.measurable_eval t)
  refine ⟨⟨by rw [Measure.map_apply hF MeasurableSet.univ]; simp⟩, fun i => ⟨fun I => ?_⟩, ?_⟩
  · have hI := (hB.isPreBrownianReal i).hasLaw I
    have hg : Measurable (fun (w : C(ℝ≥0, Fin d → ℝ)) => I.restrict (fun t => w t i)) :=
      measurable_pi_iff.2 fun t => (measurable_pi_apply i).comp (ContinuousMap.measurable_eval _)
    refine ⟨hg.aemeasurable, ?_⟩
    rw [Measure.map_map hg hF]
    exact hI.map_eq
  · have h := hB.iIndepFun
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hcoord i).aemeasurable)]
    have hBi : ∀ i, AEMeasurable (fun ω (t : ℝ≥0) => B t ω i) P := fun i =>
      (measurable_pi_iff.2 fun t => (measurable_pi_apply i).comp (hB.measurable t)).aemeasurable
    rw [iIndepFun_iff_map_fun_eq_pi_map hBi] at h
    have hall : Measurable (fun (w : C(ℝ≥0, Fin d → ℝ)) (i : Fin d) (t : ℝ≥0) => w t i) :=
      measurable_pi_iff.2 hcoord
    rw [Measure.map_map hall hF]
    have e1 : (fun w i t => w t i) ∘ F = fun ω i t => B t ω i := rfl
    have e2 : ∀ i, Measure.map (fun (w : C(ℝ≥0, Fin d → ℝ)) t => w t i) (Measure.map F P) =
        Measure.map (fun ω t => B t ω i) P := fun i => Measure.map_map (hcoord i) hF
    rw [e1]
    exact h.trans (congrArg Measure.pi (funext fun i => (e2 i).symm))

/-- The measurability of the path map of a standard Brownian motion. -/
lemma measurable_pathC {B : ℝ≥0 → Ω → (Fin d → ℝ)} {P : Measure Ω}
    (hB : IsStandardBrownianMotion d B P) :
    Measurable (fun ω => (⟨fun t => B t ω, (hB.continuous_zero ω).1⟩ : C(ℝ≥0, Fin d → ℝ))) :=
  ContinuousMap.measurable_iff_eval.2 fun t => hB.measurable t

/-- **Transfer for an (H4) coupling.** For a coupling `Q` whose second marginal is Wiener measure,
the second coordinate is `Q`-a.s. equal to a process that is a standard Brownian motion under `Q`. -/
theorem isStandardBrownianMotion_zeroMod_snd {α : Type*} [MeasurableSpace α]
    {Q : Measure (α × C(ℝ≥0, Fin d → ℝ))} (hW : IsWienerMeasure d (Q.map Prod.snd)) :
    IsStandardBrownianMotion d (zeroMod (Prod.snd : α × C(ℝ≥0, Fin d → ℝ) → _)) Q ∧
      ∀ᵐ p ∂Q, ∀ t, zeroMod (Prod.snd : α × C(ℝ≥0, Fin d → ℝ) → _) t p = p.2 t :=
  isStandardBrownianMotion_zeroMod_of_isWienerMeasure_map measurable_snd hW

/-- Unpacked form for `AdmitsBMCoupling`: some coupling `Q` carries a standard Brownian motion
(the modified second coordinate) a.s. equal to the second coordinate, with the same coupling bound. -/
theorem exists_standardBrownianMotion_of_admitsBMCoupling {T : ℝ≥0}
    {lawW : Measure (Set.Icc (0 : ℝ≥0) T → Fin d → ℤ)} {σ ε η : ℝ}
    (h : AdmitsBMCoupling d T lawW σ ε η) :
    ∃ Q : Measure (WalkPath d T × C(ℝ≥0, Fin d → ℝ)), IsProbabilityMeasure Q ∧
      Q.map (fun p => p.1.1) = lawW ∧
      IsStandardBrownianMotion d (zeroMod (Prod.snd : WalkPath d T × C(ℝ≥0, Fin d → ℝ) → _)) Q ∧
      (∀ᵐ p ∂Q, ∀ t, zeroMod (Prod.snd : WalkPath d T × C(ℝ≥0, Fin d → ℝ) → _) t p = p.2 t) ∧
      Q {p | ENNReal.ofReal ε ≤
        ⨆ t : Set.Icc (0 : ℝ≥0) T,
          ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) -
            σ • zeroMod (Prod.snd : WalkPath d T × C(ℝ≥0, Fin d → ℝ) → _) (t : ℝ≥0) p‖} ≤
        ENNReal.ofReal η := by
  obtain ⟨Q, hQ, hlaw, hW, hbd⟩ := h
  obtain ⟨hB, hae⟩ := isStandardBrownianMotion_zeroMod_snd hW
  refine ⟨Q, hQ, hlaw, hB, hae, ?_⟩
  refine le_of_eq_of_le (measure_congr ?_) hbd
  filter_upwards [hae] with p hp
  simp only [eq_iff_iff]
  simp only [hp]

end Bridge
end ElboimSly

end
