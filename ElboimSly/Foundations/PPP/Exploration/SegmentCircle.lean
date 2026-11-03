/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.SegmentReal
public import ElboimSly.Foundations.PPP.Exploration.Segment
public import ElboimSly.Foundations.PPP.Exploration.ThmStop
import Mathlib

/-!
# Segment probes on `E × 𝕋`

Segment probes on E×mathbbT_β and E×mathbbR, case (i): `X = 𝕋 = AddCircle β`, `λ = Leb_β` (`volume`), segments
`x_e(s) = [t_e + σ_e s]` with `σ_e ∈ {+1, -1}`, left inverse `s_e(y)` the `(0, β]`-representative
of `σ_e (y - [t_e])`, weight `w ≡ 1`, and horizon `h ≤ β`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly

namespace Circle

variable {β : ℝ} [Fact (0 < β)]

/-- The `(0, β]`-representative of a point of the circle. -/
noncomputable def rep (y : AddCircle β) : ℝ := (AddCircle.equivIoc β 0 y : ℝ)

theorem rep_mem (y : AddCircle β) : rep y ∈ Ioc 0 β := by
  have := (AddCircle.equivIoc β 0 y).2
  simpa [rep] using this

theorem coe_rep (y : AddCircle β) : ((rep y : ℝ) : AddCircle β) = y :=
  AddCircle.coe_equivIoc

theorem rep_coe {s : ℝ} (hs : s ∈ Ioc 0 β) : rep (s : AddCircle β) = s := by
  have : s ∈ Ioc 0 (0 + β) := by simpa using hs
  exact AddCircle.equivIoc_coe_of_mem this

theorem measurable_rep : Measurable (rep : AddCircle β → ℝ) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc β 0).measurable

/-- `∫_{rep ∈ (0,h]} G = ∫_{(0,h]} G(↑s) ds` on the circle. -/
theorem setLIntegral_rep (G : AddCircle β → ℝ≥0∞) (hG : Measurable G) {h : ℝ≥0}
    (hh : (h : ℝ) ≤ β) :
    ∫⁻ z in {z | rep z ∈ Ioc (0 : ℝ) h}, G z = ∫⁻ s in Ioc (0 : ℝ) h, G (s : AddCircle β) := by
  set T : Set (AddCircle β) := {z | rep z ∈ Ioc (0 : ℝ) h} with hTdef
  have hT : MeasurableSet T :=
    measurableSet_Ioc.preimage measurable_rep
  rw [← lintegral_indicator hT]
  have hmp := AddCircle.measurePreserving_mk β 0
  rw [← hmp.lintegral_comp (hG.indicator hT)]
  have hI : MeasurableSet (Ioc (0 : ℝ) (h : ℝ)) := measurableSet_Ioc
  have h1 : ∫⁻ s in Ioc (0 : ℝ) (0 + β), (T.indicator G) (s : AddCircle β) =
      ∫⁻ s in Ioc (0 : ℝ) (0 + β), (Ioc (0 : ℝ) h).indicator (fun s => G (s : AddCircle β)) s := by
    refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hs' : s ∈ Ioc (0 : ℝ) β := by simpa using hs
    simp only [T, Set.indicator, mem_ofPred_eq, rep_coe hs']
  rw [h1, lintegral_indicator hI, Measure.restrict_restrict hI]
  have : Ioc (0 : ℝ) h ∩ Ioc 0 (0 + β) = Ioc (0 : ℝ) h := by
    refine Set.inter_eq_left.2 fun s hs => ?_
    simp only [zero_add, mem_Ioc] at hs ⊢
    exact ⟨hs.1, hs.2.trans hh⟩
  rw [this]

instance : NullSingletonClass (volume : Measure (AddCircle β)) where
  measure_singleton x := by
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
    have hε' : (0 : ℝ) < (ε : ℝ) / 2 := by
      have : (0 : ℝ) < ε := by exact_mod_cast hε
      positivity
    calc volume {x} ≤ volume (Metric.closedBall x ((ε : ℝ) / 2)) :=
          measure_mono (by simp [Metric.mem_closedBall, hε'.le])
      _ = ENNReal.ofReal (min β (2 * ((ε : ℝ) / 2))) := AddCircle.volume_closedBall β _
      _ ≤ ENNReal.ofReal (2 * ((ε : ℝ) / 2)) := ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ = 0 + ε := by
          rw [zero_add, show 2 * ((ε : ℝ) / 2) = ε by ring, ENNReal.ofReal_coe_nnreal]

/-- Change of variables for a measure-preserving embedding `f` with left inverse `g`. -/
theorem setLIntegral_preimage_rep (f g : AddCircle β → AddCircle β)
    (hf : MeasurePreserving f volume volume) (hfe : MeasurableEmbedding f)
    (hg : ∀ y, g (f y) = y) (ψ : AddCircle β → ℝ≥0∞) (hψ : Measurable ψ)
    (hgm : Measurable g) {h : ℝ≥0} (hh : (h : ℝ) ≤ β) :
    ∫⁻ y in f ⁻¹' {z | rep z ∈ Ioc (0 : ℝ) h}, ψ y =
      ∫⁻ s in Ioc (0 : ℝ) h, ψ (g (s : AddCircle β)) := by
  have h1 : ∫⁻ y in f ⁻¹' {z | rep z ∈ Ioc (0 : ℝ) h}, ψ y =
      ∫⁻ y in f ⁻¹' {z | rep z ∈ Ioc (0 : ℝ) h}, (ψ ∘ g) (f y) := by
    refine lintegral_congr fun y => ?_
    simp [hg]
  rw [h1, hf.setLIntegral_comp_preimage_emb hfe (ψ ∘ g)]
  exact setLIntegral_rep _ (hψ.comp hgm) hh

end Circle

open _root_.ElboimSly.Circle

variable {E : Type*} [MeasurableSpace E] {β : ℝ} [Fact (0 < β)]

/-- The segment `x_e(s) = [t_e + σ_e s]` on the circle. -/
noncomputable def circX (t σ : E → ℝ) (e : E) (s : ℝ) : AddCircle β := ((t e + σ e * s : ℝ) : AddCircle β)

/-- The `(0, β]`-representative of `σ_e (y - [t_e])`. -/
noncomputable def circS (t σ : E → ℝ) (e : E) (y : AddCircle β) : ℝ :=
  if σ e = 1 then rep (y - ((t e : ℝ) : AddCircle β)) else rep (((t e : ℝ) : AddCircle β) - y)

omit [MeasurableSpace E] in
theorem circX_sinv (t σ : E → ℝ) (hσ : ∀ e, σ e = 1 ∨ σ e = -1) (e : E) (y : AddCircle β) :
    circX t σ e (circS t σ e y) = y := by
  unfold circX circS
  rcases hσ e with h | h
  · simp [h, coe_rep]
  · have : ¬ ((-1 : ℝ) = 1) := by norm_num
    simp [h, coe_rep, this]

omit [MeasurableSpace E] in
theorem circS_circX (t σ : E → ℝ) (hσ : ∀ e, σ e = 1 ∨ σ e = -1) (e : E) {s : ℝ}
    (hs : s ∈ Ioc 0 β) : circS t σ e (circX t σ e s : AddCircle β) = s := by
  unfold circX circS
  rcases hσ e with h | h
  · simp [h, rep_coe hs]
  · have : ¬ ((-1 : ℝ) = 1) := by norm_num
    simp [h, rep_coe hs, this]

omit [MeasurableSpace E] in
theorem measurable_circS (t σ : E → ℝ) (e : E) : Measurable (circS t σ e : AddCircle β → ℝ) := by
  unfold circS
  split_ifs
  · exact measurable_rep.comp (measurable_sub_const _)
  · exact measurable_rep.comp (measurable_const_sub _)

omit [MeasurableSpace E] [Fact (0 < β)] in
theorem measurable_circX (t σ : E → ℝ) (e : E) : Measurable (circX t σ e : ℝ → AddCircle β) := by
  unfold circX
  exact AddCircle.measurable_mk'.comp (by fun_prop)

omit [MeasurableSpace E] in
/-- Segment probes on E×mathbbT_β and E×mathbbR (i), the segment setup on `𝕋 = AddCircle β` with `λ = Leb_β`,
weight `w ≡ 1`, and horizon `h ≤ β`. -/
theorem segSetup_circle (A : Finset E) (t σ : E → ℝ) (hσ : ∀ e, σ e = 1 ∨ σ e = -1) (h : ℝ≥0)
    (hh : (h : ℝ) ≤ β) :
    SegSetup (volume : Measure (AddCircle β)) A (circX t σ) (circS t σ) h
      (fun _ _ => 1) := by
  refine ⟨measurable_circX t σ, measurable_circS t σ, fun _ => measurable_const,
    fun _ _ => le_refl _, fun e _ s hs => circS_circX t σ hσ e (by
      refine ⟨hs.1, hs.2.trans hh⟩), fun e => ?_, fun e _ ψ hψ => ?_⟩
  · simp only [circX_sinv t σ hσ]
    exact MeasurableSet.univ
  · have hseg : segImg (circX t σ) (circS t σ) h e =
        (if σ e = 1 then (fun y : AddCircle β => y - ((t e : ℝ) : AddCircle β))
          else fun y => ((t e : ℝ) : AddCircle β) - y) ⁻¹' {z | rep z ∈ Ioc (0 : ℝ) h} := by
      ext y
      simp only [segImg, circX_sinv t σ hσ, mem_ofPred_eq, mem_preimage, mem_Ioc, and_true]
      unfold circS
      split_ifs <;> simp
    simp only [one_mul]
    rw [hseg]
    rcases hσ e with hs | hs
    · simp only [hs, ite_true]
      have hm := measurePreserving_sub_right (volume : Measure (AddCircle β))
        ((t e : ℝ) : AddCircle β)
      rw [setLIntegral_preimage_rep (fun y => y - ((t e : ℝ) : AddCircle β))
        (fun z => z + ((t e : ℝ) : AddCircle β)) hm
        (MeasurableEquiv.subRight _).measurableEmbedding (fun y => by simp) ψ hψ
        (measurable_add_const _) hh]
      refine setLIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
      simp [circX, hs, add_comm]
    · have : σ e ≠ 1 := by rw [hs]; norm_num
      simp only [this, ite_false]
      have hm := Measure.measurePreserving_sub_left (volume : Measure (AddCircle β))
        ((t e : ℝ) : AddCircle β)
      rw [setLIntegral_preimage_rep (fun y => ((t e : ℝ) : AddCircle β) - y)
        (fun z => ((t e : ℝ) : AddCircle β) - z) hm
        (Homeomorph.subLeft ((t e : ℝ) : AddCircle β)).measurableEmbedding (fun y => by simp) ψ hψ
        (measurable_const_sub _) hh]
      refine setLIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
      simp [circX, hs, sub_eq_add_neg]

/-- Segment probes on E×mathbbT_β and E×mathbbR (i), (a): the circle segment probe is a probe. -/
theorem isProbe_segR_circle [Countable E] [MeasurableSingletonClass E] (A : Finset E)
    (t σ : E → ℝ) (hσ : ∀ e, σ e = 1 ∨ σ e = -1) (h : ℝ≥0) (hh : (h : ℝ) ≤ β)
    {Z : Set (E × AddCircle β)} (hZ : MeasurableSet Z) :
    IsProbe ((Measure.count : Measure E).prod (volume : Measure (AddCircle β)))
      (segR A (circX t σ) (circS t σ) h Z) h :=
  isProbe_segR (segSetup_circle A t σ hσ h hh) hZ

variable {U : Type*} [MeasurableSpace U]

end ElboimSly
