/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Stopping
public import ElboimSly.Foundations.Brownian.Oscillation
public import ElboimSly.Foundations.Brownian.Measurability
import Mathlib

/-!
# Real-valued Brownian motion and standard d-dimensional Brownian motion with `d = 1`

Real-valued Brownian motion and crefdef:bm with d=1.

A map `β : ℝ≥0 → Ω → ℝ` is a *standard real Brownian motion* if `toVec1 β = (fun t ω _ => β t ω)`
is a standard `1`-dimensional Brownian motion. The lemma transfers the API to `β`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- `β̄ = ι ∘ β`, where `ι x = (x) ∈ ℝ^1`. -/
def toVec1 (β : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → (Fin 1 → ℝ) := fun t ω _ => β t ω

/-- Real-valued Brownian motion and crefdef:bm with d=1. `β` is a standard real Brownian motion if `β̄` is a standard
`1`-dimensional Brownian motion. -/
def IsStandardRealBM (β : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop :=
  IsStandardBrownianMotion 1 (toVec1 β) P

/-- The natural filtration of a real process. -/
@[instance_reducible] def realFiltration (β : ℝ≥0 → Ω → ℝ) (a : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ (s : ℝ≥0) (_ : s ≤ a), MeasurableSpace.comap (β s) inferInstance

/-- The path map `ω ↦ (t ↦ β t ω)` of a real process, valued in `ℝ^{[0,∞)}`. -/
def realPath (β : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 → ℝ := fun t => β t ω

/-- The shift `sh_a β (u) = β(a+u) - β(a)`. -/
def realShift (β : ℝ≥0 → Ω → ℝ) (a : ℝ≥0) (ω : Ω) : ℝ≥0 → ℝ := fun u => β (a + u) ω - β a ω

def iotaBarInv (w : PathSpace 1) : ℝ≥0 → ℝ := fun t => w t 0

lemma measurable_iotaBarInv : Measurable iotaBarInv :=
  measurable_pi_iff.2 fun t => (measurable_pi_apply 0).comp (measurable_pi_apply t)

/-- Real-valued Brownian motion and crefdef:bm with d=1 (c). The real Wiener measure `(ῑ⁻¹)_* Wiener_1`. -/
noncomputable def realWiener : Measure (ℝ≥0 → ℝ) := (wienerMeasure 1).map iotaBarInv

/-! ### (a) -/

/-- Real-valued Brownian motion and crefdef:bm with d=1 (a). -/
theorem isStandardRealBM_iff [IsProbabilityMeasure P] {β : ℝ≥0 → Ω → ℝ} :
    IsStandardRealBM β P ↔ (∀ t, Measurable (β t)) ∧
      (∀ ω, Continuous (fun t => β t ω) ∧ β 0 ω = 0) ∧ IsPreBrownianReal β P := by
  constructor
  · intro h
    refine ⟨fun t => (measurable_pi_apply 0).comp (h.measurable t), fun ω => ?_,
      h.isPreBrownianReal 0⟩
    exact ⟨(continuous_apply 0).comp (h.continuous_zero ω).1, congrFun (h.continuous_zero ω).2 0⟩
  · rintro ⟨hm, hc, hp⟩
    exact ⟨fun t => measurable_pi_iff.2 fun _ => hm t,
      fun ω => ⟨continuous_pi fun _ => (hc ω).1, funext fun _ => (hc ω).2⟩,
      fun _ => hp, iIndepFun.of_subsingleton⟩

/-- Real-valued Brownian motion and crefdef:bm with d=1 (a): each coordinate of a standard `d`-dimensional Brownian motion
is a standard real Brownian motion. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.isStandardRealBM_coord [IsProbabilityMeasure P]
    {d : ℕ} {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (i : Fin d) :
    IsStandardRealBM (fun t ω => B t ω i) P :=
  hB.coord i

omit mΩ in
lemma toVec1_coord {B : ℝ≥0 → Ω → (Fin 1 → ℝ)} :
    toVec1 (fun t ω => B t ω 0) = B := by
  funext t ω i
  simp [toVec1, Subsingleton.elim i 0]

/-- Real-valued Brownian motion and crefdef:bm with d=1 (a): for a standard `1`-dimensional Brownian motion `B`,
`B^1` is a standard real Brownian motion and `\overline{B^1} = B`. -/
theorem isStandardRealBM_of_dim_one {B : ℝ≥0 → Ω → (Fin 1 → ℝ)}
    (hB : IsStandardBrownianMotion 1 B P) : IsStandardRealBM (fun t ω => B t ω 0) P := by
  unfold IsStandardRealBM
  rw [toVec1_coord]
  exact hB

/-! ### (b) -/

omit mΩ in
lemma comap_toVec1 (f : Ω → ℝ) :
    MeasurableSpace.comap (fun ω => (fun _ : Fin 1 => f ω)) inferInstance =
      MeasurableSpace.comap f inferInstance := by
  refine le_antisymm ?_ ?_
  · have : (fun ω => (fun _ : Fin 1 => f ω)) = (fun x : ℝ => fun _ : Fin 1 => x) ∘ f := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_iff.2 fun _ => measurable_id).comap_le
  · have : f = (fun z : Fin 1 → ℝ => z 0) ∘ (fun ω => (fun _ : Fin 1 => f ω)) := rfl
    conv_lhs => rw [this]
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply 0).comap_le

omit mΩ in
/-- Real-valued Brownian motion and crefdef:bm with d=1 (b). `β` and `β̄` have the same natural filtration. -/
theorem bmFiltration_toVec1 (β : ℝ≥0 → Ω → ℝ) (a : ℝ≥0) :
    bmFiltration (toVec1 β) a = realFiltration β a := by
  unfold bmFiltration realFiltration
  exact iSup_congr fun s => iSup_congr fun _ => comap_toVec1 (β s)

/-! ### (c) -/

/-- Real-valued Brownian motion and crefdef:bm with d=1 (c). The law of the path map of a standard real Brownian motion is
the real Wiener measure. -/
theorem IsStandardRealBM.map_realPath [IsProbabilityMeasure P] {β : ℝ≥0 → Ω → ℝ}
    (h : IsStandardRealBM β P) : P.map (realPath β) = realWiener := by
  have e : realPath β = iotaBarInv ∘ pathMap (toVec1 β) := rfl
  rw [e, ← Measure.map_map measurable_iotaBarInv h.measurable_pathMap, h.map_pathMap_eq_wiener]
  rfl

/-! ### (d) -/

theorem IsStandardRealBM.measurable [IsProbabilityMeasure P] {β : ℝ≥0 → Ω → ℝ}
    (h : IsStandardRealBM β P) (t : ℝ≥0) : Measurable (β t) :=
  (isStandardRealBM_iff.1 h).1 t

theorem IsStandardRealBM.isPreBrownianReal [IsProbabilityMeasure P] {β : ℝ≥0 → Ω → ℝ}
    (h : IsStandardRealBM β P) : IsPreBrownianReal β P :=
  (isStandardRealBM_iff.1 h).2.2

/-- Real-valued Brownian motion and crefdef:bm with d=1 (d1): the increment has law `N(0, t-s)`. -/
theorem IsStandardRealBM.hasLaw_increment [IsProbabilityMeasure P] {β : ℝ≥0 → Ω → ℝ}
    (h : IsStandardRealBM β P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => β t ω - β s ω) (gaussianReal 0 (t - s)) P := by
  have := (h.isPreBrownianReal.shift s).hasLaw_eval (t - s)
  have e : s + (t - s) = t := add_tsub_cancel_of_le hst
  simpa [e] using this

/-- Real-valued Brownian motion and crefdef:bm with d=1 (d1): the increment is independent of `ℱ_s`. -/
theorem IsStandardRealBM.indep_increment [IsProbabilityMeasure P] {β : ℝ≥0 → Ω → ℝ}
    (h : IsStandardRealBM β P) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => β t ω - β s ω) inferInstance)
      (realFiltration β s) P := by
  have := IsStandardBrownianMotion.indep_increment h hst
  rw [bmFiltration_toVec1] at this
  refine indep_of_indep_of_le_left this ?_
  have e : (fun ω => β t ω - β s ω) =
      (fun z : Fin 1 → ℝ => z 0) ∘ (fun ω => toVec1 β t ω - toVec1 β s ω) := rfl
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply 0).comap_le

/-- Real-valued Brownian motion and crefdef:bm with d=1 (d2): `-β`. -/
theorem IsStandardRealBM.neg [IsProbabilityMeasure P] {β : ℝ≥0 → Ω → ℝ}
    (h : IsStandardRealBM β P) : IsStandardRealBM (fun t ω => -β t ω) P :=
  IsStandardBrownianMotion.neg h

/-- Real-valued Brownian motion and crefdef:bm with d=1 (d2): the shift `sh_a β`. -/
theorem IsStandardRealBM.shift [IsProbabilityMeasure P] {β : ℝ≥0 → Ω → ℝ}
    (h : IsStandardRealBM β P) (a : ℝ≥0) :
    IsStandardRealBM (fun t ω => β (a + t) ω - β a ω) P :=
  IsStandardBrownianMotion.shift h a

/-- Real-valued Brownian motion and crefdef:bm with d=1 (d2): scaling `t ↦ c^{-1/2} β(c t)`. -/
theorem IsStandardRealBM.scaling [IsProbabilityMeasure P] {β : ℝ≥0 → Ω → ℝ}
    (h : IsStandardRealBM β P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsStandardRealBM (fun t ω => (Real.sqrt c)⁻¹ * β (c * t) ω) P := by
  have hc' : (0 : ℝ) < c := by positivity
  exact IsStandardBrownianMotion.scaling h (a := (Real.sqrt c)⁻¹) hc (by
    rw [inv_pow, Real.sq_sqrt hc'.le]; field_simp)

/-- Real-valued Brownian motion and crefdef:bm with d=1 (d3): the discrete stopping lemma for a real Brownian motion. -/
theorem IsStandardRealBM.lintegral_discrete_stopping [IsProbabilityMeasure P] {β : ℝ≥0 → Ω → ℝ}
    (h : IsStandardRealBM β P) {T : Set ℝ≥0} (hT : T.Countable) {τ : Ω → ℝ≥0∞}
    (hτT : ∀ ω, τ ω ≠ ∞ → ∃ a ∈ T, τ ω = a)
    (hτ : ∀ a ∈ T, MeasurableSet[realFiltration β a] {ω | τ ω = a})
    {E : Set Ω} (hE : ∀ a ∈ T, MeasurableSet[realFiltration β a] (E ∩ {ω | τ ω = a}))
    {Φ : ℝ → (ℝ≥0 → ℝ) → ℝ≥0∞} (hΦ : Measurable (Function.uncurry Φ)) :
    ∫⁻ ω, (E ∩ {ω | τ ω < ∞}).indicator
        (fun ω => Φ (β (τ ω).toNNReal ω) (realShift β (τ ω).toNNReal ω)) ω ∂P =
      ∫⁻ ω, (E ∩ {ω | τ ω < ∞}).indicator
        (fun ω => ∫⁻ w, Φ (β (τ ω).toNNReal ω) w ∂realWiener) ω ∂P := by
  have hΦ' : Measurable (Function.uncurry fun (z : Fin 1 → ℝ) (w : PathSpace 1) =>
      Φ (z 0) (iotaBarInv w)) :=
    hΦ.comp (show Measurable fun p : (Fin 1 → ℝ) × PathSpace 1 => (p.1 0, iotaBarInv p.2) from
      ((measurable_pi_apply 0).comp measurable_fst).prodMk
        (measurable_iotaBarInv.comp measurable_snd))
  have key := IsStandardBrownianMotion.lintegral_discrete_stopping h hT hτT
    (fun a ha => by rw [bmFiltration_toVec1]; exact hτ a ha)
    (fun a ha => by rw [bmFiltration_toVec1]; exact hE a ha) hΦ'
  refine key.trans (lintegral_congr fun ω => ?_)
  by_cases hω : ω ∈ E ∩ {ω | τ ω < ∞}
  · simp only [Set.indicator_of_mem hω]
    rw [realWiener]
    symm
    exact lintegral_map (f := fun w' => Φ (β (τ ω).toNNReal ω) w')
      (hΦ.comp (measurable_const.prodMk measurable_id)) measurable_iotaBarInv
  · simp [Set.indicator_of_notMem hω]

omit mΩ in
/-- The norm of `β̄` is `|β|`. -/
lemma norm_toVec1 (β : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ‖toVec1 β t ω‖ = |β t ω| := by
  obtain ⟨i, hi⟩ := exists_abs_eq_norm (toVec1 β t ω) one_pos
  rw [hi]
  rfl

/-- Real-valued Brownian motion and crefdef:bm with d=1 (d5): joint measurability of `(s, ω) ↦ β(s, ω)`. -/
theorem IsStandardRealBM.measurable_uncurry [IsProbabilityMeasure P] {β : ℝ≥0 → Ω → ℝ}
    (h : IsStandardRealBM β P) : Measurable (Function.uncurry β) :=
  (measurable_pi_apply 0).comp (IsStandardBrownianMotion.measurable_uncurry h)

end ElboimSly.Brownian
