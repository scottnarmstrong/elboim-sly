/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycEnvPath
public import ElboimSly.Foundations.Cyclic.CycMeasurable
public import ElboimSly.Foundations.Cyclic.GoodMeas
public import ElboimSly.Foundations.Cyclic.CycStepCoords
public import Mathlib

/-!
# Measurability of the environment world-lines

Measurability of record functionals (d). The set of good `ν` is measurable, the environment path
`(ν, δ) ↦ P^ν_δ` is measurable on it (into `CycPath d`), and so are the final record
`ν ↦ ρ^𝒫(ν)` and the records `Rec^𝒫(s)` once truncation is measurable.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]

omit [Countable I] [Fact (0 < β)] in
theorem measurable_cycSlice (ι : I) :
    Measurable (cycSlice ι : Measure (I × RingSpace d β) → Measure (RingSpace d β)) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have : (fun ν : Measure (I × RingSpace d β) => cycSlice ι ν s) =
      fun ν => ν (Prod.mk ι '' s) := by
    funext ν; unfold cycSlice; rw [(measurableEmbedding_prodMk_left ι).comap_apply]
  rw [this]
  exact Measure.measurable_coe ((measurableEmbedding_prodMk_left ι).measurableSet_image.mpr hs)

theorem measurableSet_cycGood :
    MeasurableSet {ν : Measure (I × RingSpace d β) | CycGood ν} := by
  have : {ν : Measure (I × RingSpace d β) | CycGood ν} =
      ⋂ ι : I, cycSlice ι ⁻¹' {μ : Measure (RingSpace d β) | Good μ} := by
    ext ν; simp [CycGood]
  rw [this]
  exact MeasurableSet.iInter fun ι => measurable_cycSlice ι measurableSet_good

/-- The good environments. -/
abbrev CycGoodSet (I : Type*) [MeasurableSpace I] (d : ℕ) (β : ℝ) [Fact (0 < β)] : Type _ :=
  {ν : Measure (I × RingSpace d β) // CycGood ν}

omit [Fact (0 < β)] in
theorem measurable_envMeasure_aux :
    Measurable (fun q : Measure (I × RingSpace d β) × CycData I d => envMeasure q.1 q.2) := by
  have : (fun q : Measure (I × RingSpace d β) × CycData I d => envMeasure q.1 q.2) =
      fun q => (fun (y : I × Bool) (ν : Measure (I × RingSpace d β)) =>
        if y.2 = true then cycSlice y.1 ν else reflectMeasure β (cycSlice y.1 ν))
          ((q.2.copy, q.2.fwd)) q.1 := by
    funext q; simp [envMeasure]
  rw [this]
  have h2 : Measurable (fun q : Measure (I × RingSpace d β) × (I × Bool) =>
      (fun (y : I × Bool) (ν : Measure (I × RingSpace d β)) =>
        if y.2 = true then cycSlice y.1 ν else reflectMeasure β (cycSlice y.1 ν)) q.2 q.1) := by
    refine measurable_from_prod_countable_left fun y => ?_
    by_cases h : y.2 = true
    · simp only [h, ite_true]; exact measurable_cycSlice y.1
    · simp only [h]; exact measurable_reflectMeasure.comp (measurable_cycSlice y.1)
  have hm : Measurable fun q : Measure (I × RingSpace d β) × CycData I d =>
      (q.1, (q.2.copy, q.2.fwd)) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  exact h2.comp hm

omit [Countable I] in
omit [MeasurableSingletonClass I] in
theorem envFn_eq_fwdTraj {ν : Measure (I × RingSpace d β)} {δ : CycData I d}
    (h : Good (cycSlice δ.copy ν)) (r : ℝ≥0) :
    envFn ν δ r = fwdTraj (good_envMeasure h) δ.start (δ.sgn * δ.phase) (δ.sgn * δ.phase + r) := by
  have := fwdTrajFn_eq (good_envMeasure h) (envFn_spec h)
  simp only [fwdTraj, fwdReal, add_sub_cancel_left, Real.toNNReal_coe]
  rw [this]

theorem measurable_envGood :
    Measurable (fun q : CycGoodSet I d β × CycData I d =>
      (⟨envMeasure q.1.1 q.2, good_envMeasure (q.1.2 q.2.copy)⟩ : GoodSet d β)) :=
  Measurable.subtype_mk (measurable_envMeasure_aux.comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))

theorem measurable_envFn (r : ℝ≥0) :
    Measurable (fun q : CycGoodSet I d β × CycData I d => envFn q.1.1 q.2 r) := by
  have h1 : Measurable (fun w : (GoodSet d β × ℝ × ℝ) × (Fin d → ℤ) =>
      fwdTraj w.1.1.2 w.2 w.1.2.1 w.1.2.2) :=
    measurable_from_prod_countable_left fun u => measurable_fwdTraj u
  have hsg : Measurable fun q : CycGoodSet I d β × CycData I d => q.2.sgn * q.2.phase := by
    have : Measurable fun δ : CycData I d => δ.sgn * δ.phase := by
      have hb : Measurable fun δ : CycData I d => δ.sgn := by
        have : (fun δ : CycData I d => δ.sgn) = fun δ => if δ.2.2.2 = true then 1 else -1 := by
          funext δ; unfold CycData.sgn CycData.fwd; split_ifs <;> rfl
        rw [this]
        exact Measurable.ite (measurableSet_eq_fun measurable_snd.snd.snd measurable_const)
          measurable_const measurable_const
      exact hb.mul (measurable_fst.comp (measurable_snd.comp measurable_snd))
    exact this.comp measurable_snd
  have hst : Measurable fun q : CycGoodSet I d β × CycData I d => q.2.start :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have h2 : Measurable (fun q : CycGoodSet I d β × CycData I d =>
      (((⟨envMeasure q.1.1 q.2, good_envMeasure (q.1.2 q.2.copy)⟩ : GoodSet d β),
        q.2.sgn * q.2.phase, q.2.sgn * q.2.phase + r), q.2.start)) :=
    ((measurable_envGood.prodMk (hsg.prodMk (hsg.add measurable_const))).prodMk hst)
  have := h1.comp h2
  convert this using 1
  funext q
  exact envFn_eq_fwdTraj (q.1.2 q.2.copy) r

theorem measurable_envPath :
    Measurable (fun q : CycGoodSet I d β × CycData I d => envPath q.1.1 q.2) := by
  have h : Measurable (fun q : CycGoodSet I d β × CycData I d => (envPath q.1.1 q.2).1) := by
    rw [CPath.measurable_iff]
    refine ⟨?_, fun r => ?_⟩
    · have : (fun q : CycGoodSet I d β × CycData I d => (envPath q.1.1 q.2).1.len) =
          fun _ => ⊤ := funext fun q => (envPath_len (q.1.2 q.2.copy)).1
      rw [this]; exact measurable_const
    · have : (fun q : CycGoodSet I d β × CycData I d => (envPath q.1.1 q.2).1.fn r) =
          fun q => envFn q.1.1 q.2 r := funext fun q => by
        rw [(envPath_len (q.1.2 q.2.copy)).2]
      rw [this]; exact measurable_envFn r
  exact Measurable.subtype_mk h

theorem CycPlan.measurable_envRule (P : CycPlan I d β) (k : ℕ) :
    Measurable fun q : CycGoodSet I d β × CycRecN I d k => envPath q.1.1 (P.start k q.2) := by
  have hsnd : Measurable fun q : CycGoodSet I d β × CycRecN I d k => q.2 := measurable_snd
  have hs : Measurable fun q : CycGoodSet I d β × CycRecN I d k => P.start k q.2 :=
    (P.measurable_start k).comp hsnd
  have hfst : Measurable fun q : CycGoodSet I d β × CycRecN I d k => q.1 := measurable_fst
  have h1 : Measurable fun q : CycGoodSet I d β × CycRecN I d k => (q.1, P.start k q.2) :=
    hfst.prodMk hs
  have hc := Measurable.comp (measurable_envPath (I := I) (d := d) (β := β)) h1
  exact hc

/-- Measurability of record functionals (d): `ν ↦ ρ^𝒫(ν)` is measurable on the good environments. -/
theorem CycPlan.measurable_envFinal (P : CycPlan I d β) :
    Measurable (fun ν : CycGoodSet I d β => P.envFinal ν.1) := by
  have h := P.measurable_cycFinal (α := CycGoodSet I d β)
    (path := fun ν k ρ => envPath ν.1 (P.start k ρ)) (P.measurable_envRule)
  exact h

end ElboimSly.Cyclic

end
