/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycHitCov
public import ElboimSly.Foundations.Cyclic.CycRegenEnvAe
public import ElboimSly.Foundations.Cyclic.CycSchemeEquiv
public import ElboimSly.Foundations.PPP.Exploration.Section
public import Mathlib

/-!
# ES22 Lemma 2.1 (b): the re-indexing `Sh_z` of the environment

ES22 Lemma 2.1 (b), "Re-indexing". For `z = (k, x, a)` the map
`cycShiftMap z` sends `(k, e, θ) ↦ (0, φ_{(x,a)}(e, θ))` and `(k + 1 + j, e, θ) ↦ (j + 1, e, θ)`
(copies are indexed from `0`, so `k` is the written proof's `k - 1`). Put
`cycShift z ν = (cycShiftMap z)_* (τ(ν)|_{copies ≥ k})`. Then `(z, ν) ↦ cycShift z ν` is
measurable (`measurable_cycShift`).
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The shift parameters `z = (k, x, a)`. -/
abbrev ShiftPar (d : ℕ) : Type := ℕ × (Fin d → ℤ) × ℝ

/-- `(k, e, θ) ↦ (0, φ_{(x,a)}(e, θ))` and `(k + 1 + j, e, θ) ↦ (j + 1, e, θ)`. -/
noncomputable def cycShiftMap (z : ShiftPar d) (p : ℕ × RingSpace d β) : ℕ × RingSpace d β :=
  if p.1 ≤ z.1 then (0, hitPhi z.2.1 z.2.2 p.2) else (p.1 - z.1, p.2)

/-- The copies `≥ k`. -/
def shiftDom (z : ShiftPar d) : Set (ℕ × RingSpace d β) := {p | z.1 ≤ p.1}

theorem measurable_cycShiftMap :
    Measurable fun q : ShiftPar d × (ℕ × RingSpace d β) => cycShiftMap (β := β) q.1 q.2 := by
  unfold cycShiftMap
  refine Measurable.ite ?_ ?_ ?_
  · exact measurableSet_le (measurable_fst.comp measurable_snd) (measurable_fst.comp measurable_fst)
  · refine measurable_const.prodMk ?_
    exact measurable_hitPhi.comp
      (((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
  · exact ((measurable_fst.comp measurable_snd).sub (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_snd)

theorem measurable_cycShiftMap_at (z : ShiftPar d) :
    Measurable (cycShiftMap (β := β) z) :=
  measurable_cycShiftMap.comp measurable_prodMk_left

theorem measurableSet_shiftDom (z : ShiftPar d) :
    MeasurableSet (shiftDom (β := β) z) :=
  measurableSet_le measurable_const measurable_fst

instance : SigmaFinite (cycIntensity ℕ d β) := by
  unfold cycIntensity; infer_instance

/-- `Sh_z ν = (Sh_z)_* (τ(ν)|_{copies ≥ k})`. -/
noncomputable def cycShift (z : ShiftPar d) (ν : Measure (ℕ × RingSpace d β)) :
    Measure (ℕ × RingSpace d β) :=
  ((tau (cycIntensity ℕ d β) ν).restrict (shiftDom z)).map (cycShiftMap z)

theorem measurable_cycShift :
    Measurable fun p : ShiftPar d × Measure (ℕ × RingSpace d β) => cycShift p.1 p.2 := by
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  have : (fun p : ShiftPar d × Measure (ℕ × RingSpace d β) => cycShift p.1 p.2 B) =
      fun p => tau (cycIntensity ℕ d β) p.2 (Prod.mk p.1 ⁻¹'
        {q : ShiftPar d × (ℕ × RingSpace d β) |
          q.2 ∈ shiftDom q.1 ∧ cycShiftMap q.1 q.2 ∈ B}) := by
    funext p
    unfold cycShift
    rw [Measure.map_apply (measurable_cycShiftMap_at p.1) hB,
      Measure.restrict_apply (measurable_cycShiftMap_at p.1 hB)]
    congr 1
    ext y
    simp [and_comm]
  rw [this]
  refine measurable_tau_section (cycIntensity ℕ d β) ?_
  refine MeasurableSet.inter ?_ (measurable_cycShiftMap hB)
  exact measurableSet_le (measurable_fst.comp measurable_fst) (measurable_fst.comp measurable_snd)

end ElboimSly.Cyclic

end
