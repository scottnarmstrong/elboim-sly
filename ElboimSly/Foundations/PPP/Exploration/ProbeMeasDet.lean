/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ProbeMeas
import Mathlib

/-!
# Measurability for deterministic probes

The deterministic case of measurability for parametrized probes (b).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [SigmaFinite μ] {R : S → ℝ≥0∞}
  {h : ℝ≥0}

theorem measurable_probeRho (hR : Measurable R) : Measurable (probeRho μ R h) := by
  classical
  unfold probeRho
  refine Measurable.min measurable_const (Measurable.iInf fun q => ?_)
  simp_rw [iInf_eq_if]
  refine Measurable.ite ?_ measurable_const measurable_const
  have hZ : MeasurableSet {x : S | R x ≤ ratTime q} := measurableSet_le hR measurable_const
  have h1 : Measurable fun ν : Measure S => tau μ ν {x | R x ≤ ratTime q} :=
    (Measure.measurable_coe hZ).comp (measurable_tau μ)
  exact MeasurableSet.inter (MeasurableSet.const _)
    (MeasurableSet.inter (MeasurableSet.const _) (measurableSet_le measurable_const h1))

theorem measurable_probeV (hR : Measurable R) : Measurable (probeV μ R h) := by
  have hρ := measurable_probeRho μ (h := h) hR
  let Z : Set (Measure S × S) := {q | R q.2 ≤ probeRho μ R h q.1}
  have hZ : MeasurableSet Z := measurableSet_le (hR.comp measurable_snd) (hρ.comp measurable_fst)
  have h1 := (measurable_tau_restrict_section μ hZ).comp
    (measurable_id.prodMk measurable_id : Measurable fun ν : Measure S => (ν, ν))
  exact h1

theorem measurable_probeStep (hR : Measurable R) : Measurable (probeStep μ R h) :=
  (measurable_probeRho μ hR).prodMk (measurable_probeV μ hR)

theorem measurable_probeRenew (hR : Measurable R) :
    Measurable fun p : Measure S × Measure S => probeRenew μ R h p.1 p.2 := by
  have hρ := (measurable_probeRho μ (h := h) hR).comp
    (measurable_fst : Measurable fun p : Measure S × Measure S => p.1)
  let Z : Set ((Measure S × Measure S) × S) := {q | R q.2 ≤ probeRho μ R h q.1.1}
  have hZ : MeasurableSet Z :=
    measurableSet_le (hR.comp measurable_snd) (hρ.comp measurable_fst)
  have h1 := (measurable_tau_restrict_section μ hZ.compl).comp
    (measurable_id.prodMk measurable_fst :
      Measurable fun p : Measure S × Measure S => (p, p.1))
  have h2 := (measurable_tau_restrict_section μ hZ).comp
    (measurable_id.prodMk measurable_snd :
      Measurable fun p : Measure S × Measure S => (p, p.2))
  exact measurable_add_measure.comp (h1.prodMk h2)

end ElboimSly
