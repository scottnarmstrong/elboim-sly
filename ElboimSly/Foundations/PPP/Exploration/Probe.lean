/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.Section
import Mathlib

/-!
# Probes, step maps and the first-point kernel

Probe, step map, first-point kernel.

A *probe* is a measurable entrance time `R : S → [0,∞]` with a horizon `h ∈ [0,∞)` such that
`μ{R ≤ h} < ∞` and `μ{R = r} = 0` for `r ∈ [0,h]`. Here `h : ℝ≥0` and `R : S → ℝ≥0∞`.

* `probeRegion R r = D(r) = {R ≤ r}`, `probeMass μ R r = m(r) = μ(D r)`;
* `probeRho`, `probeV`, `probeStep`, `probeRenew`: the step map `St = (ρ, V)` and renewal map `𝖬`;
* `probeKernel`: the first-point kernel `K` on the outcome space `ℝ≥0∞ × Measure S`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S Θ : Type*} [MeasurableSpace S] [MeasurableSpace Θ]

/-- The outcome space of one exploration step, `𝕆 = [0,∞] × 𝓜(S)`. -/
abbrev Outcome (S : Type*) [MeasurableSpace S] : Type _ := ℝ≥0∞ × Measure S

/-- `D(r) = {R ≤ r}`, the probed region at parameter `r`. -/
def probeRegion (R : S → ℝ≥0∞) (r : ℝ≥0∞) : Set S := {x | R x ≤ r}

/-- `m(r) = μ(D(r))`. -/
noncomputable def probeMass (μ : Measure S) (R : S → ℝ≥0∞) (r : ℝ≥0∞) : ℝ≥0∞ :=
  μ (probeRegion R r)

/-- Probe, step map, first-point kernel: `(R, h)` is a probe for `μ`. -/
structure IsProbe (μ : Measure S) (R : S → ℝ≥0∞) (h : ℝ≥0) : Prop where
  measurable : Measurable R
  /-- (Pr1) -/
  mass_lt_top : μ (probeRegion R h) < ∞
  /-- (Pr2) -/
  measure_eq_zero : ∀ r : ℝ≥0, r ≤ h → μ {x | R x = r} = 0

/-- A nonnegative rational `q` viewed as a time in `[0,∞]`. -/
noncomputable def ratTime (q : ℚ) : ℝ≥0∞ := ((Real.toNNReal (q : ℝ) : ℝ≥0) : ℝ≥0∞)

/-- The decreasing exponential `e^{-a}` on `[0,∞]` (only used at finite `a`). -/
noncomputable def expNeg (a : ℝ≥0∞) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-a.toReal))

theorem measurable_expNeg : Measurable expNeg :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (ENNReal.measurable_toReal.neg))

section Defs

variable (μ : Measure S) [SigmaFinite μ] (R : S → ℝ≥0∞) (h : ℝ≥0)

/-- Probe, step map, first-point kernel: `ρ(ν) = inf ({h} ∪ {q ∈ ℚ : 0 ≤ q < h, τ(ν)(D q) ≥ 1})`. -/
noncomputable def probeRho (ν : Measure S) : ℝ≥0∞ :=
  min (h : ℝ≥0∞) (⨅ q : ℚ, ⨅ (_ : 0 ≤ q ∧ ratTime q < h ∧ 1 ≤ tau μ ν (probeRegion R (ratTime q))),
    ratTime q)

/-- `V(ν) = τ(ν)|_{D(ρ(ν))}`. -/
noncomputable def probeV (ν : Measure S) : Measure S :=
  (tau μ ν).restrict (probeRegion R (probeRho μ R h ν))

/-- The step map `St(ν) = (ρ(ν), V(ν))`. -/
noncomputable def probeStep (ν : Measure S) : Outcome S :=
  (probeRho μ R h ν, probeV μ R h ν)

/-- The renewal map `𝖬(ν, ν') = τ(ν)|_{S ∖ D(ρ(ν))} + τ(ν')|_{D(ρ(ν))}`. -/
noncomputable def probeRenew (ν ν' : Measure S) : Measure S :=
  (tau μ ν).restrict (probeRegion R (probeRho μ R h ν))ᶜ +
    (tau μ ν').restrict (probeRegion R (probeRho μ R h ν))

end Defs

section Kernel

variable (μ : Measure S) (R : S → ℝ≥0∞) (h : ℝ≥0)

/-- The first-point kernel
`K = e^{-m(h)} δ_{(h,0)} + Ψ_*(1_{D(h)} e^{-m∘R} · μ)`, `Ψ(x) = (R x, δ_x)`. -/
noncomputable def probeKernel : Measure (Outcome S) :=
  expNeg (probeMass μ R h) • Measure.dirac ((h : ℝ≥0∞), (0 : Measure S)) +
    (((μ.restrict (probeRegion R h)).withDensity fun x => expNeg (probeMass μ R (R x))).map
      fun x => (R x, Measure.dirac x))

end Kernel

end ElboimSly
