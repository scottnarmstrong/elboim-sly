/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.LawInvariance
public import ElboimSly.Foundations.Cyclic.CycMeasurable
import Mathlib

/-!
# Invariance in law without the measurability hypothesis

Invariance in law, with measurability supplying the measurability of
`ν ↦ trajProc ν x a` (`measurable_trajProc`).
-/

@[expose] public section

open MeasureTheory ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]
  {N : Ω → Measure (RingSpace d β)} {P : Measure Ω} {ι : Type*}

/-- Spatial part: `Law(γ^N_{gx,a}) = Law(g ∘ γ^N_{x,a})`, jointly for a family. -/
theorem law_trajProc_lattice (h : IsPoissonPointProcess N (ringIntensity d β) P)
    (g : LatticeAut d) (x : ι → Fin d → ℤ) (a : ι → ℝ) :
    P.map (fun ω k => trajProc (N ω) (g.toEquiv (x k)) (a k)) =
      P.map (fun ω k s => g.toEquiv (trajProc (N ω) (x k) (a k) s)) :=
  law_trajProc_lattice_of_measurable h g x a
    (measurable_pi_iff.mpr fun _k => measurable_trajProc _ _)

/-- Time part: the law of `γ^N_{x,a}(a + ·)` does not depend on `a`. -/
theorem law_trajProc_shift (h : IsPoissonPointProcess N (ringIntensity d β) P)
    (r : ℝ) (x : ι → Fin d → ℤ) (a : ι → ℝ) :
    P.map (fun ω k => trajProc (N ω) (x k) (a k + r)) =
      P.map (fun ω k => trajProc (N ω) (x k) (a k)) :=
  law_trajProc_shift_of_measurable h r x a
    (measurable_pi_iff.mpr fun _k => measurable_trajProc _ _)

end ElboimSly.Cyclic

end
