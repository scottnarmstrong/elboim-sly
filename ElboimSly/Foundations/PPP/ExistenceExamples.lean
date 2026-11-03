/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Existence
public import ElboimSly.Frozen.Defs.RingIntensity
public import ElboimSly.Frozen.Defs.EdgeInstCountable
public import ElboimSly.Frozen.Defs.EdgeInstMeasurableSingletonClass
public import Mathlib

/-!
# Existence for the intensities used in the paper

Existence (the two bullets).

* `ringIntensity d β` on `RingSpace d β` (`# ⊗ Leb_β` on `Edge d × ℝ/βℤ`);
* `# ⊗ Leb|_{(0,∞)}` on `D × ℝ` for countable (e.g. finite) `D`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

universe u

namespace ElboimSly

instance sigmaFinite_ringIntensity (d : ℕ) (β : ℝ) [Fact (0 < β)] :
    SigmaFinite (ringIntensity d β) := by
  unfold ringIntensity
  infer_instance

/-- Existence, first bullet: a PPP on `RingSpace d β` with intensity
`ringIntensity d β`. -/
theorem exists_isPoissonPointProcess_ringIntensity (d : ℕ) (β : ℝ) [Fact (0 < β)] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (N : Ω → Measure (RingSpace d β)),
      IsProbabilityMeasure P ∧ IsPoissonPointProcess N (ringIntensity d β) P ∧
        ∀ ω, N ω ∈ lfSet (ringIntensity d β) :=
  exists_isPoissonPointProcess (ringIntensity d β)

/-- The intensity `# ⊗ Leb|_{(0,∞)}` on `D × ℝ`. -/
noncomputable def clockIntensity (D : Type*) [MeasurableSpace D] : Measure (D × ℝ) :=
  Measure.count.prod (volume.restrict (Set.Ioi (0 : ℝ)))

instance sigmaFinite_clockIntensity (D : Type*) [MeasurableSpace D] [Countable D]
    [MeasurableSingletonClass D] : SigmaFinite (clockIntensity D) := by
  unfold clockIntensity
  infer_instance

/-- Existence, second bullet: a PPP on `D × ℝ` with intensity
`count ⊗ Leb|_{(0,∞)}`, for countable (in particular finite) `D` with discrete `σ`-algebra. -/
theorem exists_isPoissonPointProcess_clockIntensity (D : Type u) [MeasurableSpace D]
    [Countable D] [MeasurableSingletonClass D] :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (N : Ω → Measure (D × ℝ)),
      IsProbabilityMeasure P ∧ IsPoissonPointProcess N (clockIntensity D) P ∧
        ∀ ω, N ω ∈ lfSet (clockIntensity D) :=
  exists_isPoissonPointProcess (clockIntensity D)

end ElboimSly
