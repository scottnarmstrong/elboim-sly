/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiFilt
public import ElboimSly.Foundations.Cyclic.CycSchemeEquiv
public import ElboimSly.Foundations.PPP.Exploration.SegmentReal
public import ElboimSly.Foundations.PPP.Exploration.ThmStop
public import Mathlib

/-!
# Definitions

Several walks explored one after another. For a plan `P` and the environment `N`:

* `cycRegionAt P N s ω`: the region `R^𝒫_s` of `cycRec^𝒫(s) = Trunc_s(ρ^𝒫(N))`;
* `cycRegionStop P N T ω`: `R^𝒫_T` on `{T < ∞}` and `∅` on `{T = ∞}`;
* `tildeMeasure N N' Z ω`: `N|_{S ∖ Z} + N'|_Z`;
* `GSpace 𝒢₀`: the space `Ω` carrying the `σ`-algebra `𝒢₀` (the auxiliary variable `U`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

/-- The type `Ω` carrying a prescribed `σ`-algebra, used as the auxiliary space `𝕌` of the
exploration scheme (`σ(U) = 𝒢₀`). -/
def GSpace {Ω : Type*} (_ : MeasurableSpace Ω) : Type _ := Ω

instance GSpace.instMeasurableSpace {Ω : Type*} (m : MeasurableSpace Ω) :
    MeasurableSpace (GSpace m) := m

/-- The identity `Ω → GSpace 𝒢₀`. -/
def GSpace.mk {Ω : Type*} (m : MeasurableSpace Ω) (ω : Ω) : GSpace m := ω

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- `N|_{S ∖ Z} + N'|_Z`. -/
noncomputable def tildeMeasure {Ω S : Type*} [MeasurableSpace S] (N N' : Ω → Measure S)
    (Z : Ω → Set S) (ω : Ω) : Measure S :=
  (N ω).restrict (Z ω)ᶜ + (N' ω).restrict (Z ω)

/-- The region `R^𝒫_s` of `cycRec^𝒫(s) = Trunc_s(ρ^𝒫(N))`. -/
noncomputable def cycRegionAt {Ω : Type*} (P : CycPlan I d β) (N : Ω → Measure (CycS I d β))
    (s : ℝ≥0) (ω : Ω) : Set (CycS I d β) :=
  (CycRec.trunc s (P.envFinal (N ω))).region β

/-- `R^𝒫_T` on `{T < ∞}` and `∅` on `{T = ∞}`. -/
noncomputable def cycRegionStop {Ω : Type*} (P : CycPlan I d β) (N : Ω → Measure (CycS I d β))
    (T : Ω → WithTop ℝ≥0) (ω : Ω) : Set (CycS I d β) :=
  (T ω).recTopCoe ∅ (fun t => cycRegionAt P N t ω)

end ElboimSly.Cyclic

end
