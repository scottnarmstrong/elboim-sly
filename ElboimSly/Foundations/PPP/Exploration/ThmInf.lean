/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ThmDirac
import Mathlib

/-!
# Sequential first-point exploration: the revealed part, infinite horizon

Sequential first-point exploration (a), including `k = ∞`: `Z_∞` is the disjoint union of the
`D_j(ρ_j)` and `N|_{Z_∞} = ∑_j V_j`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U] {μ : Measure S}
  [SigmaFinite μ] (sch : ExplScheme μ U)

namespace ExplScheme

/-- The explored region `Z_∞` as a function of the whole history. -/
def Zinf (y : U × (ℕ → Outcome S)) : Set S := ⋃ k, sch.Z k (truncHist k y)

theorem Zinf_Hinf (x : U × Measure S) : sch.Zinf (sch.Hinf x) = ⋃ k, sch.Z k (sch.Hfun k x) := by
  simp [Zinf, truncHist_Hinf]

omit [SigmaFinite μ] in
theorem measurableSet_Zinf :
    MeasurableSet {p : (U × (ℕ → Outcome S)) × S | p.2 ∈ sch.Zinf p.1} := by
  have : {p : (U × (ℕ → Outcome S)) × S | p.2 ∈ sch.Zinf p.1} =
      ⋃ k, {p : (U × (ℕ → Outcome S)) × S | p.2 ∈ sch.Z k (truncHist k p.1)} := by
    ext p; simp [Zinf]
  rw [this]
  exact MeasurableSet.iUnion fun k => (sch.measurableSet_Z k).preimage
    (((measurable_truncHist k).comp measurable_fst).prodMk measurable_snd)

end ExplScheme

end ElboimSly
