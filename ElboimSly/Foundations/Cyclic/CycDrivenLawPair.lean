/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.OneStepDisc
public import Mathlib

/-!
# Independent copies of a Poisson point process, in law

Several walks explored one after another (the explorations need an independent copy `N'` of the
Poisson point process `N`; the statement of the laws does not).

For a Poisson point process `N` with law `W = P.map N` on `Measure S`, the two coordinates of
`(Measure S)²` under `W ⊗ W` are independent Poisson point processes with the same law as `N`.
Hence a statement about the law of a measurable function of `N` may be proved with copies.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {N : Ω → Measure S}

namespace IsPoissonPointProcess

theorem isPPPLaw_map (h : IsPoissonPointProcess N μ P) : IsPPPLaw μ (P.map N) :=
  h.of_map_eq (N' := fun ν : Measure S => ν) (P' := P.map N) measurable_id (by simp)

/-- The pair of coordinates of `W ⊗ W`, `W = Law(N)`: independent PPPs of intensity `μ`, with
`N' = fst` independent of `N = snd`. -/
theorem indep_pair [SigmaFinite μ] (h : IsPoissonPointProcess N μ P) :
    IsPoissonPointProcess (fun p : Measure S × Measure S => p.2) μ ((P.map N).prod (P.map N)) ∧
    IsPoissonPointProcess (fun p : Measure S × Measure S => p.1) μ ((P.map N).prod (P.map N)) ∧
    IndepFun (fun p : Measure S × Measure S => p.1) (fun p : Measure S × Measure S => p.2)
      ((P.map N).prod (P.map N)) :=
  ⟨isPPPLaw_snd h.isPPPLaw_map, isPPPLaw_fst h.isPPPLaw_map, indepFun_fst_snd_prod h.isPPPLaw_map⟩

end IsPoissonPointProcess

end ElboimSly

end
