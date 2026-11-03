/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.RegularB
public import Mathlib

/-!
# Regular functionals of pairs of paths: laws

Regular functionals of pairs of paths (supplement), part (c).

If `Z, Z'` are random elements of `Π_T` with almost surely regular paths and equal laws, then the
Lebesgue measures of (b) for `Z` and `Z'` are almost surely equal to the random variables
`Φ(Z)`, `Φ(Z')`, which have the same law (and so do the Lebesgue measures).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d k : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Regular functionals of pairs of paths (c). -/
theorem es8_regular_law {T L : ℝ≥0} (ρ : ℝ) (i j : Fin k) {P : Measure Ω} {P' : Measure Ω'}
    {Z : Ω → PathsOn d k T} {Z' : Ω' → PathsOn d k T} (hZ : Measurable Z)
    (hZ' : Measurable Z') (hreg : ∀ᵐ ω ∂P, IsRegularPaths T (Z ω))
    (hreg' : ∀ᵐ ω ∂P', IsRegularPaths T (Z' ω)) (hlaw : P.map Z = P'.map Z') :
    (∀ᵐ ω ∂P, lebMeas T L ρ i j (Z ω) = Phi T L ρ i j (Z ω)) ∧
      (∀ᵐ ω ∂P', lebMeas T L ρ i j (Z' ω) = Phi T L ρ i j (Z' ω)) ∧
      P.map (fun ω => Phi T L ρ i j (Z ω)) = P'.map (fun ω => Phi T L ρ i j (Z' ω)) ∧
      P.map (fun ω => lebMeas T L ρ i j (Z ω)) = P'.map (fun ω => lebMeas T L ρ i j (Z' ω)) := by
  have h1 : ∀ᵐ ω ∂P, lebMeas T L ρ i j (Z ω) = Phi T L ρ i j (Z ω) :=
    hreg.mono fun ω hω => (Phi_eq_lebMeas ρ hω).symm
  have h2 : ∀ᵐ ω ∂P', lebMeas T L ρ i j (Z' ω) = Phi T L ρ i j (Z' ω) :=
    hreg'.mono fun ω hω => (Phi_eq_lebMeas ρ hω).symm
  have hΦ := measurable_Phi (d := d) T L ρ i j
  have h3 : P.map (fun ω => Phi T L ρ i j (Z ω)) = P'.map (fun ω => Phi T L ρ i j (Z' ω)) := by
    have e1 : P.map (fun ω => Phi T L ρ i j (Z ω)) = (P.map Z).map (Phi T L ρ i j) :=
      (Measure.map_map hΦ hZ).symm
    have e2 : P'.map (fun ω => Phi T L ρ i j (Z' ω)) = (P'.map Z').map (Phi T L ρ i j) :=
      (Measure.map_map hΦ hZ').symm
    rw [e1, e2, hlaw]
  refine ⟨h1, h2, h3, ?_⟩
  rw [Measure.map_congr h1, Measure.map_congr h2, h3]

end ElboimSly.Paper
