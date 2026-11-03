/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IndH1
public import ElboimSly.Frozen.Defs.IndH2
public import ElboimSly.Frozen.Defs.IndH3
public import ElboimSly.Frozen.Defs.IndH4
public import ElboimSly.Frozen.Defs.IndH5
public import Mathlib.Basic.Real.Basic

/-!
# IndHyp

The hypotheses mathbf H(β,n,t_0) (the hypotheses `H(β, n, t₀)`).
-/

public section

open MeasureTheory

namespace ElboimSly

/-- The hypotheses `H(β, n, t₀)` in dimension `d`: (H1)-(H4) for the regenerated walk built from the
copies of a Poisson point process `N` of intensity `# ⊗ μ_β` on `ℕ × S_β` (the constructions of the regenerated walk (i)),
and (H5) for a Poisson point process `N` of intensity `μ_β` on `S_β` (one environment, not
regenerated), each on every probability space `(Ω, P)` of universe 0 (the statements depend only on
the law). The hypotheses mathbf H(β,n,t_0). -/
@[expose] noncomputable def IndHyp (d : ℕ) (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ) : Prop :=
  (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β)),
      IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P →
        IndH1 P N n t₀ ∧ IndH2 P N n t₀ ∧ IndH3 P N n t₀ ∧ IndH4 P N n t₀) ∧
  (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (RingSpace d β)),
      IsPoissonPointProcess N (ringIntensity d β) P → IndH5 P N n t₀)

end ElboimSly

end
