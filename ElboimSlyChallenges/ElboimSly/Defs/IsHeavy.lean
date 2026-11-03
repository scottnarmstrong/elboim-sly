/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSlyChallenges.ElboimSly.Defs.VisitedSet
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic

/-!
# IsHeavy

Visited set, heavy block (ES22 §3).
-/

public section

namespace ElboimSly

/-- The block `B(x, r) = {v : ‖v - x‖ ≤ r}` (closed `ℓ∞` box, ES22 §3) is *heavy for `w` on
`[a, t]`*: `|B(x,r) ∩ V_{[a,t]}(w)| ≥ r^{5/2}`, for real `r > 0`. Visited set, heavy block.
`|·|` on vertex sets is cardinality (reading choices (c)); the intersection is finite. -/
@[expose] def IsHeavy {d : ℕ} (w : ℝ → Fin d → ℤ) (a t : ℝ) (x : Fin d → ℤ) (r : ℝ) : Prop :=
  0 < r ∧ r ^ (5 / 2 : ℝ) ≤ (({v : Fin d → ℤ | ‖v - x‖ ≤ r} ∩ visitedSet w a t).ncard : ℝ)

end ElboimSly

end
