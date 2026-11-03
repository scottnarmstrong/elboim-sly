/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# VisitedSet

Visited set, heavy block (ES22 §3).
-/

public section

namespace ElboimSly

/-- The visited set `V_{[a,t]}(w) := {w(s) : a ≤ s ≤ t}`. Visited set, heavy block. -/
@[expose] def visitedSet {d : ℕ} (w : ℝ → Fin d → ℤ) (a t : ℝ) : Set (Fin d → ℤ) :=
  w '' Set.Icc a t

end ElboimSly

end
