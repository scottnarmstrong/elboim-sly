/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IndDelta
public import ElboimSly.Frozen.Defs.IsHeavy
public import Mathlib.Basic.Real.Basic

/-!
# IsRelaxedTimeWrt

Relaxed times (ES22 §3).
-/

public section

namespace ElboimSly

/-- The time `t` is *relaxed with respect to `w|[a,t]`*:
(R1) for every real `r ≥ β^δ`, the block `B(w(t), r)` is not heavy for `w` on `[a, t]`;
(R2) `‖w(t) - w(s)‖ ≥ β^δ` for every `s ∈ [a, t - β^{3δ}]`.
Relaxed times, with `δ = indDelta d` and real powers `β ^ δ`. -/
@[expose] noncomputable def IsRelaxedTimeWrt {d : ℕ} (β : ℝ) (w : ℝ → Fin d → ℤ) (a t : ℝ) :
    Prop :=
  (∀ r : ℝ, β ^ indDelta d ≤ r → ¬ IsHeavy w a t (w t) r) ∧
  (∀ s : ℝ, a ≤ s → s ≤ t - β ^ (3 * indDelta d) → β ^ indDelta d ≤ ‖w t - w s‖)

end ElboimSly

end
