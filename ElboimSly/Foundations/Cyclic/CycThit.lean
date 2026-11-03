/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.RegenWalk

/-!
# Hitting the history; moving fast

Hitting the history; moving fast (ES22 §2, ES22 §2, ES22 §2).

The regenerated walk is `regenWalk ν` and `α` is `regenStart ν`. Both times are valued in `ℝ≥0∞`
(the infimum over the empty set is `∞`). The norm on `Fin d → ℤ` is the sup norm (D5).
-/

public section

open scoped ENNReal

namespace ElboimSly

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- `t_hit(t) := inf {s > t : ∃ s' ∈ s + βℤ, α(t) < s' < t, ‖W(s) - W(s')‖ ≤ 1}` for the regenerated
walk `W = regenWalk ν`. Hitting the history; moving fast, equation `eq:cyc-thit`. -/
@[expose] noncomputable def cycThit (ν : ℕ → MeasureTheory.Measure (RingSpace d β)) (t : ℝ) :
    ℝ≥0∞ :=
  ⨅ s ∈ {s : ℝ | t < s ∧ ∃ s' : ℝ, (∃ k : ℤ, s' = s + k * β) ∧ regenStart ν t < s' ∧ s' < t ∧
      ‖regenWalk ν s - regenWalk ν s'‖ ≤ 1}, ENNReal.ofReal s

/-- `t_fast(L) := inf {t > 0 : max_{s ∈ [t-1, t]} ‖W(t) - W(s)‖ ≥ L}` where `W(s) := W(0)` for `s < 0`
(deviation F44), for the regenerated walk `W = regenWalk ν`. Hitting the history; moving fast. The maximum
over `[t-1, t]` is expressed as an existential, which is equivalent for the piecewise-constant walk. -/
@[expose] noncomputable def cycTfast (ν : ℕ → MeasureTheory.Measure (RingSpace d β)) (L : ℝ) :
    ℝ≥0∞ :=
  ⨅ t ∈ {t : ℝ | 0 < t ∧ ∃ s : ℝ, t - 1 ≤ s ∧ s ≤ t ∧
      L ≤ ‖regenWalk ν t - regenWalk ν (max s 0)‖}, ENNReal.ofReal t

end ElboimSly

end
