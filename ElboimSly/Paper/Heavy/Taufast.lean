/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycThit
public import ElboimSly.Paper.Heavy.CyclicPath

/-!
# The stopping times `τ_fast` and `τ_jump`

The stopping times tfast and heavyJ (ES22 §6; `τ_jump` is a supplement).

For a path `w : ℝ → Fin d → ℤ` and `L ≥ 1`:

* `pathTfast w L = inf {t > 0 : max_{s ∈ [t-1,t]} ‖w t - w s‖ ≥ L}`, with `w s = 0` for `s < 0`
  (evaluated at `max s 0`, as for `cycTfast`; a cyclic path has `w 0 = 0`);
* `pathTjump w L = inf {t > 0 : J_w(t-1,t] ≥ L}`.

Both are valued in `[0, ∞]`. For the regenerated walk, `pathTfast (regenWalk ν) L = cycTfast ν L`.
The statement-level instances `τ_fast := τ_fast(W; n³)` use `L = n ^ 3`.
-/

@[expose] public section

open scoped ENNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The stopping times tfast and heavyJ. `τ_fast(w; L) = inf {t > 0 : max_{s ∈ [t-1,t]} ‖w t - w s‖ ≥ L}`
(the maximum over `[t-1,t]` is expressed as an existential, equivalent for a step path). -/
noncomputable def pathTfast (w : ℝ → Fin d → ℤ) (L : ℝ) : ℝ≥0∞ :=
  ⨅ t ∈ {t : ℝ | 0 < t ∧ ∃ s : ℝ, t - 1 ≤ s ∧ s ≤ t ∧ L ≤ ‖w t - w (max s 0)‖},
    ENNReal.ofReal t

/-- The stopping times tfast and heavyJ. `τ_jump(w; L) = inf {t > 0 : J_w(t-1, t] ≥ L}`. -/
noncomputable def pathTjump (w : ℝ → Fin d → ℤ) (L : ℝ) : ℝ≥0∞ :=
  ⨅ t ∈ {t : ℝ | 0 < t ∧ L ≤ (cycJumpCount w (t - 1) t : ℝ)}, ENNReal.ofReal t

/-- The stopping times tfast and heavyJ. The instance `τ_fast(w) := τ_fast(w; n³)`. -/
noncomputable def pathTfastCube (w : ℝ → Fin d → ℤ) (n : ℕ) : ℝ≥0∞ :=
  pathTfast w ((n : ℝ) ^ 3)

/-- The stopping times tfast and heavyJ. The instance `τ_jump(w) := τ_jump(w; n³)`. -/
noncomputable def pathTjumpCube (w : ℝ → Fin d → ℤ) (n : ℕ) : ℝ≥0∞ :=
  pathTjump w ((n : ℝ) ^ 3)

end ElboimSly.Paper
