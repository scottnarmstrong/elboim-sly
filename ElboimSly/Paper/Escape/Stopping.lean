/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Blocks
public import ElboimSly.Paper.Escape.Phases
public import ElboimSly.Paper.Heavy.Taufast
public import Mathlib

/-!
# The walks `W_i` and the stopping times `τ_i`

The walks W_i and the stopping times tau_i; 𝒜_i, 𝒜, 𝒢(β').  The stopping rule is a pathwise rule applied to the
family of walks `W_i` (`i = 1, …, I`) started at the points `p_i`: `τ_i` is the first `t > 0` at
which one of the conditions (1)–(7) holds.

* `EscStopCond`: the disjunction of conditions (1)–(7) for walk `i` at time `t`, given the earlier
  stopping times `τ_ℓ`, `ℓ < i`.
* `escTauSeq`: the sequence `τ_i = inf {t > 0 : (1)–(7)}`, defined by strong recursion on `i`.
-/

@[expose] public section

namespace ElboimSly.Paper

variable {k : ℕ}

/-- The walks W_i and the stopping times tau_i: conditions (1)–(7) for walk `i` at time `t`.

* `n j`: the scale parameters, `β`: the regeneration scale, `I`: the number of points,
* `P ℓ`: the starting points `p_ℓ`, `W ℓ`: the walks `W_ℓ`,
* `Bm`: the half block `B^-` (for (6)), and `τ ℓ` the earlier stopping times (for (5)). -/
def EscStopCond (n j : ℕ) (β : ℝ) (I : ℕ) (P : ℕ → Fin (k + 2) → ℤ)
    (W : ℕ → ℝ → Fin (k + 2) → ℤ) (Bm : Set (Fin (k + 2) → ℤ)) (τ : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    Prop :=
  W i t = 0 ∨
  (Real.log β ≤ t ∧ ‖W i t - P i‖ ≤ 2 * Real.sqrt t / Real.log t) ∨
  pathTfast (W i) (Real.log (max t (Real.log β)) ^ 2) ≤ ENNReal.ofReal t ∨
  (∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ I ∧ ℓ ≠ i ∧ ‖W i t - P ℓ‖ ≤ (n : ℝ) ^ 17 / 6) ∨
  (∃ ℓ, 1 ≤ ℓ ∧ ℓ < i ∧ ∃ s, 0 ≤ s ∧ s ≤ τ ℓ ∧ ‖W i t - W ℓ s‖ ≤ 1) ∨
  Metric.infDist (fun c => ((W i t c : ℤ) : ℝ)) ((fun x c => ((x c : ℤ) : ℝ)) '' Bm) ≤
    (2 : ℝ) ^ j / 8 ∨
  t = 4 ^ n

open Classical in
/-- The walks W_i and the stopping times tau_i: the stopping times `τ_i = inf {t > 0 : (1)–(7) hold}`. -/
noncomputable def escTauSeq (n j : ℕ) (β : ℝ) (I : ℕ) (P : ℕ → Fin (k + 2) → ℤ)
    (W : ℕ → ℝ → Fin (k + 2) → ℤ) (Bm : Set (Fin (k + 2) → ℤ)) : ℕ → ℝ
  | i => sInf {t : ℝ | 0 < t ∧ EscStopCond n j β I P W Bm
      (fun ℓ => if _ : ℓ < i then escTauSeq n j β I P W Bm ℓ else 0) i t}
termination_by i => i
decreasing_by assumption

end ElboimSly.Paper
