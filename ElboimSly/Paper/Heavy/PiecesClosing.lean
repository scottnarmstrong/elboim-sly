/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.PiecesPath
public import ElboimSly.Foundations.Cyclic.CycClosing

/-!
# Closing time, no-return property and restart for the pieces

The pieces are cyclic paths (a) and (c) (supplement).

For a good environment `μ`:
* `cycClosingTime_cycWalk`: `T(W^μ_{0,0}) = t_reg(μ)`;
* `hasNoReturn_cycWalk`: the no-return property;
* `cycWalk_restart_cycIntTimes`: `W(x + u) = W^μ_{W(x), q(x)}(u)` for `x ∈ CI_β`, `u ≥ 0`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {μ : Measure (RingSpace d β)}

omit [Fact (0 < β)] in
theorem cycClosingTime_cycWalk (μ : Measure (RingSpace d β)) :
    cycClosingTime β (fun s : ℝ => cycWalk μ 0 0 s) = cycTreg μ := by
  unfold cycClosingTime ElboimSly.cycTreg
  exact (iInf_subtype'' (fun ℓ : ℕ => 1 ≤ ℓ ∧ cycWalk μ 0 0 ((ℓ : ℝ) * β) = 0)
    (fun ℓ => ENNReal.ofReal ((ℓ : ℝ) * β))).symm

/-- The pieces are cyclic paths (a), no-return property. -/
theorem hasNoReturn_cycWalk (hμ : Good μ) : HasNoReturn β (fun s : ℝ => cycWalk μ 0 0 s) := by
  intro s s' hs' hlt hs ⟨k, hk⟩
  have hβ : 0 < β := Fact.out
  have hk1 : 1 ≤ k := by
    have : (0 : ℝ) < k := by
      by_contra hc
      push Not at hc
      nlinarith
    exact_mod_cast this
  rw [cycClosingTime_cycWalk] at hs
  exact cycWalk_ne_of_lt_treg hμ hs' hk1 hk hs

/-- The pieces are cyclic paths (c). Restart at a cyclic integer time `x`:
`W(x + u) = W_{W(x), q(x)}(u)` for `u ≥ 0`. -/
theorem cycWalk_restart_cycIntTimes (hμ : Good μ) {x : ℝ} (hx : 0 ≤ x) {u : ℝ} (hu : 0 ≤ u) :
    cycWalk μ 0 0 (x + u) = cycWalk μ (cycWalk μ 0 0 x) (cycIntPhase β x) u := by
  have hβ : 0 < β := Fact.out
  set ℓ : ℤ := ⌊x / β⌋ with hℓ
  have hq : cycIntPhase β x = x - ℓ * β := by
    unfold cycIntPhase; rw [hℓ]; ring
  rw [cycWalk_of_nonneg hμ 0 0 (by linarith), cycWalk_of_nonneg hμ 0 0 hx, zero_add, zero_add,
    cycWalk_of_nonneg hμ _ _ hu]
  have h1 := fwdTraj_restart hμ (0 : Fin d → ℤ) (a := 0) (c := x) hx (t := x + u) (by linarith)
  rw [h1]
  have h2 := fwdTraj_add_zsmul hμ (fwdTraj hμ 0 0 x) (cycIntPhase β x) ℓ
    (t := cycIntPhase β x + u) (by linarith)
  rw [hq] at h2 ⊢
  have e1 : x - ℓ * β + ℓ * β = x := by ring
  have e2 : x - ℓ * β + u + ℓ * β = x + u := by ring
  rw [e1, e2] at h2
  exact h2

end ElboimSly.Paper
