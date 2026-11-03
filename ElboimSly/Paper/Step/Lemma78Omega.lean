/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Shift
public import ElboimSly.Paper.Step.Lemma78Setting2
public import ElboimSly.Paper.Heavy.PiecesClosing
public import ElboimSly.Foundations.Cyclic.CycClosing
public import Mathlib

/-!
# The path-level consequences of `Ω`

ES22 Lemma 6.8 (hypotheses) and the event cH_1 (first line of its proof), ES22 §7. On `Ω(0,u,0,q;T)` for a good environment `ν`, with `W₁ = W^ν_{0,0}`,
`W₂ = W^ν_{u,q}` and `tk ≤ T`:
* no segment of `W₁` starting at an integer cyclic time closes within `tk`;
* no segment of `W₂` starting at `b` with `q + b` an integer cyclic time closes within `tk`;
* no pair of segments merges (the cross merge of `Step78CrossMerge` is a merge by time `T`);
* `T < T(W₁)` and `T < T(W₂ - u)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- `t_reg ≤ T` means that `W_{0,0}` closes by time `T`. -/
theorem cycClosesBy_of_treg_le {T : ℝ} (h : cycTreg ν ≤ ENNReal.ofReal T) :
    cycClosesBy ν 0 0 T := by
  have hβ : 0 < β := Fact.out
  have hlt : cycTreg ν < ⊤ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  obtain ⟨n, hn, h0, he⟩ := exists_cycTreg_eq hlt
  refine ⟨n, hn, ?_, h0⟩
  rw [he] at h
  have hT : 0 ≤ T := by
    by_contra hc
    push Not at hc
    have h1 : ENNReal.ofReal ((n : ℝ) * β) ≤ 0 := by
      have := h.trans (le_of_eq (ENNReal.ofReal_of_nonpos hc.le))
      simpa using this
    have h2 : 0 < ENNReal.ofReal ((n : ℝ) * β) := by
      apply ENNReal.ofReal_pos.2
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    exact absurd h1 (not_le.2 h2)
  exact (ENNReal.ofReal_le_ofReal_iff hT).1 h

/-- A closed segment of `W_{0,0}` (of length `≤ T`) gives a closing by time `T`. -/
theorem cycClosesBy_of_segClosed (hν : Good ν) {T tk a : ℝ} (hk : tk ≤ T)
    (h : SegClosed β tk (fun s : ℝ => cycWalk ν 0 0 s) a) : cycClosesBy ν 0 0 T := by
  obtain ⟨v, hv0, hvk, ⟨ℓ, hℓ⟩, hW⟩ := h
  have hlt : a < a + v := by linarith
  have := cycTreg_le_of_eq hν hlt (k := ℓ) (by rw [← hℓ]; ring) hW
  refine cycClosesBy_of_treg_le (this.trans ?_)
  rw [add_sub_cancel_left]
  exact ENNReal.ofReal_le_ofReal (hvk.trans hk)

theorem not_segClosed_of_omega₁ (hν : Good ν) {T tk a : ℝ} (hk : tk ≤ T)
    (hΩ : ¬ cycClosesBy ν 0 0 T) : ¬ SegClosed β tk (fun s : ℝ => cycWalk ν 0 0 s) a :=
  fun h => hΩ (cycClosesBy_of_segClosed hν hk h)

/-- The same for `W₂ = W_{u,q}`, through `N* = stepShiftEnv u (-q) ν`. -/
theorem not_segClosed_of_omega₂ (hν : Good ν) (u : Fin d → ℤ) (q : ℝ) {T tk b : ℝ}
    (hk : tk ≤ T) (hΩ : ¬ cycClosesBy ν u q T) :
    ¬ SegClosed β tk (fun s : ℝ => cycWalk ν u q s) b := by
  intro h
  apply hΩ
  have hg := good_stepShiftEnv hν u (-q)
  have h' : SegClosed β tk (fun s : ℝ => cycWalk (stepShiftEnv u (-q) ν) 0 0 s) b := by
    obtain ⟨v, hv0, hvk, hℓ, hW⟩ := h
    refine ⟨v, hv0, hvk, hℓ, ?_⟩
    have hW' : cycWalk ν u q (b + v) = cycWalk ν u q b := hW
    simp only [cycWalk_stepShiftEnv_all hν u q]
    rw [hW']
  obtain ⟨k, hk1, hk2, hk3⟩ := cycClosesBy_of_segClosed hg hk h'
  refine ⟨k, hk1, hk2, ?_⟩
  rw [cycWalk_stepShiftEnv_all hν u q] at hk3
  exact sub_eq_zero.1 hk3

omit [Fact (0 < β)] in
/-- A cross merge of segments of length `tk`, with `a + tk ≤ T` and `b + tk ≤ T`, is a merge by
time `T`. -/
theorem not_crossMerge_of_omega (u : Fin d → ℤ) (q : ℝ) {T tk a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hatk : a + tk ≤ T) (hbtk : b + tk ≤ T)
    (hΩ : ¬ cycMerges ν 0 u 0 q T) :
    ¬ Step78CrossMerge β tk q (fun s : ℝ => cycWalk ν 0 0 s) (fun s : ℝ => cycWalk ν u q s) a b := by
  rintro ⟨u₁, hu₁, u₂, hu₂, hW, ℓ, hℓ⟩
  apply hΩ
  refine ⟨a + u₁, b + u₂, ⟨by linarith [hu₁.1], by linarith [hu₁.2]⟩,
    ⟨by linarith [hu₂.1], by linarith [hu₂.2]⟩, ⟨ℓ, ?_⟩, hW⟩
  linarith

/-- `T < T(W_{0,0})` on `Ω`. -/
theorem lt_cycClosingTime_of_omega {T : ℝ} (hΩ : ¬ cycClosesBy ν 0 0 T) :
    ENNReal.ofReal T < cycClosingTime β (fun s : ℝ => cycWalk ν 0 0 s) := by
  rw [cycClosingTime_cycWalk]
  by_contra hc
  exact hΩ (cycClosesBy_of_treg_le (not_lt.1 hc))

/-- `T < T(W_{u,q} - u)` on `Ω`. -/
theorem lt_cycClosingTime_of_omega₂ (hν : Good ν) (u : Fin d → ℤ) (q : ℝ) {T : ℝ}
    (hΩ : ¬ cycClosesBy ν u q T) :
    ENNReal.ofReal T < cycClosingTime β (fun s : ℝ => cycWalk ν u q s - u) := by
  have : (fun s : ℝ => cycWalk ν u q s - u) =
      fun s : ℝ => cycWalk (stepShiftEnv u (-q) ν) 0 0 s := by
    funext s; rw [cycWalk_stepShiftEnv_all hν u q]
  rw [this]
  refine lt_cycClosingTime_of_omega ?_
  rintro ⟨k, hk1, hk2, hk3⟩
  apply hΩ
  refine ⟨k, hk1, hk2, ?_⟩
  rw [cycWalk_stepShiftEnv_all hν u q] at hk3
  exact sub_eq_zero.1 hk3

end ElboimSly.Paper.Step

end
