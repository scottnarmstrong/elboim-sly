/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Pieces
public import ElboimSly.Paper.Heavy.Agree
public import ElboimSly.Paper.Heavy.PiecesPath

/-!
# The regenerated walk and its first piece up to `t_reg`

ES22 Lemma 6.2, Step 0 (the event is a function of the path of `W` up to `t_reg`);
The functionals before closing, the pieces are cyclic paths.

* `regenWalk_eq_piece0`: `W = W^{ν 0}` on `[0, T]` when `T ≤ t_reg`.
* `cycClosingTime_regenWalk`: `T(W) = t_reg(ν 0)`.
* `tauPrimeBlock_regen_iff`: `{τ'(B)(W) ≤ t_n ∧ t_reg} = {τ'(B)(W^{ν 0}) ≤ t_n ∧ t_reg}`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : ℕ → Measure (RingSpace d β)}

omit [Fact (0 < β)] in
theorem regenSigma_zero : regenSigma ν 0 = 0 := by simp [regenSigma]

theorem regenWalk_eq_piece0 (hν : ∀ k, Good (ν k)) {T : ℝ}
    (hTt : ENNReal.ofReal T ≤ cycTreg (ν 0)) :
    ∀ s ∈ Icc 0 T, regenWalk ν s = cycWalk (ν 0) 0 0 s := by
  intro s hs
  have := es6_pieces_b_walk hν (k := 0) (by rw [regenSigma_zero]; exact ENNReal.zero_lt_top)
    hs.1 ((ENNReal.ofReal_le_ofReal hs.2).trans hTt)
  rwa [regenSigma_zero, ENNReal.toReal_zero, zero_add] at this

theorem cycClosingTime_regenWalk (hν : ∀ k, Good (ν k)) (_hw : IsCyclicPath (regenWalk ν)) :
    cycClosingTime β (regenWalk ν) = cycTreg (ν 0) := by
  have hβ : 0 < β := Fact.out
  have hp := isCyclicPath_cycWalk (hν 0)
  have hc : cycClosingTime β (fun s : ℝ => cycWalk (ν 0) 0 0 s) = cycTreg (ν 0) :=
    cycClosingTime_cycWalk _
  have base : ∀ T' : ℝ, 0 ≤ T' → ENNReal.ofReal T' ≤ cycTreg (ν 0) →
      (cycClosingTime β (regenWalk ν) ≤ ENNReal.ofReal T' ↔
        cycTreg (ν 0) ≤ ENNReal.ofReal T') := by
    intro T' hT' hle
    have := cycClosingTime_le_iff_of_agree (w := regenWalk ν)
      (w' := fun s : ℝ => cycWalk (ν 0) 0 0 s) hβ hT' (regenWalk_eq_piece0 hν hle)
    rwa [hc] at this
  have key : ∀ T : ℝ, 0 ≤ T → (cycClosingTime β (regenWalk ν) ≤ ENNReal.ofReal T ↔
      cycTreg (ν 0) ≤ ENNReal.ofReal T) := by
    intro T hT
    by_cases h : ENNReal.ofReal T ≤ cycTreg (ν 0)
    · exact base T hT h
    · push Not at h
      have htr : cycTreg (ν 0) < ⊤ := h.trans ENNReal.ofReal_lt_top
      have hT' : ENNReal.ofReal (cycTreg (ν 0)).toReal = cycTreg (ν 0) :=
        ENNReal.ofReal_toReal htr.ne
      have hb := base (cycTreg (ν 0)).toReal ENNReal.toReal_nonneg hT'.le
      rw [hT'] at hb
      exact ⟨fun _ => h.le, fun _ => (hb.2 le_rfl).trans h.le⟩
  refine le_antisymm ?_ ?_
  · rcases eq_or_ne (cycTreg (ν 0)) ⊤ with h | h
    · rw [h]; exact le_top
    · have := (key (cycTreg (ν 0)).toReal ENNReal.toReal_nonneg).2
        (by rw [ENNReal.ofReal_toReal h])
      rwa [ENNReal.ofReal_toReal h] at this
  · rcases eq_or_ne (cycClosingTime β (regenWalk ν)) ⊤ with h | h
    · rw [h]; exact le_top
    · have := (key (cycClosingTime β (regenWalk ν)).toReal ENNReal.toReal_nonneg).1
        (by rw [ENNReal.ofReal_toReal h])
      rwa [ENNReal.ofReal_toReal h] at this

/-- The event `{τ'(B) ≤ t_n ∧ t_reg}` is the same for `W` and its first piece. -/
theorem tauPrimeBlock_regen_iff (hν : ∀ k, Good (ν k)) (hw : IsCyclicPath (regenWalk ν))
    (n m : ℕ) (ι : Fin d → ℤ) {tn : ℝ} :
    heavyTauPrimeBlock d n (regenWalk ν) m ι ≤ min (ENNReal.ofReal tn) (cycTreg (ν 0)) ↔
      heavyTauPrimeBlock d n (fun s : ℝ => cycWalk (ν 0) 0 0 s) m ι ≤
        min (ENNReal.ofReal tn) (cycTreg (ν 0)) := by
  set M := min (ENNReal.ofReal tn) (cycTreg (ν 0)) with hM
  have hMt : M ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
  have hMe : ENNReal.ofReal M.toReal = M := ENNReal.ofReal_toReal hMt
  have := heavyTauPrimeBlock_le_iff_of_agree hw (isCyclicPath_cycWalk (hν 0)) n m ι
    (T := M.toReal) ENNReal.toReal_nonneg
    (regenWalk_eq_piece0 hν (by rw [hMe]; exact min_le_right _ _))
  rwa [hMe] at this

end ElboimSly.Paper.Heavy
