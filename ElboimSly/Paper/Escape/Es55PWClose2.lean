/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55PWClose
public import ElboimSly.Foundations.Cyclic.CycWalkTraj
public import ElboimSly.Foundations.Interchange.TrajProps
public import Mathlib

/-!
# Step 1 of ES22 Lemma 5.5: restart and periodicity

ES22 Lemma 5.5, Step 1, "Conclusion of Step 1": "both `η` on `[β'-r_i-ε, β']` and
`Ŵ(· + t' - β')` on the same interval are `N¹`-paths (periodicity) with value `w` at the left end,
so they agree (existence and uniqueness of trajectories) and `Ŵ(t') = p_i`".

`pwc_restart`: if `t' = β' + mβ`, the forward trajectory `Ŵ` from `(0, 0)` equals `w` just below
`t' - r`, and the backward trajectory `η_{p,β'}` equals `w` just below `β' - r`, then
`Ŵ(τ + mβ) = η_{p,β'}(τ)` for all `τ ∈ [β' - r, β']`; in particular `Ŵ(t') = p`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {μ : Measure (RingSpace k β)}

/-- **Restart and periodicity.** -/
theorem pwc_restart (hμ : Good μ) (p w : Fin k → ℤ) {β' tp r : ℝ} (m : ℤ)
    (ht' : tp = β' + m * β) (hr : 0 ≤ r) (hrt : r < tp)
    (hη : ∃ a0 < β' - r, ∀ τ ∈ Ioo a0 (β' - r), bwdTraj hμ p β' τ = w)
    (hW : ∃ s0 < tp - r, ∀ s ∈ Ioo s0 (tp - r), fwdTraj hμ 0 0 s = w) :
    ∀ τ, β' - r ≤ τ → τ ≤ β' → fwdTraj hμ 0 0 (τ + m * β) = bwdTraj hμ p β' τ := by
  obtain ⟨a0, ha0, hη⟩ := hη
  obtain ⟨s0, hs0, hW⟩ := hW
  set a1 : ℝ := max (max a0 (s0 - m * β)) (-(m * β)) with ha1
  have h1 : a1 < β' - r := by
    refine max_lt (max_lt ha0 (by linarith)) (by linarith)
  set a : ℝ := (a1 + (β' - r)) / 2 with hadef
  have haa1 : a1 < a := by linarith
  have haβ : a < β' - r := by linarith
  have ha0' : a0 < a := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) haa1
  have hs0' : s0 < a + m * β := by
    have : s0 - m * β < a := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) haa1
    linarith
  have hnn : 0 ≤ a + m * β := by
    have : -(m * β) < a := lt_of_le_of_lt (le_max_right _ _) haa1
    linarith
  have hF : IsPathOn μ (a + m * β) tp (fwdTraj hμ 0 0) :=
    (fwdTraj_isPathOn hμ 0 0 tp).mono hnn le_rfl
  have hf : IsPathOn μ a β' (fun τ => fwdTraj hμ 0 0 (τ + m * β)) := by
    have := hF.shift (-m)
    simp only [Int.cast_neg, neg_mul, sub_neg_eq_add] at this
    rwa [show a + m * β + -(m * β) = a by ring, show tp + -(m * β) = β' by rw [ht']; ring] at this
  have hg : IsPathOn μ a β' (bwdTraj hμ p β') := bwdTraj_isPathOn hμ p a β'
  have hab : a ≤ β' := by linarith
  have hfa : fwdTraj hμ 0 0 (a + m * β) = w := hW _ ⟨hs0', by linarith⟩
  have hga : bwdTraj hμ p β' a = w := hη _ ⟨ha0', haβ⟩
  intro τ hτ1 hτ2
  exact IsPathOn.eq_of_left hab hf hg (hfa.trans hga.symm) τ ⟨by linarith, hτ2⟩

/-- In particular `Ŵ(t') = p`. -/
theorem pwc_restart_end (hμ : Good μ) (p w : Fin k → ℤ) {β' tp r : ℝ} (m : ℤ)
    (ht' : tp = β' + m * β) (hr : 0 ≤ r) (hrt : r < tp)
    (hη : ∃ a0 < β' - r, ∀ τ ∈ Ioo a0 (β' - r), bwdTraj hμ p β' τ = w)
    (hW : ∃ s0 < tp - r, ∀ s ∈ Ioo s0 (tp - r), fwdTraj hμ 0 0 s = w) :
    fwdTraj hμ 0 0 tp = p := by
  have := pwc_restart hμ p w m ht' hr hrt hη hW β' (by linarith) le_rfl
  rwa [bwdTraj_self, ← ht'] at this

end ElboimSly.Paper.Escape
