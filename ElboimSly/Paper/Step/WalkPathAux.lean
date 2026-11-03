/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.WalkPath
public import Mathlib

/-!
# Suprema over `WalkPath` are countable suprema

Support for second moment of a truncated endpoint. On `WalkPath d T` (right-continuous, finitely many jumps) a
bound `‖p q‖ ≤ K` on the countable set `walkCount T` (rational times and `T`) holds at every
time, so the event `sup_{t ≤ T} ‖p t‖ ≤ K` is the measurable event cut out by `walkCount T`.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The countable set of rational times together with the endpoint `T`. -/
def walkCount (T : ℝ≥0) : Set (Set.Icc (0 : ℝ≥0) T) :=
  {q | (q : ℝ≥0) = T ∨ ∃ r : ℚ, (((q : ℝ≥0) : ℝ)) = r}

/-- The endpoint `T` as an element of `[0, T]`. -/
def walkTop (T : ℝ≥0) : Set.Icc (0 : ℝ≥0) T := ⟨T, zero_le, le_rfl⟩

theorem walkTop_mem (T : ℝ≥0) : walkTop T ∈ walkCount T := Or.inl rfl

theorem walkCount_countable (T : ℝ≥0) : (walkCount T).Countable := by
  have h1 : ({q : Set.Icc (0 : ℝ≥0) T | (q : ℝ≥0) = T}).Countable :=
    (Set.subsingleton_of_forall_eq (walkTop T) (fun q hq => Subtype.ext hq)).countable
  have h2 : ({q : Set.Icc (0 : ℝ≥0) T | ∃ r : ℚ, (((q : ℝ≥0) : ℝ)) = r}).Countable := by
    have : {q : Set.Icc (0 : ℝ≥0) T | ∃ r : ℚ, (((q : ℝ≥0) : ℝ)) = r} =
        (fun q : Set.Icc (0 : ℝ≥0) T => ((q : ℝ≥0) : ℝ)) ⁻¹' (Set.range ((↑) : ℚ → ℝ)) := by
      ext q; simp only [mem_ofPred_eq, mem_preimage, mem_range]
      exact ⟨fun ⟨r, hr⟩ => ⟨r, hr.symm⟩, fun ⟨r, hr⟩ => ⟨r, hr.symm⟩⟩
    rw [this]
    exact (Set.countable_range _).preimage
      (NNReal.coe_injective.comp Subtype.val_injective)
  exact h1.union h2

/-- The sup norm of the real cast of an integer vector is its sup norm. -/
theorem norm_intCast_pi (v : Fin d → ℤ) : ‖(fun i => ((v i : ℤ) : ℝ))‖ = ‖v‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    simpa [Int.norm_eq_abs] using norm_le_pi_norm v i
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    have := norm_le_pi_norm (fun i => ((v i : ℤ) : ℝ)) i
    simpa [Int.norm_eq_abs] using this

end ElboimSly.Paper
