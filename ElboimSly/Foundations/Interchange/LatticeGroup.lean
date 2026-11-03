/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.SymmDef
import Mathlib

/-!
# The generators of `G_d`

Lattice and time symmetries.

Translations, coordinate permutations and coordinate reflections are lattice automorphisms, so
`latticeMeasure`, `Good` preservation and covariance apply to the group `G_d` they generate.
-/

@[expose] public section

namespace ElboimSly.Interchange

variable {d : ℕ}

/-- Translation `x ↦ x + z`. -/
def LatticeAut.translate (z : Fin d → ℤ) : LatticeAut d where
  toEquiv := Equiv.addRight z
  adj u v := by simp [LatticeAdj]

/-- Coordinate permutation `x ↦ x ∘ σ`. -/
def LatticeAut.permute (σ : Equiv.Perm (Fin d)) : LatticeAut d where
  toEquiv := Equiv.arrowCongr σ.symm (Equiv.refl ℤ)
  adj u v := by
    unfold LatticeAdj
    simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply, Equiv.symm_symm]
    rw [Equiv.sum_comp σ (fun i => |u i - v i|)]

/-- Reflection `x_i ↦ -x_i` of one coordinate. -/
def LatticeAut.reflect (i : Fin d) : LatticeAut d where
  toEquiv :=
    { toFun := fun x j => if j = i then -x j else x j
      invFun := fun x j => if j = i then -x j else x j
      left_inv := fun x => by funext j; by_cases h : j = i <;> simp [h]
      right_inv := fun x => by funext j; by_cases h : j = i <;> simp [h] }
  adj u v := by
    unfold LatticeAdj
    refine Eq.congr (Finset.sum_congr rfl fun j _ => ?_) rfl
    by_cases h : j = i
    · subst h; simp; rw [← abs_neg]; congr 1; ring
    · simp [h]

end ElboimSly.Interchange
