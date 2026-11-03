/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Dyadic blocks

Lattice, norms, edges, boxes, blocks (used by scales; the constants m_0, j, k, t'_k, entrance times s_i(B) and τ'(B)).

`heavyBlock m ι = 2^m ι + [0, 2^m)^d`, the block of `ℬ_m` with index `ι`; a vertex `x` lies in it
iff `x / 2^m = ι` (coordinatewise floor division).
-/

@[expose] public section

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The block `u + [0, 2^m)^d`, `u = 2^m ι`, of the partition `ℬ_m` of `ℤ^d`. -/
def heavyBlock (m : ℕ) (ι : Fin d → ℤ) : Set (Fin d → ℤ) :=
  {x | ∀ c, x c / 2 ^ m = ι c}

/-- The index of the block of `ℬ_m` containing `x`. -/
def heavyBlockIdx (m : ℕ) (x : Fin d → ℤ) : Fin d → ℤ := fun c => x c / 2 ^ m

theorem mem_heavyBlock_idx (m : ℕ) (x : Fin d → ℤ) : x ∈ heavyBlock m (heavyBlockIdx m x) :=
  fun _ => rfl

theorem heavyBlock_eq_of_mem {m : ℕ} {ι ι' : Fin d → ℤ} {x : Fin d → ℤ}
    (h : x ∈ heavyBlock m ι) (h' : x ∈ heavyBlock m ι') : ι = ι' := by
  funext c; rw [← h c, ← h' c]

/-- `ℬ_j` refines `ℬ_m` for `j ≤ m`. -/
theorem heavyBlock_refine {j m : ℕ} (hjm : j ≤ m) {ι' ι : Fin d → ℤ} {x : Fin d → ℤ}
    (hx : x ∈ heavyBlock j ι') (hxm : x ∈ heavyBlock m ι) : heavyBlock j ι' ⊆ heavyBlock m ι := by
  intro y hy c
  have h1 : y c / 2 ^ j = x c / 2 ^ j := (hy c).trans (hx c).symm
  have e : (2 : ℤ) ^ m = 2 ^ j * 2 ^ (m - j) := by rw [← pow_add]; congr 1; omega
  have key : ∀ z : ℤ, z / 2 ^ m = (z / 2 ^ j) / 2 ^ (m - j) := by
    intro z; rw [e, Int.ediv_ediv_of_nonneg (by positivity)]
  rw [key (y c), h1, ← key (x c)]
  exact hxm c

/-- Two vertices in the same block of `ℬ_j` are within `ℓ^∞` distance `2^j - 1`. -/
theorem abs_sub_lt_of_mem_heavyBlock {j : ℕ} {ι : Fin d → ℤ} {x y : Fin d → ℤ}
    (hx : x ∈ heavyBlock j ι) (hy : y ∈ heavyBlock j ι) (c : Fin d) :
    |x c - y c| < 2 ^ j := by
  have hp : (0 : ℤ) < 2 ^ j := by positivity
  have h1 := Int.emod_add_mul_ediv (x c) (2 ^ j)
  have h2 := Int.emod_add_mul_ediv (y c) (2 ^ j)
  have h3 := Int.emod_nonneg (x c) hp.ne'
  have h4 := Int.emod_lt_of_pos (x c) hp
  have h5 := Int.emod_nonneg (y c) hp.ne'
  have h6 := Int.emod_lt_of_pos (y c) hp
  have e : x c / 2 ^ j = y c / 2 ^ j := (hx c).trans (hy c).symm
  rw [abs_lt]
  constructor <;> nlinarith [e]

end ElboimSly.Paper
