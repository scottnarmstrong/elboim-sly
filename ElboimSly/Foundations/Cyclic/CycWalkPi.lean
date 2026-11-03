/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycWalkTraj
import Mathlib

/-!
# Agreement of the cyclic walk with `π_s ∘ π_β^k`

Agreement with the source definition.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

theorem cycWalk_succ (hν : Good ν) (k : ℤ) :
    cycWalk ν 0 0 (((k + 1 : ℤ) : ℝ) * β) = piBeta hν (cycWalk ν 0 0 ((k : ℝ) * β)) := by
  have hβ : 0 < β := Fact.out
  have h := cycWalk_add_step hν k (s := β) hβ.le le_rfl (by
    by_cases hk : 0 ≤ k
    · exact Or.inl hk
    · refine Or.inr ?_
      have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      nlinarith)
  have e : ((k + 1 : ℤ) : ℝ) * β = k * β + β := by push_cast; ring
  rw [e, h, piBeta_apply, piReal]
  rfl

theorem cycWalk_int_mul (hν : Good ν) (k : ℤ) :
    cycWalk ν 0 0 ((k : ℝ) * β) = ((piBeta hν) ^ k) 0 := by
  induction k using Int.induction_on with
  | zero => simp [cycWalk_zero hν]
  | succ i ih =>
    rw [cycWalk_succ hν, ih, add_comm (i : ℤ) 1, zpow_one_add]
    rfl
  | pred i ih =>
    have h1 := cycWalk_succ hν (-(i : ℤ) - 1)
    have e : ((-(i : ℤ) - 1 + 1 : ℤ)) = -(i : ℤ) := by ring
    rw [e, ih] at h1
    have h2 : ((piBeta hν) ^ (-(i : ℤ))) 0 =
        (piBeta hν) (((piBeta hν) ^ (-(i : ℤ) - 1)) 0) := by
      rw [← Equiv.Perm.mul_apply, ← zpow_one_add]
      congr 3; ring
    rw [h2] at h1
    exact (piBeta hν).injective h1.symm

/-- Agreement with the source definition. For good `ν`, `k ∈ ℤ` and `s ∈ [0, β)`,
`W(kβ + s) = π_s (π_β^k 0)`. -/
theorem cycWalk_eq_pi (hν : Good ν) (k : ℤ) {s : ℝ} (hs0 : 0 ≤ s) (hsβ : s < β) :
    cycWalk ν 0 0 ((k : ℝ) * β + s) = interchangePi ν s.toNNReal (((piBeta hν) ^ k) 0) := by
  have hβ : 0 < β := Fact.out
  have h := cycWalk_add_step hν k hs0 hsβ.le (by
    by_cases hk : 0 ≤ k
    · exact Or.inl hk
    · refine Or.inr ?_
      have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      nlinarith)
  rw [h, cycWalk_int_mul hν]
  rfl

end ElboimSly.Cyclic

end
