/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvMark
public import Mathlib

/-!
# The environment scheme (b): non-explosion, combinatorial part

A strictly increasing sequence of marked times (jump times of a path, or multiples of `β`) is
unbounded: the steps of one walk cannot accumulate (`unbounded_of_marked`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- A strictly increasing sequence of marked times (jumps of `p` or multiples of `β`) is unbounded. -/
theorem unbounded_of_marked (p : CPath (Fin d → ℤ)) (r : ℕ → ℝ≥0) (hmono : StrictMono r)
    (hmark : ∀ j, r j ∈ CDisc p.fn ∨ ∃ m : ℕ, (r j : ℝ) = β * m) :
    ∀ M : ℝ≥0, ∃ j, M < r j := by
  intro M
  by_contra hM
  push Not at hM
  set S : Set ℝ≥0 := {x | x ≤ M ∧ (x ∈ CDisc p.fn ∨ ∃ m : ℕ, (x : ℝ) = β * m)} with hS
  have hfin : S.Finite := by
    have h1 : (CDisc p.fn ∩ Iic M).Finite := p.fin M
    have h2 : {x : ℝ≥0 | x ≤ M ∧ ∃ m : ℕ, (x : ℝ) = β * m}.Finite := by
      have hβ : 0 < β := Fact.out
      refine ((Set.finite_Iic ⌈(M : ℝ) / β⌉₊).image (fun m : ℕ => Real.toNNReal (β * m))).subset ?_
      rintro x ⟨hxM, m, hm⟩
      refine ⟨m, ?_, ?_⟩
      · have : (m : ℝ) ≤ (M : ℝ) / β := by
          rw [le_div_iff₀ hβ]
          have : (x : ℝ) ≤ M := by exact_mod_cast hxM
          linarith
        exact Nat.cast_le.1 (this.trans (Nat.le_ceil _))
      · apply NNReal.coe_injective
        rw [Real.coe_toNNReal _ (by positivity), hm]
    refine (h1.union h2).subset ?_
    rintro x ⟨hxM, hx | hx⟩
    · exact Or.inl ⟨hx, hxM⟩
    · exact Or.inr ⟨hxM, hx⟩
  have hinf : S.Infinite :=
    Set.infinite_of_injective_forall_mem hmono.injective (fun j => ⟨hM j, hmark j⟩)
  exact hinf hfin

end CycSchemeEnv
end ElboimSly.Cyclic

end
