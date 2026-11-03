/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycStepCoords
public import Mathlib

/-!
# The entries of a final record

World-lines of a plan; joint exploration filtration (a), the recursion. For the final record `ρ = cycFinal path` of the
recursion with path rule `path`, entry `k` is `newEntry path ρ_k`, where `ρ_k` is the record of the
first `k` entries of `ρ`, and every entry before the `k`-th (for `k` an index of `ρ`) has finite length.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

namespace CycPlan

variable (P : CycPlan I d β) (path : PathRule I d)

omit [Fact (0 < β)] in
theorem cycState_succ (n : ℕ) : P.cycState path (n + 1) = P.cycStep path (P.cycState path n) := by
  simp [cycState, Function.iterate_succ_apply']

open scoped Classical in
omit [Fact (0 < β)] in
theorem num_cycState (n : ℕ) (h : ∀ i < n, ¬ P.Ended (P.cycState path i)) :
    (P.cycState path n).num = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 := ih fun i hi => h i (by omega)
    rw [cycState_succ, num_cycStep, ite_eq_right (h n (by omega)), h1]
    rfl

open scoped Classical in
omit [Fact (0 < β)] in
theorem coord_cycState_lt (n : ℕ) (h : ∀ i < n, ¬ P.Ended (P.cycState path i)) {i : ℕ}
    (hi : i < n) (m : ℕ) (hm : m ≤ n) (him : i < m) :
    (P.cycState path n).coord P.junk i = (P.cycState path m).coord P.junk i := by
  induction n, hm using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    have hn := h n (by omega)
    have hnum := P.num_cycState path n (fun j hj => h j (by omega))
    rw [cycState_succ, coord_cycStep, ite_eq_right, ih (fun j hj => h j (by omega)) (by omega)]
    rintro ⟨-, h2⟩
    rw [hnum] at h2
    have : i = n := by exact_mod_cast h2
    omega

end CycPlan

end ElboimSly.Cyclic

end
