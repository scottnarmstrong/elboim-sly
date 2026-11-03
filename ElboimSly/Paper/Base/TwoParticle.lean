/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.StepRec
public import ElboimSly.Foundations.SRW.SrwDef
public import Mathlib

/-!
# The two-particle map

The two-particle map (ES22 §8, ES22 §8).

For `a b : ℤ^d` and driving paths `x₁ x₂` (start `0`, unit jumps), `twoParticle a b x₁ x₂` is the
unique step path `y` with `y 0 = b` that obeys the rules (F1)-(F3) at every `r > 0`.  The rules
involve only the left value `w = y(r-)`; they are packaged as `twoStep`.

* `IsDrivingPath`: the set `Path⁰_d` of the written proof.
* `twoStep`, `IsTwoParticle`: the rules and the path obeying them.
* `exists_unique_isTwoParticle`: existence and uniqueness (the content of the definition).
* `twoParticle`: the map `𝔉_{a,b}`.
-/

@[expose] public section

open Set Filter Topology Function
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base

variable {d : ℕ}

/-- The two-particle map (notation `Path⁰_d`): right-continuous paths with
`x(0) = 0`, finitely many jumps in bounded intervals, and all jumps in the unit vectors of `ℤ^d`. -/
structure IsDrivingPath (x : ℝ≥0 → Fin d → ℤ) : Prop where
  step : IsStepPath x
  zero : x 0 = 0
  jump : ∀ r ∈ CDisc x, x r - leftLim x r ∈ Set.range (SRW.Dir.vec (d := d))

/-- The right-hand side of the rules (F1)-(F3) at time `r`, as a function of the left value
`w = y(r-)`; here `p = a + x₁`, `p(r-) = a + x₁(r-)` and `v` is the jump of `x₂` at `r`. -/
noncomputable def twoStep (a : Fin d → ℤ) (x₁ x₂ : ℝ≥0 → Fin d → ℤ) (r : ℝ≥0)
    (w : Fin d → ℤ) : Fin d → ℤ :=
  open Classical in
  if r ∈ CDisc x₁ ∧ (w = a + leftLim x₁ r ∨ w = a + x₁ r) then
    (if w = a + leftLim x₁ r then a + x₁ r else a + leftLim x₁ r)
  else if r ∈ CDisc x₂ ∧ a + leftLim x₁ r ≠ w ∧
      a + leftLim x₁ r ≠ w + (x₂ r - leftLim x₂ r) then
    w + (x₂ r - leftLim x₂ r)
  else w

/-- `y` is a path with `y(0) = b` obeying the rules (F1)-(F3) of the two-particle map
at every `r > 0`. -/
structure IsTwoParticle (a b : Fin d → ℤ) (x₁ x₂ y : ℝ≥0 → Fin d → ℤ) : Prop where
  step : IsStepPath y
  zero : y 0 = b
  rule : ∀ r, 0 < r → y r = twoStep a x₁ x₂ r (leftLim y r)

theorem twoStep_of_notMem (a : Fin d → ℤ) {x₁ x₂ : ℝ≥0 → Fin d → ℤ} {r : ℝ≥0}
    (h1 : r ∉ CDisc x₁) (h2 : r ∉ CDisc x₂) (w : Fin d → ℤ) : twoStep a x₁ x₂ r w = w := by
  unfold twoStep
  simp [h1, h2]

theorem isStepPath_pair {x₁ x₂ : ℝ≥0 → Fin d → ℤ} (h1 : IsStepPath x₁) (h2 : IsStepPath x₂) :
    IsStepPath (fun s => (x₁ s, x₂ s)) := by
  refine ⟨fun s => ?_, fun T => ?_⟩
  · filter_upwards [h1.rc s, h2.rc s] with u hu1 hu2
    rw [hu1, hu2]
  · refine ((h1.fin T).union (h2.fin T)).subset fun r hr => ?_
    obtain ⟨⟨hr0, hr1⟩, hrT⟩ := hr
    by_contra hcon
    simp only [mem_union, mem_inter_iff, not_or, not_and, mem_Iic] at hcon
    obtain ⟨c1, c2⟩ := hcon
    have e1 : ∀ᶠ u in 𝓝[<] r, x₁ u = x₁ r := by
      by_contra h; exact c1 ⟨hr0, h⟩ hrT
    have e2 : ∀ᶠ u in 𝓝[<] r, x₂ u = x₂ r := by
      by_contra h; exact c2 ⟨hr0, h⟩ hrT
    exact hr1 (by filter_upwards [e1, e2] with u hu1 hu2; rw [hu1, hu2])

theorem notMem_pair {x₁ x₂ : ℝ≥0 → Fin d → ℤ} {r : ℝ≥0}
    (h : r ∉ CDisc (fun s => (x₁ s, x₂ s))) : r ∉ CDisc x₁ ∧ r ∉ CDisc x₂ := by
  constructor
  · intro ⟨hr0, hr1⟩
    exact h ⟨hr0, fun hh => hr1 (hh.mono fun u hu => (Prod.ext_iff.1 hu).1)⟩
  · intro ⟨hr0, hr1⟩
    exact h ⟨hr0, fun hh => hr1 (hh.mono fun u hu => (Prod.ext_iff.1 hu).2)⟩

/-- Existence and uniqueness of the two-particle path (The two-particle map). -/
theorem exists_unique_isTwoParticle (a b : Fin d → ℤ) {x₁ x₂ : ℝ≥0 → Fin d → ℤ}
    (h1 : IsStepPath x₁) (h2 : IsStepPath x₂) : ∃! y, IsTwoParticle a b x₁ x₂ y := by
  have hz := isStepPath_pair h1 h2
  obtain ⟨y, ⟨hy1, hy2, hy3⟩, huniq⟩ := exists_unique_stepRec hz
    (fun r w => twoStep a x₁ x₂ r w)
    (fun r hr w => twoStep_of_notMem a (notMem_pair hr).1 (notMem_pair hr).2 w) b
  refine ⟨y, ⟨hy1, hy2, hy3⟩, fun y' hy' => ?_⟩
  exact huniq y' ⟨hy'.step, hy'.zero, hy'.rule⟩

/-- The two-particle map: the two-particle map `𝔉_{a,b}(x₁, x₂)`. -/
noncomputable def twoParticle (a b : Fin d → ℤ) (x₁ x₂ : ℝ≥0 → Fin d → ℤ) : ℝ≥0 → Fin d → ℤ :=
  Classical.epsilon (IsTwoParticle a b x₁ x₂)

theorem isTwoParticle_twoParticle (a b : Fin d → ℤ) {x₁ x₂ : ℝ≥0 → Fin d → ℤ}
    (h1 : IsStepPath x₁) (h2 : IsStepPath x₂) :
    IsTwoParticle a b x₁ x₂ (twoParticle a b x₁ x₂) :=
  Classical.epsilon_spec (exists_unique_isTwoParticle a b h1 h2).exists

theorem eq_twoParticle {a b : Fin d → ℤ} {x₁ x₂ y : ℝ≥0 → Fin d → ℤ}
    (h1 : IsStepPath x₁) (h2 : IsStepPath x₂) (hy : IsTwoParticle a b x₁ x₂ y) :
    y = twoParticle a b x₁ x₂ :=
  (exists_unique_isTwoParticle a b h1 h2).unique hy (isTwoParticle_twoParticle a b h1 h2)

end ElboimSly.Paper
