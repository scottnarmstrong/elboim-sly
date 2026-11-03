/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRecord
public import Mathlib

/-!
# Exploration plans and the stopping length

World-lines, records, exploration plans (second half: exploration plans and the stopping length).

## Design

* `CycPlan I d β` has `β`, `I` as parameters and the lattice dimension `d`. It carries the number
  `K ∈ ℕ_{≥1} ∪ {∞}` of walks (`ℕ∞`; the value `0` is allowed and gives the empty record) and, for
  every `k : ℕ`, measurable maps `start k : CycRecN k → CycData`, `dl k, st k : CycRecN (k+1) → …`.
  The written proof prescribes them for the walks `k + 1 ≤ K` only; since the data for walks beyond `K`
  are never read, prescribing them for all `k` loses nothing (a plan with data only up to `K`
  extends by constants) and avoids dependent types in `k ≤ K`.
* The decision `st` is a `Bool` (`true` is `1`).
* `CycPlan.stopLen` is the stopping length, as an `sInf` in `[0, ∞]` of the set in the written proof; the
  convention `min ∅ = ∞` is `sInf ∅ = ⊤`. The statement that the infimum is a minimum is
  not needed to define the stopping length.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

/-- An exploration plan. World-lines, records, exploration plans. -/
structure CycPlan (I : Type*) [MeasurableSpace I] (d : ℕ) (β : ℝ) where
  /-- The number of walks. -/
  K : ℕ∞
  /-- Start data of walk `k + 1` given the first `k` world-lines. -/
  start : ∀ k : ℕ, CycRecN I d k → CycData I d
  /-- Deadline of walk `k + 1` given the first `k` world-lines and the current one. -/
  dl : ∀ k : ℕ, CycRecN I d (k + 1) → ℝ≥0∞
  /-- Decision of walk `k + 1` (`true` is `1`). -/
  st : ∀ k : ℕ, CycRecN I d (k + 1) → Bool
  measurable_start : ∀ k, Measurable (start k)
  measurable_dl : ∀ k, Measurable (dl k)
  measurable_st : ∀ k, Measurable (st k)

namespace CycPlan

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} (P : CycPlan I d β)

/-- The constant path (of length `∞`). -/
def _root_.ElboimSly.Cyclic.CycPath.const (x : Fin d → ℤ) : CycPath d :=
  ⟨⟨⊤, fun _ => x, fun _ => Filter.Eventually.of_forall fun _ => rfl,
    fun T => by
      refine (Set.finite_empty).subset ?_
      intro s hs
      obtain ⟨⟨_, h⟩, _⟩ := hs
      exact absurd (Filter.Eventually.of_forall fun _ => rfl) h,
    fun s s' h _ => absurd h (by simp)⟩, fun s hs => by
      obtain ⟨_, h⟩ := hs
      exact absurd (Filter.Eventually.of_forall fun _ => rfl) h⟩

/-- A junk world-line, used only as the value of unreachable entries. -/
noncomputable def junk : CycEntry I d :=
  (P.start 0 Fin.elim0, CycPath.const (P.start 0 Fin.elim0).start)

/-- The record `ρ̂_a = (ρ, (δ, ς_a, p(· ∧ ς_a)))` of world-lines, records, exploration plans. -/
noncomputable def hatRec (k : ℕ) (ρ : CycRecN I d k) (p : CycPath d) (a : ℕ) :
    CycRecN I d (k + 1) :=
  CycRec.snoc ρ (P.start k ρ, p.cut (p.1.jt a))

/-- The stopping length of the path `p` for walk `k + 1` after the records `ρ`:
`min ({ς_a : a ≥ 1, st(ρ̂_a) = 1} ∪ {ς_a + dl(ρ̂_a) : a ≥ 0, ς_a + dl(ρ̂_a) < ς_{a+1}})`. -/
noncomputable def stopLen (k : ℕ) (ρ : CycRecN I d k) (p : CycPath d) : ℝ≥0∞ :=
  sInf ({t | ∃ a : ℕ, 1 ≤ a ∧ p.1.jt a < ⊤ ∧ P.st k (P.hatRec k ρ p a) = true ∧ t = p.1.jt a} ∪
    {t | ∃ a : ℕ, p.1.jt a < ⊤ ∧ t = p.1.jt a + P.dl k (P.hatRec k ρ p a) ∧
      t < p.1.jt (a + 1)})

end CycPlan

end ElboimSly.Cyclic

end
