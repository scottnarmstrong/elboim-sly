/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.CountableReduction
public import ElboimSly.Foundations.SRW.Eval
public import Mathlib

/-!
# Evaluation at variable times

Evaluation at variable times.

* `ev`: the jointly measurable evaluation `ev(r, γ)` (limit of dyadic evaluations).
* `IsVersion`, `IsRegularSet`: `ℰ`-regular sets of `E × PathSpace d` and their measurable
  versions (path space, laws, SRWs, admissible filtrations (f)).
* (a) `measurable_ev`, `ev_of_regular`; (b) `isVersion_eval`; (c) `isVersion_forall_Icc`;
  (d) `isVersion_exists_Ici`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- `Γ'` is a measurable version of `Γ ⊆ E × PathSpace d`: it is measurable and agrees with
`Γ` on regular paths. -/
def IsVersion {E : Type*} [MeasurableSpace E] (Γ Γ' : Set (E × PathSpace d)) : Prop :=
  MeasurableSet Γ' ∧ ∀ z γ, IsRegularPath γ → ((z, γ) ∈ Γ ↔ (z, γ) ∈ Γ')

/-- `Γ` is `ℰ`-regular: it has a measurable version. -/
def IsRegularSet {E : Type*} [MeasurableSpace E] (Γ : Set (E × PathSpace d)) : Prop :=
  ∃ Γ', IsVersion Γ Γ'

open Classical in
/-- Evaluation at variable times (a): `ev(r,γ) = y` if `γ(D_m(r)) = y` for all large `m`,
and `0` if there is no such `y`. -/
noncomputable def ev (r : ℝ≥0) (γ : PathSpace d) : Fin d → ℤ :=
  if h : ∃ y, ∀ᶠ m in atTop, γ (dy m r) = y then h.choose else 0

/-- On regular paths `ev` is the evaluation. -/
theorem ev_of_regular {γ : PathSpace d} (hγ : IsRegularPath γ) (r : ℝ≥0) : ev r γ = γ r := by
  have h : ∃ y, ∀ᶠ m in atTop, γ (dy m r) = y := ⟨γ r, hγ.eventually_dy r⟩
  unfold ev
  rw [dite_eq_left h]
  have h1 := h.choose_spec
  have h2 := hγ.eventually_dy r
  obtain ⟨m, hm1, hm2⟩ := (h1.and h2).exists
  rw [← hm1, hm2]

theorem ev_eq_iff (r : ℝ≥0) (γ : PathSpace d) (y : Fin d → ℤ) :
    ev r γ = y ↔ (∀ᶠ m in atTop, γ (dy m r) = y) ∨
      (y = 0 ∧ ∀ y', ¬ ∀ᶠ m in atTop, γ (dy m r) = y') := by
  by_cases h : ∃ y, ∀ᶠ m in atTop, γ (dy m r) = y
  · unfold ev
    rw [dite_eq_left h]
    have h1 := h.choose_spec
    constructor
    · intro e; left; rw [← e]; exact h1
    · rintro (h2 | ⟨_, h3⟩)
      · obtain ⟨m, hm1, hm2⟩ := (h1.and h2).exists
        rw [← hm1, hm2]
      · exact absurd h1 (h3 _)
  · unfold ev
    rw [dite_eq_right h]
    have h : ∀ y, ¬ ∀ᶠ m in atTop, γ (dy m r) = y := fun y hy => h ⟨y, hy⟩
    constructor
    · intro e; right; exact ⟨e.symm, h⟩
    · rintro (h2 | ⟨h2, _⟩)
      · exact absurd h2 (h y)
      · exact h2.symm

theorem measurable_dyEval (m : ℕ) :
    Measurable fun p : ℝ≥0 × PathSpace d => p.2 (dy m p.1) := by
  have hn : Measurable fun p : ℝ≥0 × PathSpace d => ⌈p.1 * (2 : ℝ≥0) ^ m⌉₊ :=
    Nat.measurable_ceil.comp (measurable_fst.mul_const _)
  have hF : Measurable fun q : (ℝ≥0 × PathSpace d) × ℕ => q.1.2 ((q.2 : ℝ≥0) / 2 ^ m) :=
    measurable_from_prod_countable_left fun k =>
      (measurable_pi_apply ((k : ℝ≥0) / 2 ^ m)).comp measurable_snd
  exact hF.comp (measurable_id.prodMk hn)

/-- Evaluation at variable times (a): `ev` is jointly measurable. -/
theorem measurable_ev : Measurable fun p : ℝ≥0 × PathSpace d => ev p.1 p.2 := by
  refine measurable_to_countable' fun y => ?_
  have hE : ∀ y' : Fin d → ℤ, MeasurableSet
      {p : ℝ≥0 × PathSpace d | ∀ᶠ m in atTop, p.2 (dy m p.1) = y'} := by
    intro y'
    have : {p : ℝ≥0 × PathSpace d | ∀ᶠ m in atTop, p.2 (dy m p.1) = y'} =
        ⋃ M : ℕ, ⋂ m ∈ Ici M, {p | p.2 (dy m p.1) = y'} := by
      ext p; simp [eventually_atTop]
    rw [this]
    exact MeasurableSet.iUnion fun M => MeasurableSet.biInter (to_countable _) fun m _ =>
      measurable_dyEval m (measurableSet_singleton y')
  have : (fun p : ℝ≥0 × PathSpace d => ev p.1 p.2) ⁻¹' {y} =
      {p | ∀ᶠ m in atTop, p.2 (dy m p.1) = y} ∪
        ({p | y = 0} ∩ ⋂ y', {p | ¬ ∀ᶠ m in atTop, p.2 (dy m p.1) = y'}) := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, ev_eq_iff, mem_union, mem_ofPred_eq, mem_inter_iff,
      mem_iInter]
  rw [this]
  refine (hE y).union (MeasurableSet.inter ?_ (MeasurableSet.iInter fun y' => (hE y').compl))
  by_cases hy : y = 0 <;> simp [hy]

end SRW
end ElboimSly
