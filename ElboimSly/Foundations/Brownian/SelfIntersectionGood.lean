/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.SelfIntersectionSet
public import ElboimSly.Foundations.Brownian.Markov

import Mathlib

/-!
# The good events `G(a)` of the self-intersection claim

ES22 Claim 9.4 (events `Sup`, `Osc`, `Occ`, `G`, `G_j`).

For `a ≥ 0` the event `good a` says that, up to time `a`: the path stays in the ball of radius `t`;
it oscillates by at most `ρ` over unit time; and for every lattice point `x` of the box of radius
`2t`, the number of integer times `i ≤ a` with `‖B i - x‖ ≤ R₃` is at most `M`. The family is
decreasing in `a`, and `good a` is measurable for the filtration `ℱ_a`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*}

/-- Five-dimensional Euclidean space (with the sup norm). -/
abbrev R5 : Type := Fin 5 → ℝ

/-- The lattice points `x ∈ ℤ⁵` with `‖x‖ ≤ ⌊2t⌋`. -/
noncomputable def latticeBox (t : ℝ) : Finset (Fin 5 → ℤ) :=
  Fintype.piFinset fun _ : Fin 5 => Finset.Icc (-(⌊2 * t⌋₊ : ℤ)) (⌊2 * t⌋₊ : ℤ)

/-- The embedding of a lattice point in `ℝ⁵`. -/
def latticePt (x : Fin 5 → ℤ) : R5 := fun k => (x k : ℝ)

/-- The number of integer times `i ≤ n` with `‖B i - x‖ ≤ R₃`. -/
noncomputable def visitCount (B : ℝ≥0 → Ω → R5) (ω : Ω) (x : R5) (R₃ : ℝ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun i : ℕ => ‖B (i : ℝ≥0) ω - x‖ ≤ R₃).card

/-- `Sup`: `‖B u‖ ≤ t` for `u ≤ a`. -/
def goodSup (B : ℝ≥0 → Ω → R5) (t : ℝ) (a : ℝ≥0) : Set Ω := {ω | ∀ u ≤ a, ‖B u ω‖ ≤ t}

/-- `Osc`: `‖B u - B v‖ ≤ ρ` for `u, v ≤ a` with `|u - v| ≤ 1`. -/
def goodOsc (B : ℝ≥0 → Ω → R5) (ρ : ℝ) (a : ℝ≥0) : Set Ω :=
  {ω | ∀ p ∈ closePairs (Set.Icc 0 a) 1, ‖B p.1 ω - B p.2 ω‖ ≤ ρ}

/-- `Occ`: bounded visits of lattice balls at integer times `≤ a`. -/
def goodOcc (B : ℝ≥0 → Ω → R5) (t R₃ M : ℝ) (a : ℝ≥0) : Set Ω :=
  {ω | ∀ x ∈ latticeBox t, (visitCount B ω (latticePt x) R₃ ⌊(a : ℝ)⌋₊ : ℝ) ≤ M}

/-- The good event `G(a) = Sup ∩ Osc ∩ Occ` up to time `a`. -/
def good (B : ℝ≥0 → Ω → R5) (t ρ R₃ M : ℝ) (a : ℝ≥0) : Set Ω :=
  goodSup B t a ∩ goodOsc B ρ a ∩ goodOcc B t R₃ M a

lemma goodSup_anti (B : ℝ≥0 → Ω → R5) (t : ℝ) {a b : ℝ≥0} (h : a ≤ b) :
    goodSup B t b ⊆ goodSup B t a :=
  fun _ hω u hu => hω u (hu.trans h)

lemma goodOsc_anti (B : ℝ≥0 → Ω → R5) (ρ : ℝ) {a b : ℝ≥0} (h : a ≤ b) :
    goodOsc B ρ b ⊆ goodOsc B ρ a := fun _ hω p hp =>
  hω p ⟨⟨zero_le, hp.1.2.trans h⟩, ⟨zero_le, hp.2.1.2.trans h⟩, hp.2.2⟩

lemma visitCount_mono (B : ℝ≥0 → Ω → R5) (ω : Ω) (x : R5) (R₃ : ℝ) {m n : ℕ} (h : m ≤ n) :
    visitCount B ω x R₃ m ≤ visitCount B ω x R₃ n :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))

lemma goodOcc_anti (B : ℝ≥0 → Ω → R5) (t R₃ M : ℝ) {a b : ℝ≥0} (h : a ≤ b) :
    goodOcc B t R₃ M b ⊆ goodOcc B t R₃ M a := by
  intro ω hω x hx
  refine le_trans ?_ (hω x hx)
  exact_mod_cast visitCount_mono B ω _ R₃ (Nat.floor_le_floor (by exact_mod_cast h))

lemma good_anti (B : ℝ≥0 → Ω → R5) (t ρ R₃ M : ℝ) {a b : ℝ≥0} (h : a ≤ b) :
    good B t ρ R₃ M b ⊆ good B t ρ R₃ M a :=
  inter_subset_inter (inter_subset_inter (goodSup_anti B t h) (goodOsc_anti B ρ h))
    (goodOcc_anti B t R₃ M h)

/-! ### Measurability -/

section Meas

variable {B : ℝ≥0 → Ω → R5}

lemma measurableSet_goodSup' {m : MeasurableSpace Ω} {a : ℝ≥0} (hc : ∀ ω, Continuous fun u => B u ω)
    (hm : ∀ u ≤ a, Measurable[m] (B u)) (t : ℝ) :
    MeasurableSet[m] (goodSup B t a) := by
  have e : goodSup B t a = ⋂ u ∈ denseSub (Set.Icc 0 a), {ω | ‖B u ω‖ ≤ t} := by
    ext ω
    simp only [goodSup, Set.mem_ofPred_eq, Set.mem_iInter]
    exact forall_le_iff_denseSub (f := fun u => ‖B u ω‖) (hc ω).norm a t
  rw [e]
  refine MeasurableSet.biInter (denseSub_countable _) fun u hu => ?_
  exact measurableSet_le (hm u (denseSub_subset _ hu).2).norm measurable_const

lemma measurableSet_goodOsc' {m : MeasurableSpace Ω} {a : ℝ≥0} (hc : ∀ ω, Continuous fun u => B u ω)
    (hm : ∀ u ≤ a, Measurable[m] (B u)) (ρ : ℝ) :
    MeasurableSet[m] (goodOsc B ρ a) := by
  have e : goodOsc B ρ a = ⋂ p ∈ closePairs (denseSub (Set.Icc 0 a)) 1,
      {ω | ‖B p.1 ω - B p.2 ω‖ ≤ ρ} := by
    ext ω
    simp only [goodOsc, Set.mem_ofPred_eq, Set.mem_iInter]
    exact forall_closePairs_iff (w := fun u => B u ω) (hc ω) Set.ordConnected_Icc 1 ρ
  rw [e]
  refine MeasurableSet.biInter ?_ fun p hp => ?_
  · exact ((denseSub_countable (Set.Icc 0 a)).prod (denseSub_countable (Set.Icc 0 a))).mono
      fun p hp => Set.mem_prod.2 ⟨hp.1, hp.2.1⟩
  · exact measurableSet_le ((hm p.1 (denseSub_subset _ hp.1).2).sub
      (hm p.2 (denseSub_subset _ hp.2.1).2)).norm measurable_const

lemma measurable_visitCount {m : MeasurableSpace Ω} {n : ℕ}
    (hm : ∀ i : ℕ, i ≤ n → Measurable[m] (B (i : ℝ≥0))) (x : R5) (R₃ : ℝ) :
    Measurable[m] fun ω => (visitCount B ω x R₃ n : ℝ) := by
  have e : (fun ω => (visitCount B ω x R₃ n : ℝ)) =
      fun ω => ∑ i ∈ Finset.range (n + 1), {ω | ‖B (i : ℝ≥0) ω - x‖ ≤ R₃}.indicator
        (fun _ => (1 : ℝ)) ω := by
    funext ω
    simp only [visitCount, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : ‖B (i : ℝ≥0) ω - x‖ ≤ R₃ <;> simp [h]
  rw [e]
  refine Finset.measurable_sum _ fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  exact measurable_const.indicator (measurableSet_le ((hm i hi').sub measurable_const).norm
    measurable_const)

lemma measurableSet_goodOcc' {m : MeasurableSpace Ω} {a : ℝ≥0}
    (hm : ∀ i : ℕ, i ≤ ⌊(a : ℝ)⌋₊ → Measurable[m] (B (i : ℝ≥0))) (t R₃ M : ℝ) :
    MeasurableSet[m] (goodOcc B t R₃ M a) := by
  have e : goodOcc B t R₃ M a = ⋂ x ∈ latticeBox t,
      {ω | (visitCount B ω (latticePt x) R₃ ⌊(a : ℝ)⌋₊ : ℝ) ≤ M} := by
    ext ω; simp [goodOcc]
  rw [e]
  refine Finset.measurableSet_biInter _ fun x _ => ?_
  exact measurableSet_le (measurable_visitCount hm _ _) measurable_const

lemma measurableSet_good' {m : MeasurableSpace Ω} {a : ℝ≥0}
    (hc : ∀ ω, Continuous fun u => B u ω) (hm : ∀ u ≤ a, Measurable[m] (B u))
    (t ρ R₃ M : ℝ) : MeasurableSet[m] (good B t ρ R₃ M a) :=
  ((measurableSet_goodSup' hc hm t).inter (measurableSet_goodOsc' hc hm ρ)).inter
    (measurableSet_goodOcc' (fun i hi => hm _ (by
      have : (i : ℝ) ≤ a := (Nat.cast_le.2 hi).trans (Nat.floor_le a.2)
      exact_mod_cast this)) t R₃ M)

/-- The good events up to time `a` are `ℱ_a`-measurable. -/
lemma measurableSet_good {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (hB : IsStandardBrownianMotion 5 B P) (t ρ R₃ M : ℝ) (a : ℝ≥0) :
    MeasurableSet[bmFiltration B a] (good B t ρ R₃ M a) :=
  measurableSet_good' (fun ω => (hB.continuous_zero ω).1) (fun _ hu => measurable_bmFiltration hu)
    t ρ R₃ M

end Meas

end ElboimSly.Brownian
