/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.SimpleSet2
public import Mathlib

/-!
# The `π`-system for factorial moment measures

Factorial moment measures (set-theoretic part).

For a separating partition sequence `D` of `S` and `n : ℕ`, on `Fin n → S`:

* `injSet n`: the injective tuples (the off-diagonal), measurable;
* `meckeC D n`: boxes of pairwise disjoint measurable sets, each inside a level-`0` cell, together
  with all measurable subsets of the complement of `injSet n`. It is a `π`-system generating the
  product `σ`-algebra and a countable subfamily of finite-mass-type sets covers everything.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S]

/-- Injective tuples. -/
def injSet (S : Type*) (n : ℕ) : Set (Fin n → S) := {x | Function.Injective x}

namespace SepPartSeq

variable (D : SepPartSeq S) (n : ℕ)

theorem measurableSet_eq_coords (D : SepPartSeq S) (n : ℕ) (i j : Fin n) :
    MeasurableSet {x : Fin n → S | x i = x j} := by
  have : {x : Fin n → S | x i = x j} = ⋂ m, {x : Fin n → S | D.idx m (x i) = D.idx m (x j)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h m; rw [h]
    · intro h
      by_contra hne
      obtain ⟨m, hm⟩ := D.separate _ _ hne
      exact hm (h m)
  rw [this]
  exact MeasurableSet.iInter fun m => measurableSet_eq_fun
    ((D.measurable_idx m).comp (measurable_pi_apply i))
    ((D.measurable_idx m).comp (measurable_pi_apply j))

theorem measurableSet_injSet (D : SepPartSeq S) (n : ℕ) : MeasurableSet (injSet S n) := by
  have : injSet S n = ⋂ i, ⋂ j, ⋂ (_ : i ≠ j), {x : Fin n → S | x i = x j}ᶜ := by
    ext x
    simp only [injSet, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff, Function.Injective]
    constructor
    · intro h i j hij hx; exact hij (h hx)
    · intro h i j hx; by_contra hij; exact h i j hij hx
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    (D.measurableSet_eq_coords n i j).compl

/-- Boxes of pairwise disjoint measurable sets, each inside a level-`0` cell. -/
def discBoxes : Set (Set (Fin n → S)) :=
  {R | ∃ B : Fin n → Set S, (∀ j, MeasurableSet (B j)) ∧ (∀ j, ∃ i, B j ⊆ D.cell 0 i) ∧
    Pairwise (Function.onFun Disjoint B) ∧ R = Set.pi Set.univ B}

/-- The `π`-system for Mecke. -/
def meckeC : Set (Set (Fin n → S)) :=
  D.discBoxes n ∪ {A | MeasurableSet A ∧ A ⊆ (injSet S n)ᶜ}

omit [MeasurableSpace S] in
theorem discBox_subset_injSet {B : Fin n → Set S} (hB : Pairwise (Function.onFun Disjoint B)) :
    Set.pi Set.univ B ⊆ injSet S n := by
  intro x hx i j hij
  by_contra hne
  have := Set.disjoint_left.1 (hB hne) (hx i (Set.mem_univ i))
  exact this (hij ▸ hx j (Set.mem_univ j))

theorem isPiSystem_meckeC : IsPiSystem (D.meckeC n) := by
  rintro s (⟨B, hB, hc, hd, rfl⟩ | ⟨hs, hsub⟩) t (⟨B', hB', hc', hd', rfl⟩ | ⟨ht, htsub⟩) hne
  · refine Or.inl ⟨fun j => B j ∩ B' j, fun j => (hB j).inter (hB' j), fun j => ?_, ?_, ?_⟩
    · obtain ⟨i, hi⟩ := hc j
      exact ⟨i, Set.inter_subset_left.trans hi⟩
    · intro i j hij
      exact (hd hij).mono Set.inter_subset_left Set.inter_subset_left
    · rw [Set.pi_inter_distrib]
  · exfalso
    obtain ⟨x, hx1, hx2⟩ := hne
    exact htsub hx2 (discBox_subset_injSet n hd hx1)
  · exfalso
    obtain ⟨x, hx1, hx2⟩ := hne
    exact hsub hx1 (discBox_subset_injSet n hd' hx2)
  · exact Or.inr ⟨hs.inter ht, fun x hx => hsub hx.1⟩

theorem meckeC_measurable {A : Set (Fin n → S)} (hA : A ∈ D.meckeC n) : MeasurableSet A := by
  rcases hA with ⟨B, hB, -, -, rfl⟩ | ⟨hA, -⟩
  · exact MeasurableSet.univ_pi hB
  · exact hA

/-- The off-diagonal part of a box is a countable union of boxes of pairwise distinct cells. -/
theorem pi_inter_injSet_eq (B : Fin n → Set S) :
    Set.pi Set.univ B ∩ injSet S n = ⋃ p : ℕ × (Fin n → ℕ),
      if Function.Injective p.2 then Set.pi Set.univ (fun j => B j ∩ D.cell p.1 (p.2 j)) else ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hx, hinj⟩
    obtain ⟨m, hm⟩ := D.exists_separating_level (Set.finite_range x)
    have hb : Function.Injective (fun j => D.idx m (x j)) := by
      intro i j hij
      exact hinj (hm _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij)
    refine ⟨(m, fun j => D.idx m (x j)), ?_⟩
    simp only [hb, ite_true, Set.mem_pi, Set.mem_univ, true_implies]
    exact fun j => ⟨hx j (Set.mem_univ j), rfl⟩
  · rintro ⟨p, hp⟩
    by_cases hinj : Function.Injective p.2
    · simp only [hinj, ite_true, Set.mem_pi, Set.mem_univ, true_implies] at hp
      refine ⟨fun j _ => (hp j).1, ?_⟩
      intro i j hij
      apply hinj
      have h1 : D.idx p.1 (x i) = p.2 i := (hp i).2
      have h2 : D.idx p.1 (x j) = p.2 j := (hp j).2
      rw [← h1, ← h2, hij]
    · simp [hinj] at hp

theorem generateFrom_meckeC :
    MeasurableSpace.generateFrom (D.meckeC n) =
      (MeasurableSpace.pi : MeasurableSpace (Fin n → S)) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le fun A hA => D.meckeC_measurable n hA) ?_
  rw [← generateFrom_pi]
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨B, hB, rfl⟩
  have hB' : ∀ j, MeasurableSet (B j) := fun j => hB j (Set.mem_univ j)
  have hsplit : Set.pi Set.univ B =
      (Set.pi Set.univ B ∩ injSet S n) ∪ (Set.pi Set.univ B \ injSet S n) := by
    ext x; by_cases h : x ∈ injSet S n <;> simp
  rw [hsplit]
  refine MeasurableSet.union ?_ (MeasurableSpace.measurableSet_generateFrom
    (Or.inr ⟨(MeasurableSet.univ_pi hB').diff (D.measurableSet_injSet n), fun x hx => hx.2⟩))
  rw [D.pi_inter_injSet_eq n B]
  refine MeasurableSet.iUnion fun p => ?_
  by_cases hinj : Function.Injective p.2
  · simp only [hinj, ite_true]
    refine MeasurableSpace.measurableSet_generateFrom (Or.inl ⟨_, fun j => (hB' j).inter
      (D.measurableSet_cell _ _), fun j => ?_, ?_, rfl⟩)
    · by_cases hne : (D.cell p.1 (p.2 j)).Nonempty
      · obtain ⟨y, hy⟩ := hne
        exact ⟨_, Set.inter_subset_right.trans (D.cell_subset_cell_zero hy)⟩
      · exact ⟨0, by rw [Set.not_nonempty_iff_eq_empty.1 hne]; simp⟩
    · intro i j hij
      refine Set.disjoint_left.2 fun y hy hy' => hij (hinj ?_)
      have h1 : D.idx p.1 y = p.2 i := hy.2
      have h2 : D.idx p.1 y = p.2 j := hy'.2
      rw [← h1, ← h2]
  · simp only [hinj, ite_false]
    exact MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨MeasurableSet.empty, by simp⟩)

end SepPartSeq

end ElboimSly
