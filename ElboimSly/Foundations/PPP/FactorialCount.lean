/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Factorial
public import Mathlib

/-!
# Counting injective tuples

Factorial moment measures (the mass of `T_k^n`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
theorem ncard_injTuples (F : Finset S) (n : ℕ) :
    {x : Fin n → S | (∀ i, x i ∈ F) ∧ Function.Injective x}.ncard = F.card.descFactorial n := by
  let g : (Fin n ↪ (F : Set S)) → (Fin n → S) := fun e i => (e i : S)
  have hg : Function.Injective g := by
    intro e e' h
    ext i
    exact congrFun h i
  have hrange : {x : Fin n → S | (∀ i, x i ∈ F) ∧ Function.Injective x} = Set.range g := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨fun i => ⟨x i, by simpa using h1 i⟩, fun i j hij => h2 (by simpa using hij)⟩, rfl⟩
    · rintro ⟨e, rfl⟩
      exact ⟨fun i => Finset.mem_coe.1 (e i).2, fun i j hij => e.injective (Subtype.ext hij)⟩
  rw [hrange, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hg, Nat.card_eq_fintype_card,
    Fintype.card_embedding_eq]
  simp

theorem measurableSet_injTuples [MeasurableSingletonClass S] (F : Finset S) (n : ℕ) :
    MeasurableSet {x : Fin n → S | (∀ i, x i ∈ F) ∧ Function.Injective x} := by
  have : {x : Fin n → S | (∀ i, x i ∈ F) ∧ Function.Injective x} ⊆ Set.pi Set.univ (fun _ => (F : Set S)) :=
    fun x hx i _ => hx.1 i
  have hfin : {x : Fin n → S | (∀ i, x i ∈ F) ∧ Function.Injective x}.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin n => (F : Set S)) (fun _ => F.finite_toSet)).subset ?_
    exact this
  exact hfin.measurableSet

end ElboimSly
