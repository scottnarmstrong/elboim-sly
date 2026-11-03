/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# The volume of an ordered simplex

Configurations are a.s. good (the identity `Leb^n {t₁ < ⋯ < tₙ ∈ I} = |I|^n / n!`, used here only as
the upper bound `n! · Leb^n(T) ≤ |I|^n`).

The `n!` coordinate permutations of the ordered set `T` are pairwise disjoint, have the same volume
as `T`, and lie in the cube `I^n`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Nat

namespace ElboimSly.Interchange

/-- The set of strictly increasing `n`-tuples in `[p, q]`. -/
def orderedSimplex (n : ℕ) (p q : ℝ) : Set (Fin n → ℝ) :=
  {t | StrictMono t ∧ ∀ i, t i ∈ Set.Icc p q}

theorem measurableSet_orderedSimplex (n : ℕ) (p q : ℝ) :
    MeasurableSet (orderedSimplex n p q) := by
  have h1 : {t : Fin n → ℝ | StrictMono t} = ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j),
      {t | t i < t j} := by
    ext t; simp [StrictMono]
  have : orderedSimplex n p q = {t : Fin n → ℝ | StrictMono t} ∩ Set.pi Set.univ
      (fun _ => Set.Icc p q) := by
    ext t
    simp only [orderedSimplex, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
      true_implies]
  rw [this, h1]
  refine MeasurableSet.inter ?_ (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)

/-- The permuted copy of the ordered simplex. -/
def permSimplex (n : ℕ) (p q : ℝ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  (fun t => t ∘ σ) ⁻¹' orderedSimplex n p q

theorem volume_permSimplex (n : ℕ) (p q : ℝ) (σ : Equiv.Perm (Fin n)) :
    volume (permSimplex n p q σ) = volume (orderedSimplex n p q) := by
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have : (fun t : Fin n → ℝ => t ∘ σ) = Equiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm := by
    funext t i
    simp [Equiv.piCongrLeft_apply]
  unfold permSimplex
  rw [this]
  exact hmp.measure_preimage (measurableSet_orderedSimplex n p q).nullMeasurableSet

theorem measurableSet_permSimplex (n : ℕ) (p q : ℝ) (σ : Equiv.Perm (Fin n)) :
    MeasurableSet (permSimplex n p q σ) :=
  (measurableSet_orderedSimplex n p q).preimage
    (measurable_pi_iff.2 fun i => measurable_pi_apply (σ i))

theorem permSimplex_subset (n : ℕ) (p q : ℝ) (σ : Equiv.Perm (Fin n)) :
    permSimplex n p q σ ⊆ Set.pi Set.univ (fun _ => Set.Icc p q) := by
  intro t ht i _
  have := ht.2 (σ.symm i)
  simpa using this

theorem disjoint_permSimplex (n : ℕ) (p q : ℝ) :
    Pairwise (Function.onFun Disjoint (permSimplex n p q)) := by
  intro σ τ hστ
  rw [Function.onFun, Set.disjoint_left]
  intro t h1 h2
  apply hστ
  have hinj : Function.Injective t := by
    intro a b hab
    obtain ⟨a', rfl⟩ := σ.surjective a
    obtain ⟨b', rfl⟩ := σ.surjective b
    have := h1.1.injective hab
    rw [this]
  have hr : Set.range (t ∘ σ) = Set.range (t ∘ τ) := by
    rw [Set.range_comp, Set.range_comp, σ.surjective.range_eq, τ.surjective.range_eq]
  have := StrictMono.range_inj_of_wellFoundedLT h1.1 h2.1 |>.1 hr
  have h3 : t ∘ σ = t ∘ τ := this
  ext i
  exact congrArg Fin.val (hinj (congrFun h3 i))

/-- `n! · Leb^n {t₁ < ⋯ < tₙ ∈ [p,q]} ≤ (q-p)^n`. -/
theorem factorial_mul_volume_orderedSimplex_le (n : ℕ) (p q : ℝ) :
    (n ! : ℝ≥0∞) * volume (orderedSimplex n p q) ≤ ENNReal.ofReal (q - p) ^ n := by
  have hU : volume (⋃ σ : Equiv.Perm (Fin n), permSimplex n p q σ) =
      ∑ σ : Equiv.Perm (Fin n), volume (permSimplex n p q σ) := by
    rw [measure_iUnion (disjoint_permSimplex n p q) (measurableSet_permSimplex n p q),
      tsum_fintype]
  have hle : volume (⋃ σ : Equiv.Perm (Fin n), permSimplex n p q σ) ≤
      volume (Set.pi Set.univ (fun _ : Fin n => Set.Icc p q)) :=
    measure_mono (Set.iUnion_subset (permSimplex_subset n p q))
  rw [volume_pi_pi] at hle
  simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hle
  rw [hU] at hle
  simp only [volume_permSimplex, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul] at hle
  exact hle

end ElboimSly.Interchange
