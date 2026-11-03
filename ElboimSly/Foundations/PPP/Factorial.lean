/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.MeckeSets
public import ElboimSly.Foundations.PPP.PoissonMoments
public import Mathlib

/-!
# Factorial measures

Factorial measures.

`factorialMeasure n ν` is counting measure on `Fin n → S` restricted to the tuples of pairwise
distinct atoms of `ν`. `meckePhi D n ν` is the same for `ν` in the simple set `D.bSimple` and `0`
otherwise (this is the integrand `𝟙_{Ω_s} ν^{(n)}` of factorial moment measures).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S]

/-- Factorial measures: the `n`-th factorial measure `ν^{(n)}`, counting measure on
`Λ(ν)^n_≠ ⊆ S^n`. -/
noncomputable def factorialMeasure (n : ℕ) (ν : Measure S) : Measure (Fin n → S) :=
  Measure.count.restrict {x | (∀ i, x i ∈ SepPartSeq.atoms ν) ∧ Function.Injective x}

open Classical in
/-- `𝟙_{ν ∈ 𝔐_s} ν^{(n)}`. -/
noncomputable def meckePhi (D : SepPartSeq S) (n : ℕ) (ν : Measure S) : Measure (Fin n → S) :=
  if ν ∈ D.bSimple then factorialMeasure n ν else 0

theorem meckePhi_of_not_mem {D : SepPartSeq S} (n : ℕ) {ν : Measure S} (h : ν ∉ D.bSimple) :
    meckePhi D n ν = 0 := by
  classical
  simp [meckePhi, h]

theorem meckePhi_of_mem {D : SepPartSeq S} (n : ℕ) {ν : Measure S} (h : ν ∈ D.bSimple) :
    meckePhi D n ν = factorialMeasure n ν := by
  classical
  simp [meckePhi, h]

theorem factorialMeasure_eq_zero_of_subset (n : ℕ) (ν : Measure S) {A : Set (Fin n → S)}
    (hA : MeasurableSet A) (hsub : A ⊆ (injSet S n)ᶜ) : factorialMeasure n ν A = 0 := by
  rw [factorialMeasure, Measure.restrict_apply hA]
  have : A ∩ {x | (∀ i, x i ∈ SepPartSeq.atoms ν) ∧ Function.Injective x} = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun hx hx' => hsub hx hx'.2
  rw [this]; simp

theorem cast_prod_encard {ι : Type*} (s : Finset ι) (f : ι → ℕ∞) :
    ((∏ i ∈ s, f i : ℕ∞) : ℝ≥0∞) = ∏ i ∈ s, (f i : ℝ≥0∞) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, ENat.toENNReal_mul, ih]

namespace SepPartSeq

variable {D : SepPartSeq S}

/-- The box formula: on simple measures, the factorial measure of a box of pairwise disjoint
sets is the product of the masses. -/
theorem meckePhi_box {n : ℕ} {ν : Measure S} (hν : ν ∈ D.bSimple) {B : Fin n → Set S}
    (hB : ∀ j, MeasurableSet (B j)) (hd : Pairwise (Function.onFun Disjoint B)) :
    meckePhi D n ν (Set.pi Set.univ B) = ∏ j, ν (B j) := by
  have := D.measurableSingletonClass
  rw [meckePhi_of_mem n hν, factorialMeasure, Measure.restrict_apply (MeasurableSet.univ_pi hB)]
  have hat := measurableSet_atoms hν
  have e : Set.pi Set.univ B ∩ {x | (∀ i, x i ∈ atoms ν) ∧ Function.Injective x} =
      Set.pi Set.univ (fun j => B j ∩ atoms ν) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, -⟩; exact fun j => ⟨h1 j, h2 j⟩
    · intro h
      exact ⟨fun j => (h j).1, fun j => (h j).2, discBox_subset_injSet n hd
        (fun j _ => (h j).1)⟩
  rw [e, Measure.count_apply (MeasurableSet.univ_pi fun j => (hB j).inter hat),
    Set.encard_pi_eq_prod_encard, cast_prod_encard]
  exact Finset.prod_congr rfl fun j _ =>
    ((structure_of_mem_bSimple hν).2.2.2 (B j) (hB j)).symm

end SepPartSeq

end ElboimSly
