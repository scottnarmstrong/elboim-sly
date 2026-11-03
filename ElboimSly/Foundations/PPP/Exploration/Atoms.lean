/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Law
import Mathlib

/-!
# Atoms and measures of total mass one

A measure `ρ` of total mass `1` which gives integer mass to each atom of `B₀,…,B_{l-1}` charges
exactly one atom `α_{ε₀}`, and then `ρ(Bᵢ) = 1{ε₀ i}`. Used for first-point law of a deterministic probe.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {l : ℕ} {B : Fin l → Set S}

omit [MeasurableSpace S] in
theorem iUnion_atom (B : Fin l → Set S) : ⋃ ε : Fin l → Bool, atom B ε = Set.univ := by
  classical
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨fun i => decide (x ∈ B i), mem_atom.2 fun i => by simp⟩

theorem sum_measure_atom (hB : ∀ i, MeasurableSet (B i)) (ρ : Measure S) :
    ∑ ε : Fin l → Bool, ρ (atom B ε) = ρ Set.univ := by
  classical
  rw [← measure_biUnion_finset (s := Finset.univ) (f := atom B)
    (fun ε _ ε' _ hne => pairwise_disjoint_atom B hne) fun ε _ => measurableSet_atom hB ε]
  congr 1
  simpa using iUnion_atom B

theorem measure_atom_eq_zero (hB : ∀ i, MeasurableSet (B i)) {ρ : Measure S}
    (h1 : ρ Set.univ = 1) {ε₀ : Fin l → Bool} (h0 : ρ (atom B ε₀) = 1) {ε : Fin l → Bool}
    (hne : ε ≠ ε₀) : ρ (atom B ε) = 0 := by
  classical
  have hs := sum_measure_atom hB ρ
  rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ ε₀), h0] at hs
  have hrest : ∑ x ∈ Finset.univ.erase ε₀, ρ (atom B x) = 0 :=
    (ENNReal.add_right_inj ENNReal.one_ne_top).1 (hs.trans (add_zero 1).symm)
  exact (Finset.sum_eq_zero_iff.1 hrest) ε (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩)

theorem measure_eq_of_atom (hB : ∀ i, MeasurableSet (B i)) {ρ : Measure S}
    (h1 : ρ Set.univ = 1) {ε₀ : Fin l → Bool} (h0 : ρ (atom B ε₀) = 1) (i : Fin l) :
    ρ (B i) = if ε₀ i then 1 else 0 := by
  classical
  rw [measure_eq_sum_atom hB ρ i]
  by_cases hε : ε₀ i = true
  · rw [ite_eq_left hε, Finset.sum_eq_single ε₀]
    · exact h0
    · intro ε _ hne
      exact measure_atom_eq_zero hB h1 h0 hne
    · intro h; exact absurd (by simp [hε]) h
  · rw [ite_eq_right hε]
    refine Finset.sum_eq_zero fun ε hε' => ?_
    have : ε ≠ ε₀ := by
      rintro rfl
      simp at hε'
      exact hε hε'
    exact measure_atom_eq_zero hB h1 h0 this

theorem exists_atom_eq_one (hB : ∀ i, MeasurableSet (B i)) {ρ : Measure S}
    (h1 : ρ Set.univ = 1) (hint : ∀ ε : Fin l → Bool, ∃ n : ℕ, ρ (atom B ε) = n) :
    ∃ ε₀, ρ (atom B ε₀) = 1 := by
  classical
  choose n hn using hint
  have hs := sum_measure_atom hB ρ
  rw [h1] at hs
  simp_rw [hn] at hs
  have hnat : ∑ ε, n ε = 1 := by exact_mod_cast hs
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀, 1 ≤ n ε₀ := by
    by_contra hcon
    push Not at hcon
    have : ∀ ε, n ε = 0 := fun ε => by have := hcon ε; omega
    simp [this] at hnat
  have hle : n ε₀ ≤ 1 := hnat ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ ε₀)
  refine ⟨ε₀, ?_⟩
  rw [hn, show n ε₀ = 1 by omega]
  simp

end ElboimSly
