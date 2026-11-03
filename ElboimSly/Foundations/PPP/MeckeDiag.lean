/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.MeckeSets
public import Mathlib

/-!
# The off-diagonal is of full product measure

Factorial moment measures (the diffuseness of `μ` makes `μ^{⊗ n}` live on `Λ^n_≠`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S]

namespace SepPartSeq

variable {D : SepPartSeq S}

theorem sigmaFinite_of_isDissecting {μ : Measure S} (h : D.IsDissecting μ) : SigmaFinite μ :=
  ⟨⟨{ set := D.cell 0
      set_mem := fun _ => Set.mem_univ _
      finite := h
      spanning := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
        exact ⟨D.idx 0 x, rfl⟩ }⟩⟩

theorem pi_coords_eq_null (D : SepPartSeq S) {n : ℕ} {μ : Measure S} [SigmaFinite μ]
    (hdiff : ∀ x, μ {x} = 0) {i j : Fin n} (hij : i ≠ j) :
    Measure.pi (fun _ : Fin n => μ) {x : Fin n → S | x i = x j} = 0 := by
  have : NullSingletonClass μ := ⟨hdiff⟩
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => μ) (fun l => l = i)
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => S) (fun l => l = i)
  let E : Set ((∀ l : {l // l = i}, S) × (∀ l : {l // ¬ l = i}, S)) :=
    {p | p.1 ⟨i, rfl⟩ = p.2 ⟨j, fun h => hij h.symm⟩}
  have hE : {x : Fin n → S | x i = x j} = e ⁻¹' E := rfl
  have hEm : MeasurableSet E := by
    have : E = ⋂ m, {p : (∀ l : {l // l = i}, S) × (∀ l : {l // ¬ l = i}, S) |
        D.idx m (p.1 ⟨i, rfl⟩) = D.idx m (p.2 ⟨j, fun h => hij h.symm⟩)} := by
      ext p
      simp only [E, Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h m; rw [h]
      · intro h
        by_contra hne
        obtain ⟨m, hm⟩ := D.separate _ _ hne
        exact hm (h m)
    rw [this]
    exact MeasurableSet.iInter fun m => measurableSet_eq_fun
      ((D.measurable_idx m).comp ((measurable_pi_apply _).comp measurable_fst))
      ((D.measurable_idx m).comp ((measurable_pi_apply _).comp measurable_snd))
  rw [hE, hmp.measure_preimage_equiv, Measure.prod_apply_symm hEm]
  have hz : ∀ y : (∀ l : {l // ¬ l = i}, S),
      Measure.pi (fun _ : {l // l = i} => μ) ((fun a => (a, y)) ⁻¹' E) = 0 := fun y =>
    Measure.pi_hyperplane (fun _ : {l // l = i} => μ) ⟨i, rfl⟩ (y ⟨j, fun h => hij h.symm⟩)
  refine le_antisymm ?_ bot_le
  refine (lintegral_mono (g := fun _ => (0 : ℝ≥0∞)) fun y => ?_).trans lintegral_zero.le
  convert (hz y).le

end SepPartSeq

end ElboimSly
