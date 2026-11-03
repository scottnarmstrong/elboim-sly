/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenCoupleDef
public import ElboimSly.Foundations.Cyclic.CycRegenShiftLaw
public import Mathlib

/-!
# ES22 Lemma 2.1: the slices of `Ñ_T` and of `M = Sh_Z Ñ_T`

ES22 Lemma 2.1, proof, "Case `L = 0`" and "Case `L > 0`": for the
environment `Ñ = ν|_{S∖R_t} + ν'|_{R_t}` with `R_t` the region of the truncated record of `ν`:
* the copies `j > k_t` of `Ñ` are those of `ν` (`cycSlice_tilde_gt`);
* the copy `k_t` of `Ñ` agrees with that of `ν` off `ℛ_{(0,L]}(w)` (`cycSlice_tilde_last_compl`);
* the slices of `Sh_Z Ñ` are `seqCons ((φ_{(x,L)})_* Ñ^{k_t}) (ν^·) k_t` (`slices_cycShift_tilde`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem cycSlice_restrict (j : ℕ) (ν : Measure (ℕ × RingSpace d β)) {S : Set (ℕ × RingSpace d β)}
    (_hS : MeasurableSet S) : cycSlice j (ν.restrict S) = (cycSlice j ν).restrict (Prod.mk j ⁻¹' S) := by
  ext B hB
  have hi := (measurableEmbedding_prodMk_left (β := RingSpace d β) j).measurableSet_image.2 hB
  unfold cycSlice
  rw [(measurableEmbedding_prodMk_left j).comap_apply, Measure.restrict_apply hi,
    Measure.restrict_apply hB, (measurableEmbedding_prodMk_left j).comap_apply,
    Set.image_inter_preimage, inter_comm]

theorem cycSlice_add (j : ℕ) (ν ν' : Measure (ℕ × RingSpace d β)) :
    cycSlice j (ν + ν') = cycSlice j ν + cycSlice j ν' := by
  ext B hB
  unfold cycSlice
  simp only [(measurableEmbedding_prodMk_left j).comap_apply, Measure.add_apply]

/-- `Ñ = ν|_{S∖R} + ν'|_R` in the environment picture. -/
noncomputable abbrev tildeEnv (ν ν' : Measure (ℕ × RingSpace d β)) (R : Set (ℕ × RingSpace d β)) :
    Measure (ℕ × RingSpace d β) :=
  ν.restrict Rᶜ + ν'.restrict R

theorem cycSlice_tildeEnv (j : ℕ) (ν ν' : Measure (ℕ × RingSpace d β))
    {R : Set (ℕ × RingSpace d β)} (hR : MeasurableSet R) :
    cycSlice j (tildeEnv ν ν' R) =
      (cycSlice j ν).restrict (Prod.mk j ⁻¹' R)ᶜ + (cycSlice j ν').restrict (Prod.mk j ⁻¹' R) := by
  unfold tildeEnv
  rw [cycSlice_add, cycSlice_restrict j ν hR.compl, cycSlice_restrict j ν' hR]
  rfl

theorem cycSlice_tildeEnv_of_empty (j : ℕ) (ν ν' : Measure (ℕ × RingSpace d β))
    {R : Set (ℕ × RingSpace d β)} (hR : MeasurableSet R) (h : Prod.mk j ⁻¹' R = ∅) :
    cycSlice j (tildeEnv ν ν' R) = cycSlice j ν := by
  rw [cycSlice_tildeEnv j ν ν' hR, h]
  simp

theorem cycSlice_tildeEnv_compl (j : ℕ) (ν ν' : Measure (ℕ × RingSpace d β))
    {R : Set (ℕ × RingSpace d β)} (hR : MeasurableSet R) {C : Set (RingSpace d β)}
    (hC : MeasurableSet C) (h : Prod.mk j ⁻¹' R = C) :
    (cycSlice j (tildeEnv ν ν' R)).restrict Cᶜ = (cycSlice j ν).restrict Cᶜ := by
  rw [cycSlice_tildeEnv j ν ν' hR, h]
  exact restrict_tilde_compl _ _ hC

theorem measurableSet_region_trunc (ρ : CycRec ℕ d) :
    MeasurableSet (ρ.region β) := by
  have : Nonempty (CycEntry ℕ d) := ⟨((regPlan d β).junk)⟩
  exact (measurableSet_region (I := ℕ) (d := d) (β := β)).preimage
    (measurable_prodMk_left (x := ρ))

/-- The slices of `Sh_z Ñ` for `z = (k, x, L)`. -/
theorem slices_cycShift (z : ShiftPar d) (Y : Measure (ℕ × RingSpace d β))
    (hY : Y ∈ lfSet (cycIntensity ℕ d β)) (ν : ℕ → Measure (RingSpace d β))
    (hgt : ∀ j, z.1 < j → cycSlice j Y = ν j) :
    slices (cycShift z Y) =
      seqCons ((cycSlice z.1 Y).map (hitPhi z.2.1 z.2.2)) ν z.1 := by
  funext j
  cases j with
  | zero =>
    show cycSlice 0 (cycShift z Y) = _
    rw [cycSlice_zero_cycShift, tau_of_mem _ hY]
    rfl
  | succ j =>
    show cycSlice (j + 1) (cycShift z Y) = ν (z.1 + 1 + j)
    rw [cycSlice_succ_cycShift, tau_of_mem _ hY]
    exact hgt _ (by omega)

end ElboimSly.Cyclic

end
