/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.ExistenceExamples
public import ElboimSly.Foundations.PPP.Operations
public import ElboimSly.Foundations.PPP.Invariance
public import ElboimSly.Foundations.PPP.Giry
public import ElboimSly.Frozen.Defs.RingIntensity
import Mathlib

/-!
# Translations and local σ-algebras on the space of ring configurations

Translations and local σ-algebras; Properties of translations and local σ-algebras.

We write `ringShift z` for `g_z(e, θ) = (e + z, θ)`, `thetaShift z` for the induced map on measures,
`resMeas F` for restriction to `F × 𝕋`, and `locSigma F` for the events depending only on `F`.
`F - z` is written `edgeShift z ⁻¹' F`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {d : ℕ} {β : ℝ}

/-! ### Translation of edges -/

/-- Translation of an edge by `z ∈ ℤᵈ` (underlying function). -/
def edgeShiftFun (z : Fin d → ℤ) (e : Edge d) : Edge d :=
  ⟨e.1.map (· + z), by
    obtain ⟨e, u, v, rfl, h⟩ := e
    refine ⟨u + z, v + z, by simp, ?_⟩
    simpa [LatticeAdj] using h⟩

theorem edgeShiftFun_zero (e : Edge d) : edgeShiftFun 0 e = e := by
  apply Subtype.ext
  simp [edgeShiftFun]

theorem edgeShiftFun_add (z z' : Fin d → ℤ) (e : Edge d) :
    edgeShiftFun z (edgeShiftFun z' e) = edgeShiftFun (z' + z) e := by
  apply Subtype.ext
  simp only [edgeShiftFun, Sym2.map_map]
  congr 1
  funext u
  simp [add_assoc]

/-- Translation of edges as an equivalence. Translations and local σ-algebras (a). -/
def edgeShift (z : Fin d → ℤ) : Edge d ≃ Edge d where
  toFun := edgeShiftFun z
  invFun := edgeShiftFun (-z)
  left_inv e := by rw [edgeShiftFun_add]; simp [edgeShiftFun_zero]
  right_inv e := by rw [edgeShiftFun_add]; simp [edgeShiftFun_zero]

theorem edgeShift_apply (z : Fin d → ℤ) (e : Edge d) : edgeShift z e = edgeShiftFun z e := rfl

theorem edgeShift_zero (e : Edge d) : edgeShift 0 e = e := edgeShiftFun_zero e

theorem edgeShift_add (z z' : Fin d → ℤ) (e : Edge d) :
    edgeShift z (edgeShift z' e) = edgeShift (z + z') e := by
  simp only [edgeShift_apply, edgeShiftFun_add, add_comm z' z]

/-! ### Translation of the ring space and of measures -/

/-- The translation `g_z(e, θ) = (e + z, θ)` of `S_β`. Translations and local σ-algebras (a). -/
def ringShift (d : ℕ) (β : ℝ) (z : Fin d → ℤ) : RingSpace d β → RingSpace d β :=
  Prod.map (edgeShift z) id

theorem measurable_ringShift (z : Fin d → ℤ) : Measurable (ringShift d β z) :=
  (measurable_of_countable (edgeShift z)).prodMap measurable_id

theorem ringShift_zero (x : RingSpace d β) : ringShift d β 0 x = x := by
  obtain ⟨e, t⟩ := x
  simp only [ringShift, Prod.map_apply, id, edgeShift_zero]

theorem ringShift_add (z z' : Fin d → ℤ) (x : RingSpace d β) :
    ringShift d β z (ringShift d β z' x) = ringShift d β (z + z') x := by
  obtain ⟨e, t⟩ := x
  simp only [ringShift, Prod.map_apply, id, edgeShift_add]

/-- Properties of translations and local σ-algebras (a): `(g_z)_* μ_β = μ_β`. -/
theorem map_ringShift_ringIntensity [Fact (0 < β)] (z : Fin d → ℤ) :
    (ringIntensity d β).map (ringShift d β z) = ringIntensity d β :=
  count_prod_map_invariant _ (edgeShift z) measurable_id Measure.map_id

/-- The action `ϑ_z ν = (g_z)_* ν` on measures. Translations and local σ-algebras (a). -/
noncomputable def thetaShift (d : ℕ) (β : ℝ) (z : Fin d → ℤ) :
    Measure (RingSpace d β) → Measure (RingSpace d β) :=
  fun ν => ν.map (ringShift d β z)

theorem measurable_thetaShift (z : Fin d → ℤ) : Measurable (thetaShift d β z) :=
  measurable_map_measure (measurable_ringShift z)

theorem thetaShift_zero (ν : Measure (RingSpace d β)) : thetaShift d β 0 ν = ν := by
  have : ringShift d β 0 = id := funext ringShift_zero
  simp [thetaShift, this]

theorem thetaShift_add (z z' : Fin d → ℤ) (ν : Measure (RingSpace d β)) :
    thetaShift d β z (thetaShift d β z' ν) = thetaShift d β (z + z') ν := by
  have : ringShift d β z ∘ ringShift d β z' = ringShift d β (z + z') :=
    funext (ringShift_add z z')
  simp only [thetaShift]
  rw [Measure.map_map (measurable_ringShift z) (measurable_ringShift z'), this]

theorem thetaShift_neg_thetaShift (z : Fin d → ℤ) (ν : Measure (RingSpace d β)) :
    thetaShift d β (-z) (thetaShift d β z ν) = ν := by
  rw [thetaShift_add, neg_add_cancel, thetaShift_zero]

theorem thetaShift_thetaShift_neg (z : Fin d → ℤ) (ν : Measure (RingSpace d β)) :
    thetaShift d β z (thetaShift d β (-z) ν) = ν := by
  rw [thetaShift_add, add_neg_cancel, thetaShift_zero]

/-- Properties of translations and local σ-algebras (b): `ϑ_z⁻¹(A) = ϑ_{-z}(A)`. -/
theorem preimage_thetaShift (z : Fin d → ℤ) (A : Set (Measure (RingSpace d β))) :
    thetaShift d β z ⁻¹' A = thetaShift d β (-z) '' A :=
  by
  ext ν
  constructor
  · intro h
    exact ⟨_, h, thetaShift_neg_thetaShift z ν⟩
  · rintro ⟨μ, hμ, rfl⟩
    simpa [thetaShift_neg_thetaShift] using (show thetaShift d β z (thetaShift d β (-z) μ) ∈ A by
      rw [thetaShift_thetaShift_neg]; exact hμ)

/-- Translation invariance of an event. Translations and local σ-algebras (d). -/
def IsShiftInvariant (d : ℕ) (β : ℝ) (A : Set (Measure (RingSpace d β))) : Prop :=
  ∀ z : Fin d → ℤ, thetaShift d β z ⁻¹' A = A

/-- Properties of translations and local σ-algebras (b): invariance iff `ϑ_z(A) ⊆ A` for all `z`. -/
theorem isShiftInvariant_iff (A : Set (Measure (RingSpace d β))) :
    IsShiftInvariant d β A ↔ ∀ z, thetaShift d β z '' A ⊆ A := by
  constructor
  · intro h z
    have := h (-z)
    rw [preimage_thetaShift, neg_neg] at this
    exact this.le
  · intro h z
    apply Set.Subset.antisymm
    · rw [preimage_thetaShift]; exact h _
    · intro ν hν
      exact h z ⟨ν, hν, rfl⟩

/-! ### Restriction and local σ-algebras -/

/-- Restriction to the rings of the edges in `F`: `ρ_F ν = ν|_{F × 𝕋}`. -/
noncomputable def resMeas (d : ℕ) (β : ℝ) (F : Set (Edge d)) :
    Measure (RingSpace d β) → Measure (RingSpace d β) :=
  fun ν => ν.restrict (F ×ˢ Set.univ)

/-- The σ-algebra of events depending only on the rings of the edges in `F`.
Translations and local σ-algebras (b). -/
@[instance_reducible] noncomputable def locSigma (d : ℕ) (β : ℝ) (F : Set (Edge d)) : MeasurableSpace (Measure (RingSpace d β)) :=
  MeasurableSpace.comap (resMeas d β F) inferInstance

theorem measurable_resMeas (F : Set (Edge d)) : Measurable (resMeas d β F) :=
  measurable_restrict_measure (MeasurableSet.prod (MeasurableSet.of_discrete) MeasurableSet.univ)

theorem locSigma_le (F : Set (Edge d)) :
    locSigma d β F ≤ (inferInstance : MeasurableSpace (Measure (RingSpace d β))) :=
  (measurable_resMeas F).comap_le

theorem resMeas_resMeas {F F' : Set (Edge d)} (h : F ⊆ F') (ν : Measure (RingSpace d β)) :
    resMeas d β F (resMeas d β F' ν) = resMeas d β F ν := by
  simp only [resMeas]
  rw [Measure.restrict_restrict (MeasurableSet.prod MeasurableSet.of_discrete MeasurableSet.univ)]
  rw [Set.inter_eq_left.2 (Set.prod_mono h le_rfl)]

/-- Properties of translations and local σ-algebras (d): monotonicity. -/
theorem locSigma_mono {F F' : Set (Edge d)} (h : F ⊆ F') :
    locSigma d β F ≤ locSigma d β F' := by
  rintro _ ⟨C, hC, rfl⟩
  refine ⟨resMeas d β F ⁻¹' C, (measurable_resMeas F) hC, ?_⟩
  ext ν
  simp [resMeas_resMeas h]

theorem preimage_ringShift_prod (z : Fin d → ℤ) (F : Set (Edge d)) :
    ringShift d β z ⁻¹' (F ×ˢ Set.univ) = (edgeShift z ⁻¹' F) ×ˢ Set.univ := by
  ext x; simp [ringShift]

/-- Properties of translations and local σ-algebras (e): `ρ_F ∘ ϑ_z = ϑ_z ∘ ρ_{F - z}`. -/
theorem resMeas_thetaShift (z : Fin d → ℤ) (F : Set (Edge d)) (ν : Measure (RingSpace d β)) :
    resMeas d β F (thetaShift d β z ν) =
      thetaShift d β z (resMeas d β (edgeShift z ⁻¹' F) ν) := by
  simp only [resMeas, thetaShift]
  rw [Measure.restrict_map (measurable_ringShift z)
    (MeasurableSet.prod MeasurableSet.of_discrete MeasurableSet.univ), preimage_ringShift_prod]

/-- Properties of translations and local σ-algebras (e): preimage of a local event is local. -/
theorem measurableSet_locSigma_preimage_thetaShift (z : Fin d → ℤ) {F : Set (Edge d)}
    {A : Set (Measure (RingSpace d β))} (hA : MeasurableSet[locSigma d β F] A) :
    MeasurableSet[locSigma d β (edgeShift z ⁻¹' F)] (thetaShift d β z ⁻¹' A) := by
  obtain ⟨C, hC, rfl⟩ := hA
  refine ⟨thetaShift d β z ⁻¹' C, (measurable_thetaShift z) hC, ?_⟩
  ext ν
  simp [Set.mem_preimage, resMeas_thetaShift]

/-- Properties of translations and local σ-algebras (f): translated finite sets are eventually disjoint. -/
theorem exists_disjoint_edgeShift {F : Set (Edge d)} (hF : F.Finite) :
    ∃ R : ℝ, ∀ z : Fin d → ℤ, R < ‖z‖ → Disjoint F (edgeShift z ⁻¹' F) := by
  have hfin : {u : Fin d → ℤ | ∃ e ∈ F, u ∈ e.1}.Finite := by
    have : {u : Fin d → ℤ | ∃ e ∈ F, u ∈ e.1} = ⋃ e ∈ F, {u | u ∈ e.1} := by
      ext; simp
    rw [this]
    refine hF.biUnion fun e _ => ?_
    obtain ⟨e, _⟩ := e
    induction e using Sym2.ind with
    | h a b => exact (Set.toFinite {a, b}).subset (by intro u hu; simpa [Sym2.mem_iff] using hu)
  obtain ⟨M, hM⟩ := (hfin.image (fun u => ‖u‖)).bddAbove
  refine ⟨2 * M, fun z hz => ?_⟩
  rw [Set.disjoint_left]
  intro e he he'
  have hex : ∀ s : Sym2 (Fin d → ℤ), ∃ u, u ∈ s := fun s => by
    induction s using Sym2.ind with
    | h a b => exact ⟨a, Sym2.mem_mk_left a b⟩
  obtain ⟨u, hu⟩ := hex e.1
  have h1 : ‖u‖ ≤ M := hM ⟨u, ⟨e, he, hu⟩, rfl⟩
  have h2 : ‖u + z‖ ≤ M :=
    hM ⟨u + z, ⟨edgeShift z e, he', Sym2.mem_map.2 ⟨u, hu, rfl⟩⟩, rfl⟩
  have : ‖z‖ ≤ ‖u + z‖ + ‖u‖ := by
    calc ‖z‖ = ‖(u + z) - u‖ := by simp
      _ ≤ ‖u + z‖ + ‖u‖ := norm_sub_le _ _
  linarith

end ElboimSly
