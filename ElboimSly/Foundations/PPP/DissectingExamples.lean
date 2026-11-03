/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.DissectingProd
public import ElboimSly.Foundations.PPP.ExistenceExamples
public import Mathlib

/-!
# Dissecting systems for the ring and clock spaces

Examples (b), (d).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly

namespace SepPartSeq

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

end SepPartSeq

section Clock

variable (D : Type*) [MeasurableSpace D] [Countable D] [MeasurableSingletonClass D]

/-- Level-`0` cells of `realSeq` have finite mass under `Leb|_{(0,∞)}`. -/
theorem realSeq_isDissecting_restrict_Ioi :
    realSeq.IsDissecting (volume.restrict (Set.Ioi (0 : ℝ))) := by
  intro i
  have hsub : realSeq.cell 0 i ⊆ Set.Ico (((Equiv.intEquivNat.symm i : ℤ)) : ℝ)
      ((Equiv.intEquivNat.symm i : ℤ) + 1) := by
    intro x hx
    have h : Equiv.intEquivNat ⌊x * 2 ^ 0⌋ = i := hx
    have h2 : ⌊x * 2 ^ 0⌋ = Equiv.intEquivNat.symm i := by rw [← h]; simp
    simp only [pow_zero, mul_one] at h2
    exact ⟨h2 ▸ Int.floor_le x, h2 ▸ Int.lt_floor_add_one x⟩
  refine lt_of_le_of_lt (measure_mono hsub) ?_
  exact lt_of_le_of_lt (Measure.restrict_apply_le _ _) (by simp)

/-- The clock space `D × ℝ` with `# ⊗ Leb|_{(0,∞)}` has a generating dissecting system.
Examples (d). -/
noncomputable def clockSeq : SepPartSeq (D × ℝ) := SepPartSeq.prodCount D realSeq

theorem clockSeq_isDissecting : (clockSeq D).IsDissecting (clockIntensity D) :=
  SepPartSeq.prodCount_isDissecting realSeq _ realSeq_isDissecting_restrict_Ioi

omit [Countable D] [MeasurableSingletonClass D] in
theorem clockIntensity_singleton (p : D × ℝ) : clockIntensity D {p} = 0 := by
  have : ({p} : Set (D × ℝ)) = {p.1} ×ˢ {p.2} := by ext ⟨a, b⟩; simp [Prod.ext_iff]
  rw [this, clockIntensity, Measure.prod_prod]
  have : (volume.restrict (Set.Ioi (0 : ℝ))) {p.2} = 0 :=
    le_antisymm ((Measure.restrict_apply_le _ _).trans (by simp)) bot_le
  rw [this, mul_zero]

end Clock

section Ring

variable (E : Type*) [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]
  (β : ℝ) [Fact (0 < β)]

/-- The coordinate on the circle: `θ ↦ -(rep θ)/β` with `rep θ ∈ (0, β]`. -/
noncomputable def circleCoord (θ : AddCircle β) : ℝ :=
  -((AddCircle.measurableEquivIoc β 0 θ : ℝ) / β)

theorem circleCoord_measurableEmbedding : MeasurableEmbedding (circleCoord β) := by
  have h1 : MeasurableEmbedding (fun θ : AddCircle β => (AddCircle.measurableEquivIoc β 0 θ : ℝ)) :=
    (MeasurableEmbedding.subtype_coe measurableSet_Ioc).comp
      (AddCircle.measurableEquivIoc β 0).measurableEmbedding
  have hβ : β ≠ 0 := (Fact.out : 0 < β).ne'
  have h2 : MeasurableEmbedding (fun x : ℝ => -(x / β)) := by
    have := (Homeomorph.neg ℝ).measurableEmbedding.comp
      (Homeomorph.mulRight₀ β⁻¹ (inv_ne_zero hβ)).measurableEmbedding
    convert this using 1
    funext x
    simp [div_eq_mul_inv]
  exact h2.comp h1

/-- The dyadic partitions of the circle `ℝ/βℤ`. Examples (b). -/
noncomputable def circleSeq : SepPartSeq (AddCircle β) :=
  realSeq.comap (circleCoord β) (circleCoord_measurableEmbedding β).measurable
    (circleCoord_measurableEmbedding β).injective

theorem circleSeq_isDissecting : (circleSeq β).IsDissecting (volume : Measure (AddCircle β)) :=
  fun _ => measure_lt_top _ _

/-- The ring space `E × ℝ/βℤ` with `# ⊗ Leb_β`. Examples (d). -/
noncomputable def ringSeq : SepPartSeq (E × AddCircle β) := SepPartSeq.prodCount E (circleSeq β)

theorem ringSeq_isDissecting :
    (ringSeq E β).IsDissecting
      ((Measure.count : Measure E).prod (volume : Measure (AddCircle β))) :=
  SepPartSeq.prodCount_isDissecting (circleSeq β) _ (circleSeq_isDissecting β)

theorem volume_singleton_circle (θ : AddCircle β) :
    (volume : Measure (AddCircle β)) {θ} = 0 := by
  have hm := AddCircle.measurePreserving_mk β 0
  have hmeas : MeasurableSet (((↑) : ℝ → AddCircle β) ⁻¹' {θ}) :=
    hm.measurable (measurableSet_singleton θ)
  rw [← hm.map_eq, Measure.map_apply hm.measurable (measurableSet_singleton θ),
    Measure.restrict_apply hmeas]
  refine measure_mono_null ?_ (Real.volume_singleton (a := (AddCircle.measurableEquivIoc β 0 θ : ℝ)))
  rintro y ⟨hy1, hy2⟩
  have h1 : (AddCircle.measurableEquivIoc β 0).symm ⟨y, hy2⟩ = θ := hy1
  have h2 : AddCircle.measurableEquivIoc β 0 θ = ⟨y, hy2⟩ := by
    rw [← h1, MeasurableEquiv.apply_symm_apply]
  rw [Set.mem_singleton_iff, h2]

omit [Countable E] [MeasurableSingletonClass E] in
theorem ring_singleton (p : E × AddCircle β) :
    ((Measure.count : Measure E).prod (volume : Measure (AddCircle β))) {p} = 0 := by
  have : ({p} : Set (E × AddCircle β)) = {p.1} ×ˢ {p.2} := by ext ⟨a, b⟩; simp [Prod.ext_iff]
  rw [this, Measure.prod_prod, volume_singleton_circle β p.2, mul_zero]

end Ring

end ElboimSly
