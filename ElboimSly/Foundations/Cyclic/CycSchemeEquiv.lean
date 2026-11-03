/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.SegmentCircle
public import ElboimSly.Foundations.Cyclic.CycRecord
public import Mathlib

/-!
# The associativity equivalence `cycS ≃ᵐ E × 𝕋`

The environment scheme of a plan (the segment probe of segment probes on E×mathbbT_β and E×mathbbR, case (i), on
`E = I × Ed`, `X = 𝕋 = AddCircle β`).

The cyclic space is `cycS = I × RingSpace d β = I × (Edge d × AddCircle β)` with the intensity
`μ = # ⊗ (# ⊗ Leb_β)`, while the segment API lives on `E × X` with `# ⊗ Leb_β`, `E = I × Edge d`.
`cycEquiv` is the measurable equivalence `I × (Edge d × 𝕋) ≃ᵐ (I × Edge d) × 𝕋`; it preserves the
intensities (`cycEquiv_measurePreserving`).

`cycSegR A x sinv h Z` is the segment probe on `cycS` with mask `Z ⊆ cycS`: it is `segR` with the
mask `cycEquiv.symm ⁻¹' Z` composed with `cycEquiv`. The `simp` lemmas `cycSegR_apply`,
`mem_cycMask_iff` say how masks, regions and slices transport.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The cyclic space `𝒮 = I × Ed × 𝕋`. -/
abbrev CycS (I : Type*) (d : ℕ) (β : ℝ) : Type _ := I × RingSpace d β

/-- The intensity `μ = # ⊗ μ_β` on the cyclic space. -/
noncomputable def cycIntensity (I : Type*) [MeasurableSpace I] (d : ℕ) (β : ℝ) [Fact (0 < β)] :
    Measure (CycS I d β) :=
  (Measure.count : Measure I).prod (ringIntensity d β)

/-- The associativity equivalence `I × (Ed × 𝕋) ≃ᵐ (I × Ed) × 𝕋`. -/
def cycEquiv : CycS I d β ≃ᵐ (I × Edge d) × AddCircle β :=
  MeasurableEquiv.prodAssoc.symm

theorem count_prod_count_eq [Countable I] [MeasurableSingletonClass I] :
    ((Measure.count : Measure I).prod (Measure.count : Measure (Edge d))) =
      (Measure.count : Measure (I × Edge d)) := by
  refine Measure.ext_of_singleton ?_
  intro p
  rw [Measure.count_singleton]
  have : ({p} : Set (I × Edge d)) = ({p.1} : Set I) ×ˢ ({p.2} : Set (Edge d)) := by
    ext q; simp [Prod.ext_iff]
  rw [this, Measure.prod_prod, Measure.count_singleton, Measure.count_singleton, one_mul]

/-- The equivalence preserves the intensities. -/
theorem cycEquiv_measurePreserving [Countable I] [MeasurableSingletonClass I] :
    MeasurePreserving (cycEquiv (I := I) (d := d) (β := β)) (cycIntensity I d β)
      ((Measure.count : Measure (I × Edge d)).prod (volume : Measure (AddCircle β))) := by
  have : SFinite (Measure.count : Measure I) := inferInstance
  have h := (measurePreserving_prodAssoc (Measure.count : Measure I)
    (Measure.count : Measure (Edge d)) (volume : Measure (AddCircle β))).symm
  rw [count_prod_count_eq] at h
  exact h

/-- The segment probe on `cycS` with mask `Z ⊆ cycS`. -/
noncomputable def cycSegR (A : Finset (I × Edge d)) (x : I × Edge d → ℝ → AddCircle β)
    (sinv : I × Edge d → AddCircle β → ℝ) (h : ℝ≥0) (Z : Set (CycS I d β))
    (s : CycS I d β) : ℝ≥0∞ :=
  segR A x sinv h (cycEquiv.symm ⁻¹' Z) (cycEquiv s)

omit [Fact (0 < β)] in
@[simp] theorem cycSegR_apply (A : Finset (I × Edge d)) (x : I × Edge d → ℝ → AddCircle β)
    (sinv : I × Edge d → AddCircle β → ℝ) (h : ℝ≥0) (Z : Set (CycS I d β))
    (ι : I) (e : Edge d) (θ : AddCircle β) :
    cycSegR A x sinv h Z (ι, (e, θ)) = segR A x sinv h (cycEquiv.symm ⁻¹' Z) ((ι, e), θ) := rfl

omit [Fact (0 < β)] in
@[simp] theorem mem_cycMask_iff (Z : Set (CycS I d β)) (y : (I × Edge d) × AddCircle β) :
    y ∈ (cycEquiv (I := I) (d := d) (β := β)).symm ⁻¹' Z ↔ (y.1.1, (y.1.2, y.2)) ∈ Z := Iff.rfl

omit [Fact (0 < β)] in
theorem measurableSet_cycMask {Z : Set (CycS I d β)} (hZ : MeasurableSet Z) :
    MeasurableSet ((cycEquiv (I := I) (d := d) (β := β)).symm ⁻¹' Z) :=
  cycEquiv.symm.measurable hZ

/-- A probe transports along a measure-preserving equivalence. -/
theorem isProbe_comp_equiv {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] {μ : Measure S}
    {ν : Measure T} (e : S ≃ᵐ T) (he : MeasurePreserving e μ ν) {R : T → ℝ≥0∞} {h : ℝ≥0}
    (hP : IsProbe ν R h) : IsProbe μ (R ∘ e) h := by
  refine ⟨hP.measurable.comp e.measurable, ?_, fun r hr => ?_⟩
  · have : probeRegion (R ∘ e) h = e ⁻¹' probeRegion R h := rfl
    rw [this, he.measure_preimage_equiv]
    exact hP.mass_lt_top
  · have : {x | (R ∘ e) x = r} = e ⁻¹' {y | R y = r} := rfl
    rw [this, he.measure_preimage_equiv]
    exact hP.measure_eq_zero r hr

/-- Segment probes on E×mathbbT_β and E×mathbbR (i), (a), transported to `cycS`: the cyclic segment probe is a
probe for `μ`. -/
theorem isProbe_cycSegR [Countable I] [MeasurableSingletonClass I] (A : Finset (I × Edge d))
    (t σ : I × Edge d → ℝ) (hσ : ∀ e, σ e = 1 ∨ σ e = -1) (h : ℝ≥0) (hh : (h : ℝ) ≤ β)
    {Z : Set (CycS I d β)} (hZ : MeasurableSet Z) :
    IsProbe (cycIntensity I d β) (cycSegR A (circX t σ) (circS t σ) h Z) h :=
  isProbe_comp_equiv cycEquiv cycEquiv_measurePreserving
    (isProbe_segR_circle A t σ hσ h hh (measurableSet_cycMask hZ))

end ElboimSly.Cyclic

end
