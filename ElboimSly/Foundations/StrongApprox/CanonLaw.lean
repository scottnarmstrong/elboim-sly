/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.Wald
public import ElboimSly.Foundations.Brownian.Existence
public import Mathlib

/-!
# The law of a Brownian path on `C0`

Measurability of the embedding (e) (Part II).

The set of continuous paths vanishing at `0` is not measurable in the product `σ`-algebra, but it
carries the trace `σ`-algebra (`C0`), on which exit times and the iterated embedding are
measurable. We show that all standard real Brownian motions, on all probability spaces, induce the
same law `wienerC0` on `C0`. Hence the law of any functional of the path (the embedding) is the same
for all Brownian motions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

/-- The path of a process, as an element of `C0`. -/
def pathC0 {Ω : Type*} [MeasurableSpace Ω] {β : ℝ≥0 → Ω → ℝ} (hβ : IsProcess β) (ω : Ω) : C0 :=
  ⟨fun t => β t ω, hβ.1 ω⟩

lemma measurable_pathC0 {Ω : Type*} [MeasurableSpace Ω] {β : ℝ≥0 → Ω → ℝ} (hβ : IsProcess β) :
    Measurable (pathC0 hβ) :=
  Measurable.subtype_mk (measurable_pi_iff.2 hβ.2)

/-- The law of the path of any standard real Brownian motion on `C0` does not depend on the
Brownian motion. -/
theorem map_pathC0_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {β : ℝ≥0 → Ω → ℝ}
    {β' : ℝ≥0 → Ω' → ℝ} (hβ : IsStandardRealBM β P) (hβ' : IsStandardRealBM β' P') :
    P.map (pathC0 (isProcess_of_realBM hβ)) = P'.map (pathC0 (isProcess_of_realBM hβ')) := by
  refine Measure.ext fun S hS => ?_
  obtain ⟨T, hT, rfl⟩ := hS
  rw [Measure.map_apply (measurable_pathC0 _) ⟨T, hT, rfl⟩,
    Measure.map_apply (measurable_pathC0 _) ⟨T, hT, rfl⟩]
  have h1 := hβ.map_realPath
  have h2 := hβ'.map_realPath
  have hm1 : Measurable (realPath β) := measurable_pi_iff.2 hβ.measurable
  have hm2 : Measurable (realPath β') := measurable_pi_iff.2 hβ'.measurable
  have e1 : P (pathC0 (isProcess_of_realBM hβ) ⁻¹' (Subtype.val ⁻¹' T)) =
      P.map (realPath β) T := by
    rw [Measure.map_apply hm1 hT]; rfl
  have e2 : P' (pathC0 (isProcess_of_realBM hβ') ⁻¹' (Subtype.val ⁻¹' T)) =
      P'.map (realPath β') T := by
    rw [Measure.map_apply hm2 hT]; rfl
  rw [e1, e2, h1, h2]

/-! ### A concrete Brownian motion -/

/-- The sample space of the Lévy–Ciesielski construction in dimension one. -/
abbrev Ω₀ : Type := Idx 1 → ℝ

/-- The product Gaussian measure on `Ω₀`. -/
noncomputable def P₀ : Measure Ω₀ := Measure.infinitePi fun _ : Idx 1 => gaussianReal 0 1

instance : IsProbabilityMeasure P₀ := by unfold P₀; infer_instance

/-- The Lévy–Ciesielski Brownian motion. -/
noncomputable def β₀ : ℝ≥0 → Ω₀ → ℝ :=
  fun t ω => levyCiesielski (fun (α : Idx 1) (ω : Idx 1 → ℝ) => ω α) t ω 0

theorem isStandardRealBM_β₀ : IsStandardRealBM β₀ P₀ := by
  let μ : Idx 1 → Measure ℝ := fun _ => gaussianReal 0 1
  have hind : iIndepFun (fun (α : Idx 1) (x : Idx 1 → ℝ) => x α) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (P := μ) (X := fun _ x => x) fun _ => measurable_id
  have hlaw : ∀ α, HasLaw (fun (x : Idx 1 → ℝ) => x α) (gaussianReal 0 1)
      (Measure.infinitePi μ) := fun α =>
    ⟨(measurable_pi_apply α).aemeasurable, Measure.infinitePi_map_eval μ α⟩
  have hB0 := isStandardBrownianMotion_levyCiesielski (P := Measure.infinitePi μ)
    (ξ := fun (α : Idx 1) (x : Idx 1 → ℝ) => x α) (fun α => measurable_pi_apply α) hind hlaw
  exact isStandardRealBM_of_dim_one hB0

/-- The canonical law of a standard real Brownian motion on `C0`. -/
noncomputable def wienerC0 : Measure C0 :=
  P₀.map (pathC0 (isProcess_of_realBM isStandardRealBM_β₀))

instance : IsProbabilityMeasure wienerC0 := by
  unfold wienerC0
  exact (Measure.isProbabilityMeasure_map_iff (measurable_pathC0 _).aemeasurable).2 inferInstance

/-- Every standard real Brownian motion has the path law `wienerC0` on `C0`. -/
theorem map_pathC0 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {β : ℝ≥0 → Ω → ℝ} (hβ : IsStandardRealBM β P) :
    P.map (pathC0 (isProcess_of_realBM hβ)) = wienerC0 :=
  map_pathC0_eq hβ isStandardRealBM_β₀

end ElboimSly.StrongApprox
