/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Existence
public import ElboimSly.Foundations.Brownian.GaussChar
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily
import Mathlib

/-!
# The law of Brownian motion

Gaussian-process characterization (full iff), the law of Brownian motion.

* `isStandardBrownianMotion_iff_gaussian`: the full characterization.
* `fddLaw d I`: the finite-dimensional law `γ_{I,d}` on `I → Fin d → ℝ`.
* `IsStandardBrownianMotion.map_restrict_eq`: the law of Brownian motion (a).
* `wienerMeasure d`: Wiener measure on `ℝ≥0 → Fin d → ℝ`, the law of the canonical
  Lévy–Ciesielski process.
* `IsStandardBrownianMotion.map_path_eq_wiener`: the law of Brownian motion (b).
* `IsStandardBrownianMotion.measure_affine_preimage`: the law of Brownian motion (c).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- Gaussian-process characterization. Full characterization of standard Brownian motion among
processes satisfying (BM0) and (BM1). -/
theorem isStandardBrownianMotion_iff_gaussian [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (h0 : ∀ t, Measurable (B t))
    (h1 : ∀ ω, Continuous (fun t => B t ω) ∧ B 0 ω = 0) :
    IsStandardBrownianMotion d B P ↔
      IsGaussianProcess (fun (p : Σ _ : Fin d, ℝ≥0) ω => B p.2 ω p.1) P ∧
      (∀ p : Σ _ : Fin d, ℝ≥0, ∫ ω, B p.2 ω p.1 ∂P = 0) ∧
      (∀ p q : Σ _ : Fin d, ℝ≥0,
        cov[fun ω => B p.2 ω p.1, fun ω => B q.2 ω q.1; P] =
          if p.1 = q.1 then ((min p.2 q.2 : ℝ≥0) : ℝ) else 0) :=
  ⟨fun h => ⟨h.isGaussianProcess, h.integral_eval, h.covariance_eval⟩,
    fun ⟨hG, hm, hc⟩ => isStandardBrownianMotion_of_gaussian h0 h1 hG hm hc⟩

/-- The finite-dimensional law `γ_{I,d}` of standard `d`-dimensional Brownian motion on a finite
set of times `I`: the image of the product of the one-dimensional laws. -/
noncomputable def fddLaw (d : ℕ) (I : Finset ℝ≥0) : Measure (I → Fin d → ℝ) :=
  (Measure.pi fun _ : Fin d => (BrownianReal.projectiveFamily I)).map
    (fun (x : Fin d → I → ℝ) (t : I) (i : Fin d) => x i t)

lemma measurable_swapCoord (d : ℕ) (I : Finset ℝ≥0) :
    Measurable (fun (x : Fin d → I → ℝ) (t : I) (i : Fin d) => x i t) :=
  measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ => by fun_prop

/-- The law of Brownian motion (a). The finite-dimensional laws of a standard Brownian motion are
`fddLaw d I`; in particular they depend only on `I` and `d`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.map_restrict_eq [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (I : Finset ℝ≥0) :
    P.map (fun ω => I.restrict (B · ω)) = fddLaw d I := by
  classical
  let V : Fin d → Ω → (I → ℝ) := fun i ω => I.restrict (fun t => B t ω i)
  have hVind : iIndepFun V P :=
    hB.iIndepFun.comp (fun _ (w : ℝ≥0 → ℝ) => I.restrict w)
      (fun _ => measurable_pi_iff.2 fun t => measurable_pi_apply _)
  have hVm : ∀ i, Measurable (V i) := fun i =>
    measurable_pi_iff.2 fun t => (measurable_pi_apply i).comp (hB.measurable t)
  have hVm' : Measurable (fun ω i => V i ω) := measurable_pi_iff.2 hVm
  have hlaw : P.map (fun ω i => V i ω) = Measure.pi fun _ : Fin d => BrownianReal.projectiveFamily I := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hVm i).aemeasurable)).1 hVind]
    congr 1
    funext i
    exact ((hB.isPreBrownianReal i).hasLaw I).map_eq
  have : (fun ω => I.restrict (B · ω)) =
      (fun (x : Fin d → I → ℝ) (t : I) (i : Fin d) => x i t) ∘ (fun ω i => V i ω) := rfl
  rw [this, ← Measure.map_map (measurable_swapCoord d I) hVm', hlaw]
  rfl

/-- The path map `ω ↦ (t ↦ B t ω)` into the path space `ℝ≥0 → Fin d → ℝ`. -/
def pathMap (B : ℝ≥0 → Ω → (Fin d → ℝ)) (ω : Ω) : ℝ≥0 → Fin d → ℝ := fun t => B t ω

lemma _root_.ElboimSly.IsStandardBrownianMotion.measurable_pathMap {B : ℝ≥0 → Ω → (Fin d → ℝ)}
    (hB : IsStandardBrownianMotion d B P) : Measurable (pathMap B) :=
  measurable_pi_iff.2 hB.measurable

/-- Wiener measure on the path space `ℝ≥0 → Fin d → ℝ`: the law of the canonical
Lévy–Ciesielski process on `ℝ^{Idx d}` with the product Gaussian measure. -/
noncomputable def wienerMeasure (d : ℕ) : Measure (ℝ≥0 → Fin d → ℝ) :=
  (Measure.infinitePi fun _ : Idx d => gaussianReal 0 1).map
    (pathMap (levyCiesielski (fun (α : Idx d) (ω : Idx d → ℝ) => ω α)))

/-- The law of Brownian motion (b), uniqueness. Two standard Brownian motions, possibly on different
probability spaces, have the same path law. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.map_pathMap_eq {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} {B' : ℝ≥0 → Ω' → (Fin d → ℝ)}
    (hB : IsStandardBrownianMotion d B P) (hB' : IsStandardBrownianMotion d B' P') :
    P.map (pathMap B) = P'.map (pathMap B') := by
  have h := isProjectiveLimit_map (P := P) (X := fun t ω => B t ω)
    hB.measurable_pathMap.aemeasurable
  have h' := isProjectiveLimit_map (P := P') (X := fun t ω => B' t ω)
    hB'.measurable_pathMap.aemeasurable
  have e : (fun I : Finset ℝ≥0 => P.map (fun ω => I.restrict (B · ω))) =
      fun I => P'.map (fun ω => I.restrict (B' · ω)) := by
    funext I
    rw [hB.map_restrict_eq, hB'.map_restrict_eq]
  rw [e] at h
  exact h.unique h'

/-- The law of Brownian motion (b). The path law of every standard Brownian motion is
`wienerMeasure d`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.map_pathMap_eq_wiener [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) :
    P.map (pathMap B) = wienerMeasure d := by
  let μ : Idx d → Measure ℝ := fun _ => gaussianReal 0 1
  have hind : iIndepFun (fun (α : Idx d) (x : Idx d → ℝ) => x α) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (P := μ) (X := fun _ x => x) fun _ => measurable_id
  have hlaw : ∀ α, HasLaw (fun (x : Idx d → ℝ) => x α) (gaussianReal 0 1)
      (Measure.infinitePi μ) := fun α =>
    ⟨(measurable_pi_apply α).aemeasurable, Measure.infinitePi_map_eval μ α⟩
  have hB0 := isStandardBrownianMotion_levyCiesielski (P := Measure.infinitePi μ)
    (ξ := fun (α : Idx d) (x : Idx d → ℝ) => x α) (fun α => measurable_pi_apply α) hind hlaw
  exact hB.map_pathMap_eq hB0

/-- The law of Brownian motion (c). For measurable `A` of path space, `x ∈ ℝ^d`, `σ`:
`P(x + σ B ∈ A) = wiener {w | x + σ w ∈ A}`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.measure_affine_preimage [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (x : Fin d → ℝ) (σ : ℝ)
    {A : Set (ℝ≥0 → Fin d → ℝ)} (hA : MeasurableSet A) :
    P {ω | (fun t => x + σ • B t ω) ∈ A} =
      wienerMeasure d {w | (fun t => x + σ • w t) ∈ A} := by
  have hf : Measurable (fun (w : ℝ≥0 → Fin d → ℝ) (t : ℝ≥0) => x + σ • w t) :=
    measurable_pi_iff.2 fun t => by fun_prop
  rw [← hB.map_pathMap_eq_wiener]
  exact (Measure.map_apply hB.measurable_pathMap (hf hA)).symm

end ElboimSly.Brownian
