/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ThmKernel
import Mathlib

/-!
# Sequential first-point exploration: the law-level induction

Sequential first-point exploration (b), (d).

Everything is stated on `Λ = ν_U ⊗ W` on `𝕌 × 𝓜(S)`, the law of `(U, N)`. We prove by induction on `k`:

* `(J_k)`: for measurable `F`, `E F(H_k, N|_{S∖Z_k}) = E Φ_F(H_k)`;
* `(D_k)`: for measurable `g`, `E g(H_{k+1}) = E ∫ g(H_k, o) K_k(H_k, do)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U] {μ : Measure S}
  [SigmaFinite μ] (sch : ExplScheme μ U) {W : Measure (Measure S)} (νU : Measure U)

namespace ExplScheme

/-- `(J_k)`: the unexplored part is fresh. -/
def FreshAt (W : Measure (Measure S)) (νU : Measure U) (k : ℕ) : Prop :=
  ∀ F : Hist U S k × Measure S → ℝ≥0∞, Measurable F →
    ∫⁻ x, F (sch.Hfun k x, sch.unexpl k (sch.Hfun k x) x.2) ∂(νU.prod W) =
      ∫⁻ x, ∫⁻ ν, F (sch.Hfun k x, sch.unexpl k (sch.Hfun k x) ν) ∂W ∂(νU.prod W)

/-- `(D_k)`: one-step law. -/
def StepLawAt (W : Measure (Measure S)) (νU : Measure U) (k : ℕ) : Prop :=
  ∀ g : Hist U S (k + 1) → ℝ≥0∞, Measurable g →
    ∫⁻ x, g (sch.Hfun (k + 1) x) ∂(νU.prod W) =
      ∫⁻ x, ∫⁻ o, g ((sch.Hfun k x).snoc o) ∂(sch.kernelAt k (sch.Hfun k x)) ∂(νU.prod W)

variable [IsProbabilityMeasure νU]

omit [IsProbabilityMeasure νU] in
theorem freshAt_zero (hW : IsPPPLaw μ W) : sch.FreshAt W νU 0 := by
  have := hW.isProbabilityMeasure
  intro F hF
  have hu : ∀ (η : Hist U S 0) (ν : Measure S), sch.unexpl 0 η ν = tau μ ν := by
    intro η ν
    simp [unexpl, Z]
  simp_rw [hu]
  have hm : Measurable fun x : U × Measure S => F (sch.Hfun 0 x, tau μ x.2) :=
    hF.comp (((sch.measurable_Hfun 0)).prodMk ((measurable_tau μ).comp measurable_snd))
  rw [lintegral_prod _ hm.aemeasurable]
  rw [lintegral_prod _ (Measurable.lintegral_prod_right' (ν := W) (f := fun p : (U × Measure S) × Measure S =>
    F (sch.Hfun 0 p.1, tau μ p.2)) (hF.comp ((((sch.measurable_Hfun 0).comp measurable_fst)).prodMk
      ((measurable_tau μ).comp measurable_snd)))).aemeasurable]
  refine lintegral_congr fun u => ?_
  simp [Hfun]

theorem lintegral_stepAt (hW : IsPPPLaw μ W) (k : ℕ) (η : Hist U S k) {φ : Outcome S → ℝ≥0∞}
    (hφ : Measurable φ) : ∫⁻ ν, φ (sch.stepAt k η ν) ∂W = ∫⁻ o, φ o ∂(sch.kernelAt k η) := by
  rw [kernelAt, ← map_probeStep_eq_kernel hW (sch.isProbe_Rt k η),
    lintegral_map hφ (measurable_probeStep μ (sch.isProbe_Rt k η).measurable)]
  rfl

omit [IsProbabilityMeasure νU] in
theorem stepLawAt_of_fresh (hW : IsPPPLaw μ W) (k : ℕ) (hk : sch.FreshAt W νU k) :
    sch.StepLawAt W νU k := by
  have := hW.isProbabilityMeasure
  intro g hg
  let f : Hist U S k × Measure S → ℝ≥0∞ := fun q => g (q.1.snoc (sch.stepAt k q.1 q.2))
  have hf : Measurable f := hg.comp ((Hist.measurable_snoc k).comp
    (measurable_fst.prodMk (sch.measurable_stepAt k)))
  have h1 := hk f hf
  simp only [f, stepAt_unexpl] at h1
  refine h1.trans ?_
  refine lintegral_congr fun x => ?_
  exact sch.lintegral_stepAt hW k _ (hg.comp ((Hist.measurable_snoc k).comp
    (measurable_const.prodMk measurable_id)))

theorem unexpl_succ_unexpl (k : ℕ) (η : Hist U S k) (ν : Measure S) (o : Outcome S) :
    sch.unexpl (k + 1) (η.snoc o) (sch.unexpl k η ν) = sch.unexpl (k + 1) (η.snoc o) ν := by
  have hlf : sch.unexpl k η ν ∈ lfSet μ := restrict_mem_lfSet (tau_mem_lfSet μ ν) _
  conv_rhs => rw [sch.unexpl_snoc_unexpl]
  have e : tau μ ((tau μ ν).restrict (sch.Z k η)ᶜ) = (tau μ ν).restrict (sch.Z k η)ᶜ :=
    tau_of_mem μ hlf
  unfold unexpl
  rw [e]

omit [IsProbabilityMeasure νU] in
theorem freshAt_succ (hW : IsPPPLaw μ W) (k : ℕ) (hk : sch.FreshAt W νU k) :
    sch.FreshAt W νU (k + 1) := by
  have := hW.isProbabilityMeasure
  intro G hG
  let f : Hist U S k × Measure S → ℝ≥0∞ := fun q =>
    G (q.1.snoc (sch.stepAt k q.1 q.2),
      sch.unexpl (k + 1) (q.1.snoc (sch.stepAt k q.1 q.2)) q.2)
  have hsn : Measurable fun q : Hist U S k × Measure S => q.1.snoc (sch.stepAt k q.1 q.2) :=
    (Hist.measurable_snoc k).comp (measurable_fst.prodMk (sch.measurable_stepAt k))
  have hf : Measurable f := hG.comp (hsn.prodMk
    ((sch.measurable_unexpl (k + 1)).comp (hsn.prodMk measurable_snd)))
  have h1 := hk f hf
  have hpt : ∀ (η : Hist U S k) (ν : Measure S), f (η, sch.unexpl k η ν) =
      G (η.snoc (sch.stepAt k η ν), sch.unexpl (k + 1) (η.snoc (sch.stepAt k η ν)) ν) := by
    intro η ν
    simp only [f, stepAt_unexpl, unexpl_succ_unexpl]
  simp only [hpt] at h1
  let Ψ : Hist U S (k + 1) → ℝ≥0∞ := fun η' => ∫⁻ m, G (η', sch.unexpl (k + 1) η' m) ∂W
  have hΨ : Measurable Ψ :=
    Measurable.lintegral_prod_right' (f := fun p : Hist U S (k + 1) × Measure S =>
      G (p.1, sch.unexpl (k + 1) p.1 p.2)) (hG.comp (measurable_fst.prodMk
        (sch.measurable_unexpl (k + 1))))
  have h2 := sch.stepLawAt_of_fresh νU hW k hk Ψ hΨ
  have e : ∀ x : U × Measure S, ∫⁻ ν, G (sch.Hfun k x |>.snoc (sch.stepAt k (sch.Hfun k x) ν),
      sch.unexpl (k + 1) ((sch.Hfun k x).snoc (sch.stepAt k (sch.Hfun k x) ν)) ν) ∂W =
      ∫⁻ o, Ψ ((sch.Hfun k x).snoc o) ∂(sch.kernelAt k (sch.Hfun k x)) := fun x =>
    sch.lintegral_step_unexpl hW k (sch.Hfun k x) hG
  simp only [e] at h1
  exact h1.trans h2.symm

omit [IsProbabilityMeasure νU] in
theorem freshAt_all (hW : IsPPPLaw μ W) (k : ℕ) : sch.FreshAt W νU k := by
  induction k with
  | zero => exact sch.freshAt_zero νU hW
  | succ k ih => exact sch.freshAt_succ νU hW k ih

omit [IsProbabilityMeasure νU] in
theorem stepLawAt_all (hW : IsPPPLaw μ W) (k : ℕ) : sch.StepLawAt W νU k :=
  sch.stepLawAt_of_fresh νU hW k (sch.freshAt_all νU hW k)

end ExplScheme

end ElboimSly
