/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.BaseSpaceBM
public import Mathlib

/-!
# The Brownian motion of the base coupling

ES22 (8.3): base coupling with precision n^10 ("The Brownian motion"), via Brownian interpolation of a Gaussian walk.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

open SRW

/-- A family whose joint law is a product measure is independent with the marginal laws. -/
theorem iIndep_hasLaw {Ω ι T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (U : ι → Ω → T) (hU : ∀ i, Measurable (U i)) (Q : ι → Measure T)
    [∀ i, IsProbabilityMeasure (Q i)] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : P.map (fun ω i => U i ω) = Measure.infinitePi Q) :
    iIndepFun U P ∧ ∀ i, HasLaw (U i) (Q i) P := by
  have hfam : Measurable fun ω i => U i ω := measurable_pi_iff.2 hU
  have hlaw : ∀ i, P.map (U i) = Q i := by
    intro i
    have : U i = (fun x : ι → T => x i) ∘ (fun ω i => U i ω) := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply i) hfam, h, Measure.infinitePi_map_eval]
  refine ⟨(iIndepFun_iff_map_fun_eq_infinitePi_map hU).2 ?_, fun i => ⟨(hU i).aemeasurable, hlaw i⟩⟩
  simp_rw [hlaw]
  exact h

variable {d N : ℕ} {μN : Measure ((Fin N → ℝ) × (Fin N → ℝ))} [IsProbabilityMeasure μN]

/-- The Brownian motion of the base coupling. -/
theorem base_brownian (hμ2 : μN.map Prod.snd = Measure.pi fun _ : Fin N => gaussianReal 0 1) :
    ∃ B : NNReal → OmBase d N → Fin d → ℝ,
      IsStandardBrownianMotion d B (PBase d N μN) ∧
      ∀ (j : ℕ) (ω : OmBase d N), B j ω = ∑ m ∈ Finset.range j, Xfam d N ω.1 m := by
  set X : ℕ → OmBase d N → Fin d → ℝ := fun m ω => Xfam d N ω.1 m with hX
  set η : Brownian.BridgeIdx d → OmBase d N → ℝ := fun β ω => ω.2 β with hη
  have hXm : ∀ m, Measurable (X m) := fun m =>
    (measurable_pi_apply m).comp (measurable_Xfam.comp measurable_fst)
  have hηm : ∀ β, Measurable (η β) := fun β => (measurable_pi_apply β).comp measurable_snd
  have hXfam : (PBase d N μN).map (fun ω i => X i ω) =
      Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
    have : (fun ω i => X i ω) = Xfam d N ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map measurable_Xfam measurable_fst, map_fst_PBase, map_Xfam hμ2]
    rfl
  have hηfam : (PBase d N μN).map (fun ω β => η β ω) =
      Measure.infinitePi fun _ : Brownian.BridgeIdx d => gaussianReal 0 1 := by
    have : (fun ω β => η β ω) = (id : SH d → SH d) ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map measurable_id measurable_snd, map_snd_PBase, Measure.map_id]
    rfl
  obtain ⟨hXind, hXlaw⟩ := iIndep_hasLaw X hXm _ _ hXfam
  obtain ⟨hηind, hηlaw⟩ := iIndep_hasLaw η hηm _ _ hηfam
  have hXη : IndepFun (fun ω m => X m ω) (fun ω β => η β ω) (PBase d N μN) :=
    indepFun_prod (μ := PMain d N μN) (ν := PH d) (X := Xfam d N) (Y := id)
      measurable_Xfam measurable_id
  refine ⟨Brownian.levyCiesielski (Brownian.interpXi X η),
    Brownian.isStandardBrownianMotion_interp hXm hηm hXind hXlaw hηind hηlaw hXη, ?_⟩
  intro j ω
  exact Brownian.levyCiesielski_interpXi_nat X η j ω

end StrongApprox
end ElboimSly
