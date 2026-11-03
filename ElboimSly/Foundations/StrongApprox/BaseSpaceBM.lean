/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.BaseSpaceLaw
public import Mathlib

/-!
# The blocks and the Brownian motion on the base coupling space

ES22 (8.3): base coupling with precision n^10 ("The walk": the law of the family of blocks; "The Brownian
motion": the hypotheses of Brownian interpolation of a Gaussian walk).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

open SRW

variable {d N : ℕ} {μN : Measure ((Fin N → ℝ) × (Fin N → ℝ))} [IsProbabilityMeasure μN]

omit [IsProbabilityMeasure μN] in
theorem map_fst_PMain : (PMain d N μN).map Prod.fst = (PA d N μN).prod (PBpts d N) := by
  unfold PMain; simp [Measure.map_fst_prod]

theorem map_snd_PMain : (PMain d N μN).map Prod.snd = (PC d).prod (PX d) := by
  unfold PMain; simp [Measure.map_snd_prod]

omit [IsProbabilityMeasure μN] in
theorem map_fst_PBase : (PBase d N μN).map Prod.fst = PMain d N μN := by
  unfold PBase; simp [Measure.map_fst_prod]

theorem map_snd_PBase : (PBase d N μN).map Prod.snd = PH d := by
  unfold PBase; simp [Measure.map_snd_prod]

/-- The law of the family of blocks is the product of the cell block laws. -/
theorem map_blocks
    (hμ1 : μN.map Prod.fst = Measure.pi fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ)) :
    (PMain d N μN).map (blocks d N) = PC d := by
  have hZ : Measurable fun ω : OmMain d N => zk d N ω.1 := measurable_zk.comp measurable_fst
  have hW : Measurable fun ω : OmMain d N => ω.2.1 := measurable_fst.comp measurable_snd
  have hind : IndepFun (fun ω : OmMain d N => zk d N ω.1) (fun ω : OmMain d N => ω.2.1)
      (PMain d N μN) :=
    indepFun_prod (μ := (PA d N μN).prod (PBpts d N)) (ν := (PC d).prod (PX d))
      (X := zk d N) (Y := fun p : SC d × SX d => p.1) measurable_zk measurable_fst
  have hZlaw : (PMain d N μN).map (fun ω : OmMain d N => zk d N ω.1) =
      Measure.pi fun a : JIdx d N => blockMeasure (cellLaw d (jcell d N a)) (cellMass d (jcell d N a)) := by
    have : (fun ω : OmMain d N => zk d N ω.1) = zk d N ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map measurable_zk measurable_fst, map_fst_PMain]
    exact law_zk hμ1
  have hWlaw : (PMain d N μN).map (fun ω : OmMain d N => ω.2.1) = PC d := by
    have : (fun ω : OmMain d N => ω.2.1) = Prod.fst ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map measurable_fst measurable_snd, map_snd_PMain]
    simp [Measure.map_fst_prod]
  exact map_overrideAt_eq_infinitePi (fun k => blockMeasure (cellLaw d k) (cellMass d k))
    (jcell_injective d N) hZ hW hind hZlaw hWlaw

/-- The law of the family `(X_m)_m`. -/
theorem map_Xfam (hμ2 : μN.map Prod.snd = Measure.pi fun _ : Fin N => gaussianReal 0 1) :
    (PMain d N μN).map (Xfam d N) = PX d := by
  have hZ : Measurable fun ω : OmMain d N => zdiff d N ω.1.1 :=
    measurable_zdiff.comp (measurable_fst.comp measurable_fst)
  have hW : Measurable fun ω : OmMain d N => ω.2.2 := measurable_snd.comp measurable_snd
  have hind : IndepFun (fun ω : OmMain d N => zdiff d N ω.1.1) (fun ω : OmMain d N => ω.2.2)
      (PMain d N μN) :=
    indepFun_prod (μ := (PA d N μN).prod (PBpts d N)) (ν := (PC d).prod (PX d))
      (X := fun p : SA d N × SB d N => zdiff d N p.1) (Y := fun p : SC d × SX d => p.2)
      (measurable_zdiff.comp measurable_fst) measurable_snd
  have hZlaw : (PMain d N μN).map (fun ω : OmMain d N => zdiff d N ω.1.1) =
      Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
    have : (fun ω : OmMain d N => zdiff d N ω.1.1) = zdiff d N ∘ (Prod.fst ∘ Prod.fst) := rfl
    rw [this, ← Measure.map_map measurable_zdiff (measurable_fst.comp measurable_fst),
      ← Measure.map_map measurable_fst measurable_fst, map_fst_PMain]
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
    exact law_zdiff hμ2
  have hWlaw : (PMain d N μN).map (fun ω : OmMain d N => ω.2.2) = PX d := by
    have : (fun ω : OmMain d N => ω.2.2) = Prod.snd ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map measurable_snd measurable_snd, map_snd_PMain]
    simp [Measure.map_snd_prod]
  exact map_overrideAt_eq_infinitePi
    (fun _ : ℕ => Measure.pi fun _ : Fin d => gaussianReal 0 1) Fin.val_injective hZ hW hind hZlaw
    hWlaw

end StrongApprox
end ElboimSly
