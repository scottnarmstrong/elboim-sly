/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.BaseSpace
public import Mathlib

/-!
# Laws on the base coupling space

ES22 (8.3): base coupling with precision n^10 ("The walk" and "The Brownian motion": the laws of the blocks
`(K_k, (Y_{k,i})_i)` and of the increments `(X_m)`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

open SRW

variable {d N : ℕ} {μN : Measure ((Fin N → ℝ) × (Fin N → ℝ))} [IsProbabilityMeasure μN]

theorem cellMass_jcell (a : JIdx d N) : cellMass d (jcell d N a) = 1 := by
  have : 1 ≤ (jcell d N a).2 := by simp [jcell]
  simp [cellMass, this]

/-- Marginal law of the counts: `Poisson(1)^{⊗(D×[N])}`. -/
theorem law_kapOf
    (hμ1 : μN.map Prod.fst = Measure.pi fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ)) :
    (PA d N μN).map (kapOf d N) = Measure.pi fun _ : JIdx d N => poissonMeasure 1 := by
  set g : ℝ → ℕ := fun x => ⌊max x 0⌋₊ with hg
  have hgm : Measurable g := Nat.measurable_floor.comp (measurable_id.max measurable_const)
  set f : (Fin N → ℝ) × (Fin N → ℝ) → Fin N → ℕ := fun x m => g (x.1 m) with hf
  have hfm : Measurable f := measurable_pi_iff.2 fun m =>
    hgm.comp ((measurable_pi_apply m).comp measurable_fst)
  have hlaw : μN.map f = Measure.pi fun _ : Fin N => poissonMeasure 1 := by
    have e : f = (fun (y : Fin N → ℝ) (m : Fin N) => g (y m)) ∘ Prod.fst := rfl
    have hm : Measurable fun (y : Fin N → ℝ) (m : Fin N) => g (y m) :=
      measurable_pi_iff.2 fun m => hgm.comp (measurable_pi_apply m)
    rw [e, ← Measure.map_map hm measurable_fst, hμ1]
    have := Measure.pi_map_pi (μ := fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ))
      (f := fun _ => g) (fun _ => hgm.aemeasurable)
    rw [this]
    congr 1
    funext _
    rw [Measure.map_map hgm Measurable.of_discrete]
    have : g ∘ (Nat.cast : ℕ → ℝ) = id := by
      funext n; simp [hg]
    rw [this, Measure.map_id]
  exact law_flatten μN hfm (poissonMeasure 1) hlaw

/-- Marginal law of the Brownian increments of the coupling: independent `N_d(0,I)`. -/
theorem law_zdiff (hμ2 : μN.map Prod.snd = Measure.pi fun _ : Fin N => gaussianReal 0 1) :
    (PA d N μN).map (zdiff d N) =
      Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
  have hflat : (PA d N μN).map (zOf d N) = Measure.pi fun _ : JIdx d N => gaussianReal 0 1 :=
    law_flatten μN (f := fun x => x.2) measurable_snd (gaussianReal 0 1) hμ2
  have e : zdiff d N = (fun (G : (Fin d × Bool) × Fin N → ℝ) (m : Fin N) (i : Fin d) =>
      (G ((i, true), m) - G ((i, false), m)) / √2) ∘ zOf d N := rfl
  have hm : Measurable fun (G : (Fin d × Bool) × Fin N → ℝ) (m : Fin N) (i : Fin d) =>
      (G ((i, true), m) - G ((i, false), m)) / √2 := by fun_prop
  have hz : Measurable (zOf d N) := measurable_pi_iff.2 fun p =>
    (measurable_pi_apply p.2).comp (measurable_snd.comp (measurable_pi_apply p.1))
  rw [e, ← Measure.map_map hm hz, hflat]
  exact law_pairDiff

/-- The law of the block seen by the cells of `𝒦_N`. -/
theorem law_zk
    (hμ1 : μN.map Prod.fst = Measure.pi fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ)) :
    ((PA d N μN).prod (PBpts d N)).map (zk d N) =
      Measure.pi fun a : JIdx d N => blockMeasure (cellLaw d (jcell d N a)) (cellMass d (jcell d N a)) := by
  set e := MeasurableEquiv.arrowProdEquivProdArrow ℕ (ℕ → Dir d × ℝ) (JIdx d N) with he
  have hz : zk d N = e.symm ∘ Prod.map (kapOf d N) id := by
    funext p a; rfl
  have hk : Measurable (Prod.map (kapOf d N) (id : SB d N → SB d N)) :=
    measurable_kapOf.prodMap measurable_id
  rw [hz, ← Measure.map_map e.symm.measurable hk, ← Measure.map_prod_map _ _ measurable_kapOf
    measurable_id, law_kapOf hμ1, Measure.map_id]
  have hmp := (measurePreserving_arrowProdEquivProdArrow ℕ (ℕ → Dir d × ℝ) (JIdx d N)
    (fun _ => poissonMeasure 1)
    (fun a => Measure.infinitePi fun _ : ℕ => cellLaw d (jcell d N a))).symm e
  unfold PBpts
  rw [hmp.map_eq]
  congr 1
  funext a
  unfold blockMeasure
  rw [cellMass_jcell]

end StrongApprox
end ElboimSly
