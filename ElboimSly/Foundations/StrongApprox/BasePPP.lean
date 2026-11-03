/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.BaseBM
public import Mathlib

/-!
# The Poisson point process of the base coupling

ES22 (8.3): base coupling with precision n^10 ("The walk": `N'` is a `PPP(μ_d)`), via
A Poisson point process from cell blocks on any probability space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

open SRW

variable {d N : ℕ} {μN : Measure ((Fin N → ℝ) × (Fin N → ℝ))} [IsProbabilityMeasure μN]

theorem measurable_Kc (k : CellIdx d) : Measurable fun ω : OmMain d N => Kc d N ω k :=
  (measurable_fst.comp ((measurable_pi_apply k).comp measurable_blocks))

theorem measurable_Yc (k : CellIdx d) (i : ℕ) : Measurable fun ω : OmMain d N => Yc d N ω k i :=
  (measurable_pi_apply i).comp (measurable_snd.comp ((measurable_pi_apply k).comp measurable_blocks))

/-- `N'` is a Poisson point process with intensity `μ_d` on the main space. -/
theorem base_ppp_main (hd : 1 ≤ d)
    (hμ1 : μN.map Prod.fst = Measure.pi fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ)) :
    IsPoissonPointProcess (Nproc d N) (clockIntensity (Dir d)) (PMain d N μN) := by
  have : Nonempty (Dir d) := ⟨(⟨0, hd⟩, true)⟩
  refine isPoissonPointProcess_cellProc (clockIntensity (Dir d)) (cellSet d)
    (measurableSet_cellSet d) (pairwise_disjoint_cellSet d) (iUnion_cellSet d) (cellLaw d)
    (cellMass d) (cell_restrict d) (PMain d N μN) (fun k ω => Kc d N ω k)
    (fun k i ω => Yc d N ω k i) measurable_Kc measurable_Yc ?_
  have : (fun (ω : OmMain d N) (k : CellIdx d) => (Kc d N ω k, fun i => Yc d N ω k i)) =
      blocks d N := rfl
  rw [this, map_blocks hμ1]
  rfl

/-- `N'` is a Poisson point process with intensity `μ_d` on the whole space. -/
theorem base_ppp (hd : 1 ≤ d)
    (hμ1 : μN.map Prod.fst = Measure.pi fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ)) :
    IsPoissonPointProcess (fun ω : OmBase d N => Nproc d N ω.1) (clockIntensity (Dir d))
      (PBase d N μN) := by
  refine (base_ppp_main hd hμ1).of_map_eq ((base_ppp_main hd hμ1).measurable.comp measurable_fst) ?_
  have : (fun ω : OmBase d N => Nproc d N ω.1) = Nproc d N ∘ Prod.fst := rfl
  rw [this, ← Measure.map_map (base_ppp_main hd hμ1).measurable measurable_fst, map_fst_PBase]

end StrongApprox
end ElboimSly
