/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycHitShift
public import Mathlib

/-!
# ES22 Lemma 2.1, Step 1: covariance and invariance of the recentring

ES22 Lemma 2.1, Step 1 (via covariance of trajectories (a), (b)).

* `map_hitPhi_eq`: `(φ_{(x,a)})_* ν = g_* (ρ_{-a})_* ν` with `g = translate (-x)`;
* `good_map_hitPhi`, `cycWalk_map_hitPhi`: `W^{(φ_{(x,a)})_* ν}_{0,0}(s) = W^ν_{x,a}(s) - x`;
* `law_hitShift`: `Law((φ_z)_* τ(N)) = Law(N)` for a PPP `N`.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem map_hitPhi_eq (ν : Measure (RingSpace d β)) (x : Fin d → ℤ) (a : ℝ) :
    ν.map (hitPhi x a) = latticeMeasure (LatticeAut.translate (-x)) (rotateMeasure (-a) ν) := by
  unfold latticeMeasure rotateMeasure ringPush
  have hm1 : Measurable (ringMapEquiv (Equiv.refl (Edge d))
      (MeasurableEquiv.addRight (((-a : ℝ)) : AddCircle β))) := MeasurableEquiv.measurable _
  have hm2 : Measurable (ringMapEquiv (edgeEquiv (LatticeAut.translate (-x)))
      (MeasurableEquiv.refl (AddCircle β))) := MeasurableEquiv.measurable _
  rw [Measure.map_map hm2 hm1]
  congr 1
  funext y
  unfold hitPhi
  simp [ringMapEquiv_apply]
  rfl

theorem good_map_hitPhi {ν : Measure (RingSpace d β)} (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) :
    Good (ν.map (hitPhi x a)) := by
  rw [map_hitPhi_eq]
  exact good_latticeMeasure _ (good_rotateMeasure _ hν)

theorem cycWalk_map_hitPhi {ν : Measure (RingSpace d β)} (hν : Good ν) (x : Fin d → ℤ) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    ElboimSly.cycWalk (ν.map (hitPhi x a)) 0 0 s = ElboimSly.cycWalk ν x a s - x := by
  have hrot := good_rotateMeasure (-a) hν
  have hmap : Good (ν.map (hitPhi x a)) := good_map_hitPhi hν x a
  rw [cycWalk_of_nonneg hmap 0 0 hs, cycWalk_of_nonneg hν x a hs]
  have key : ∀ (ν' : Measure (RingSpace d β)),
      ν' = latticeMeasure (LatticeAut.translate (-x)) (rotateMeasure (-a) ν) → ∀ hν' : Good ν',
      fwdTraj hν' 0 0 (0 + s) = fwdTraj hν x a (a + s) - x := by
    intro ν' h hν'
    subst h
    have e2 := fwdTraj_latticeMeasure hrot (LatticeAut.translate (-x)) x 0 (0 + s)
    have e3 := fwdTraj_rotateMeasure hν (-a) x a (a + s)
    have h0 : (LatticeAut.translate (-x)).toEquiv x = 0 := by simp [LatticeAut.translate]
    rw [h0] at e2
    rw [show a + -a = 0 by ring, show a + s + -a = 0 + s by ring] at e3
    rw [e2, e3]
    simp [LatticeAut.translate, sub_eq_add_neg]
  exact key _ (map_hitPhi_eq ν x a) hmap

theorem law_hitShift {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N : Ω → Measure (RingSpace d β)} (hN : IsPoissonPointProcess N (ringIntensity d β) Pr)
    (z : (Fin d → ℤ) × ℝ) : Pr.map (fun ω => hitShift z (N ω)) = Pr.map N := by
  have h1 := hN.map_measure_law_eq (measurable_hitPhi_at z.1 z.2) (map_hitPhi z.1 z.2)
  have h2 : (fun ω => hitShift z (N ω)) =ᵐ[Pr] fun ω => (N ω).map (hitPhi z.1 z.2) := by
    filter_upwards [hN.tau_comp_ae_eq] with ω hω
    unfold hitShift
    rw [hω]
  rw [Measure.map_congr h2]
  exact h1

end ElboimSly.Cyclic

end
