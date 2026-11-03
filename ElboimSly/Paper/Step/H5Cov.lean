/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSrwShortLaw
public import ElboimSly.Foundations.Interchange.SymmCov
public import ElboimSly.Foundations.Interchange.SymmG3
public import ElboimSly.Foundations.Interchange.LawInvariance
public import ElboimSly.Foundations.Interchange.LatticeGroup
public import ElboimSly.Frozen.Defs.CycOmega
public import Mathlib

/-!
# Translation covariance of the cyclic walks

(H5) at level n (proof), covariance of trajectories, invariance in law,
Restriction, restart, periodicity (c).

For a configuration `ν`, a lattice vector `u₁` and a circle rotation `r`, put
`stepShiftEnv u₁ r ν := (ρ_r)_* (τ_{-u₁})_* ν`. For good `ν`:

* `cycWalk_stepShiftEnv`: `W^{shift ν}_{x - u₁, a + r}(s) = W^ν_{x,a}(s) - u₁` for `s ≥ 0`;
* `cycWalk_period`: `W_{x,a+β}(s) = W_{x,a}(s)` for `s ≥ 0`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Interchange ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The common shift `(e, θ) ↦ (e - u₁, θ + [r])` of the environment. -/
noncomputable def stepShiftEnv (u₁ : Fin d → ℤ) (r : ℝ) (ν : Measure (RingSpace d β)) :
    Measure (RingSpace d β) :=
  rotateMeasure r (latticeMeasure (LatticeAut.translate (-u₁)) ν)

theorem good_stepShiftEnv {ν : Measure (RingSpace d β)} (hν : Good ν) (u₁ : Fin d → ℤ) (r : ℝ) :
    Good (stepShiftEnv u₁ r ν) :=
  good_rotateMeasure r (good_latticeMeasure _ hν)

theorem isPoissonPointProcess_stepShiftEnv {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (RingSpace d β)} (h : IsPoissonPointProcess N (ringIntensity d β) P)
    (u₁ : Fin d → ℤ) (r : ℝ) :
    IsPoissonPointProcess (fun ω => stepShiftEnv u₁ r (N ω)) (ringIntensity d β) P :=
  isPoissonPointProcess_rotate (isPoissonPointProcess_lattice h _) r

theorem cycWalk_eq_fwdTrajFn {ν : Measure (RingSpace d β)} (hν : Good ν) (x : Fin d → ℤ) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) : cycWalk ν x a s = fwdTrajFn hν x a s.toNNReal := by
  have := cycWalk_eq_trajProc hν x a s.toNNReal
  rw [Real.coe_toNNReal _ hs] at this
  rw [this, trajProc_of_good hν]

theorem cycWalk_stepShiftEnv {ν : Measure (RingSpace d β)} (hν : Good ν) (u₁ x : Fin d → ℤ)
    (r a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    cycWalk (stepShiftEnv u₁ r ν) (x - u₁) (a + r) s = cycWalk ν x a s - u₁ := by
  have hl := good_latticeMeasure (LatticeAut.translate (-u₁)) hν
  rw [cycWalk_eq_fwdTrajFn (good_stepShiftEnv hν u₁ r) _ _ hs, cycWalk_eq_fwdTrajFn hν _ _ hs]
  unfold stepShiftEnv
  have h1 := fwdTrajFn_rotateMeasure hl r (x - u₁) a
  have h2 := fwdTrajFn_latticeMeasure hν (LatticeAut.translate (-u₁)) x a
  have e : (LatticeAut.translate (-u₁)).toEquiv x = x - u₁ := by
    simp [LatticeAut.translate, sub_eq_add_neg]
  rw [e] at h2
  rw [h1, h2]
  simp [LatticeAut.translate, sub_eq_add_neg]

omit [Fact (0 < β)] in
theorem rotateMeasure_period (ν : Measure (RingSpace d β)) : rotateMeasure β ν = ν := by
  unfold rotateMeasure ringPush
  have : (⇑(ringMapEquiv (Equiv.refl (Edge d))
      (MeasurableEquiv.addRight ((β : ℝ) : AddCircle β))) : RingSpace d β → RingSpace d β) = id := by
    funext p
    simp [ringMapEquiv_apply, AddCircle.coe_period]
  rw [this, Measure.map_id]

theorem cycWalk_period {ν : Measure (RingSpace d β)} (hν : Good ν) (x : Fin d → ℤ) (a : ℝ)
    {s : ℝ} (hs : 0 ≤ s) : cycWalk ν x (a + β) s = cycWalk ν x a s := by
  have hr := good_rotateMeasure β hν
  have h1 := fwdTrajFn_rotateMeasure hν β x a
  rw [cycWalk_eq_fwdTrajFn hν _ _ hs, cycWalk_eq_fwdTrajFn hν _ _ hs]
  have e := rotateMeasure_period ν
  have h2 : fwdTrajFn hν x (a + β) = fwdTrajFn hr x (a + β) := by
    congr 1; simp [e]
  rw [h2, h1]

end ElboimSly.Paper.Step

end
