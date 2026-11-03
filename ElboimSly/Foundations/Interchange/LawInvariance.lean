/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.GoodAs
public import ElboimSly.Foundations.Interchange.SymmCov
public import ElboimSly.Foundations.Interchange.SymmG3
public import ElboimSly.Foundations.PPP.Invariance
public import Mathlib

/-!
# Invariance in law

Invariance in law.

The environment's law is invariant under lattice automorphisms, rotations and the reflection of the
circle (images and invariance on E×mathbbT_β). Combined with the covariance of trajectories
(covariance of trajectories) and configurations are a.s. good, this gives the invariance of the trajectory laws.

The only input that is not proved here is measurability: the measurability of
`ν ↦ γ^ν_{x,a}` on the configuration space. The trajectory statements therefore carry that
measurability as a hypothesis, and are named `*_of_measurable`. The laws of the configurations
themselves, and the law of `G(g_* N)` for every measurable `G`, are unconditional.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]
  {N : Ω → Measure (RingSpace d β)} {P : Measure Ω}

/-! ### The environment is preserved by the symmetries -/

theorem map_ringMapEquiv_lattice (g : LatticeAut d) :
    (ringIntensity d β).map (ringMapEquiv (edgeEquiv g) (MeasurableEquiv.refl (AddCircle β))) =
      ringIntensity d β := by
  have e : ⇑(ringMapEquiv (edgeEquiv g) (MeasurableEquiv.refl (AddCircle β))) =
      Prod.map (edgeEquiv g) (· + (0 : AddCircle β)) := by
    funext p; simp [ringMapEquiv_apply]; rfl
  rw [e]
  exact map_ringIntensity_translate d β (edgeEquiv g) 0

theorem map_ringMapEquiv_rotate (r : ℝ) :
    (ringIntensity d β).map (ringMapEquiv (Equiv.refl (Edge d))
      (MeasurableEquiv.addRight ((r : ℝ) : AddCircle β))) = ringIntensity d β :=
  map_ringIntensity_translate d β (Equiv.refl (Edge d)) _

theorem map_ringMapEquiv_reflect :
    (ringIntensity d β).map (ringMapEquiv (Equiv.refl (Edge d))
      (MeasurableEquiv.neg (AddCircle β))) = ringIntensity d β :=
  map_ringIntensity_neg d β (Equiv.refl (Edge d))

/-- `g_* N` is again a Poisson point process with intensity `μ_β`. -/
theorem isPoissonPointProcess_lattice (h : IsPoissonPointProcess N (ringIntensity d β) P)
    (g : LatticeAut d) :
    IsPoissonPointProcess (fun ω => latticeMeasure g (N ω)) (ringIntensity d β) P := by
  have := h.map_measure (MeasurableEquiv.measurable
    (ringMapEquiv (edgeEquiv g) (MeasurableEquiv.refl (AddCircle β))))
  rwa [map_ringMapEquiv_lattice] at this

/-- `(ρ_r)_* N` is again a Poisson point process with intensity `μ_β`. -/
theorem isPoissonPointProcess_rotate (h : IsPoissonPointProcess N (ringIntensity d β) P)
    (r : ℝ) :
    IsPoissonPointProcess (fun ω => rotateMeasure r (N ω)) (ringIntensity d β) P := by
  have := h.map_measure (MeasurableEquiv.measurable (ringMapEquiv (Equiv.refl (Edge d))
    (MeasurableEquiv.addRight ((r : ℝ) : AddCircle β))))
  rwa [map_ringMapEquiv_rotate] at this

/-- The law of the configuration is invariant under lattice automorphisms. -/
theorem law_latticeMeasure (h : IsPoissonPointProcess N (ringIntensity d β) P)
    (g : LatticeAut d) : P.map (fun ω => latticeMeasure g (N ω)) = P.map N :=
  h.map_measure_law_eq (MeasurableEquiv.measurable _) (map_ringMapEquiv_lattice g)

/-- The law of the configuration is invariant under rotations of the circle. -/
theorem law_rotateMeasure (h : IsPoissonPointProcess N (ringIntensity d β) P) (r : ℝ) :
    P.map (fun ω => rotateMeasure r (N ω)) = P.map N :=
  h.map_measure_law_eq (MeasurableEquiv.measurable _) (map_ringMapEquiv_rotate r)

/-- The law of the configuration is invariant under the reflection of the circle. -/
theorem law_reflectMeasure (h : IsPoissonPointProcess N (ringIntensity d β) P) :
    P.map (fun ω => reflectMeasure β (N ω)) = P.map N :=
  h.map_measure_law_eq (MeasurableEquiv.measurable _) map_ringMapEquiv_reflect

/-- Every measurable functional of the configuration has the same law under `g_*`. -/
theorem law_comp_latticeMeasure (h : IsPoissonPointProcess N (ringIntensity d β) P)
    (g : LatticeAut d) {T : Type*} [MeasurableSpace T] {G : Measure (RingSpace d β) → T}
    (hG : Measurable G) :
    P.map (fun ω => G (latticeMeasure g (N ω))) = P.map (fun ω => G (N ω)) :=
  h.map_comp_map_measure_law_eq (MeasurableEquiv.measurable _) (map_ringMapEquiv_lattice g) hG

/-- Every measurable functional of the configuration has the same law under `(ρ_r)_*`. -/
theorem law_comp_rotateMeasure (h : IsPoissonPointProcess N (ringIntensity d β) P) (r : ℝ)
    {T : Type*} [MeasurableSpace T] {G : Measure (RingSpace d β) → T} (hG : Measurable G) :
    P.map (fun ω => G (rotateMeasure r (N ω))) = P.map (fun ω => G (N ω)) :=
  h.map_comp_map_measure_law_eq (MeasurableEquiv.measurable _) (map_ringMapEquiv_rotate r) hG

/-! ### Trajectories as functions of the configuration -/

/-- The forward trajectory from `(x, a)` as a function of the configuration, extended by the
constant path `x` when the configuration is not good. -/
noncomputable def trajProc (ν : Measure (RingSpace d β)) (x : Fin d → ℤ) (a : ℝ) :
    ℝ≥0 → Fin d → ℤ :=
  open Classical in if h : Good ν then fwdTrajFn h x a else fun _ => x

theorem trajProc_of_good {ν : Measure (RingSpace d β)} (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) :
    trajProc ν x a = fwdTrajFn hν x a := by
  unfold trajProc
  simp [hν]

theorem trajProc_latticeMeasure {ν : Measure (RingSpace d β)} (hν : Good ν) (g : LatticeAut d)
    (x : Fin d → ℤ) (a : ℝ) :
    trajProc (latticeMeasure g ν) (g.toEquiv x) a = fun s => g.toEquiv (trajProc ν x a s) := by
  rw [trajProc_of_good (good_latticeMeasure g hν), trajProc_of_good hν,
    fwdTrajFn_latticeMeasure hν g x a]

theorem trajProc_rotateMeasure {ν : Measure (RingSpace d β)} (hν : Good ν) (r : ℝ)
    (x : Fin d → ℤ) (a : ℝ) :
    trajProc (rotateMeasure r ν) x (a + r) = trajProc ν x a := by
  rw [trajProc_of_good (good_rotateMeasure r hν), trajProc_of_good hν,
    fwdTrajFn_rotateMeasure hν r x a]

/-! ### Invariance in law -/

variable {ι : Type*}

/-- Invariance in law (spatial part): `Law(γ^N_{gx,a}) = Law(g ∘ γ^N_{x,a})`,
jointly for a family of trajectories. The measurability hypothesis is the content of
Measurability, which is not formalized here. -/
theorem law_trajProc_lattice_of_measurable (h : IsPoissonPointProcess N (ringIntensity d β) P)
    (g : LatticeAut d) (x : ι → Fin d → ℤ) (a : ι → ℝ)
    (hmeas : Measurable fun ν : Measure (RingSpace d β) =>
      fun k => trajProc ν (g.toEquiv (x k)) (a k)) :
    P.map (fun ω k => trajProc (N ω) (g.toEquiv (x k)) (a k)) =
      P.map (fun ω k s => g.toEquiv (trajProc (N ω) (x k) (a k) s)) := by
  have h1 := law_comp_latticeMeasure h g hmeas
  have h2 : (fun ω k => trajProc (latticeMeasure g (N ω)) (g.toEquiv (x k)) (a k)) =ᵐ[P]
      fun ω k s => g.toEquiv (trajProc (N ω) (x k) (a k) s) := by
    filter_upwards [ae_good h] with ω hω
    funext k
    exact trajProc_latticeMeasure hω g (x k) (a k)
  rw [← h1]
  exact Measure.map_congr h2

/-- Invariance in law (time part): the law of `γ^N_{x,a}(a + ·)` does not depend
on `a`, jointly for a family of trajectories translated by a common time shift `r`. The
measurability hypothesis is the content of measurability. -/
theorem law_trajProc_shift_of_measurable (h : IsPoissonPointProcess N (ringIntensity d β) P)
    (r : ℝ) (x : ι → Fin d → ℤ) (a : ι → ℝ)
    (hmeas : Measurable fun ν : Measure (RingSpace d β) =>
      fun k => trajProc ν (x k) (a k + r)) :
    P.map (fun ω k => trajProc (N ω) (x k) (a k + r)) =
      P.map (fun ω k => trajProc (N ω) (x k) (a k)) := by
  have h1 := law_comp_rotateMeasure h r hmeas
  have h2 : (fun ω k => trajProc (rotateMeasure r (N ω)) (x k) (a k + r)) =ᵐ[P]
      fun ω k => trajProc (N ω) (x k) (a k) := by
    filter_upwards [ae_good h] with ω hω
    funext k
    exact trajProc_rotateMeasure hω r (x k) (a k)
  rw [← h1]
  exact Measure.map_congr h2

end ElboimSly.Interchange
