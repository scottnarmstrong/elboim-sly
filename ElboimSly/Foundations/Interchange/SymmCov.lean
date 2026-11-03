/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.SymmG3
public import ElboimSly.Foundations.Interchange.TrajApi
import Mathlib

/-!
# Covariance of trajectories, lattice and time rotations

Covariance of trajectories(a), (b).

For a good configuration `ν`:
* `γ^{g_*ν}_{gx,a} = g ∘ γ^ν_{x,a}` for a lattice automorphism `g`;
* `γ^{(ρ_r)_*ν}_{x,a+r}(t+r) = γ^ν_{x,a}(t)` for a rotation `ρ_r`.

Trajectories are the half-line paths of `TrajApi`; the conclusions are about `fwdTrajFn`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

omit [Fact (0 < β)] in
theorem swapRule_latticeMeasure (g : LatticeAut d) {t : ℝ} {z w : Fin d → ℤ}
    (h : SwapRule ν t z w) :
    SwapRule (latticeMeasure g ν) t (g.toEquiv z) (g.toEquiv w) := by
  refine ⟨fun e' he' hr' => ?_, fun hn => ?_⟩
  · obtain ⟨e, rfl⟩ := (edgeEquiv g).surjective e'
    have hme : e.Mem z := (edgeEquiv_mem g e z).mp he'
    have hre : Rings ν e t := (rings_latticeMeasure g ν e t).mp hr'
    rw [edgeEquiv_val, h.1 e hme hre]
    rfl
  · have : ¬ ∃ e : Edge d, e.Mem z ∧ Rings ν e t := by
      rintro ⟨e, he, hr⟩
      exact hn ⟨edgeEquiv g e, (edgeEquiv_mem g e z).mpr he,
        (rings_latticeMeasure g ν e t).mpr hr⟩
    rw [h.2 this]

omit [Fact (0 < β)] in
theorem swapRule_rotateMeasure_iff (r : ℝ) {t : ℝ} {z w : Fin d → ℤ} :
    SwapRule (rotateMeasure r ν) t z w ↔ SwapRule ν (t - r) z w := by
  unfold SwapRule
  simp only [rings_rotateMeasure]

omit [Fact (0 < β)] in
theorem swapRule_reflectMeasure_iff {t : ℝ} {z w : Fin d → ℤ} :
    SwapRule (reflectMeasure β ν) t z w ↔ SwapRule ν (-t) z w := by
  unfold SwapRule
  simp only [rings_reflectMeasure]

/-- Covariance under lattice automorphisms. Covariance of trajectories(a). -/
theorem fwdTrajFn_latticeMeasure (hν : Good ν) (g : LatticeAut d) (x : Fin d → ℤ) (a : ℝ) :
    fwdTrajFn (good_latticeMeasure g hν) (g.toEquiv x) a =
      fun s => g.toEquiv (fwdTrajFn hν x a s) := by
  symm
  refine fwdTrajFn_eq (good_latticeMeasure g hν) ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro s
    filter_upwards [(fwdTrajFn_spec hν x a).1.1 s] with u hu
    simp [hu]
  · intro s hs
    obtain ⟨z, hz⟩ := (fwdTrajFn_spec hν x a).1.2.1 s hs
    exact ⟨g.toEquiv z, hz.mono fun u hu => by simp [hu]⟩
  · intro T
    refine ((fwdTrajFn_spec hν x a).1.2.2.1 T).subset ?_
    rintro s ⟨hs, hsT, z, hz, hne⟩
    obtain ⟨z0, hz0⟩ := (fwdTrajFn_spec hν x a).1.2.1 s hs
    have hz0' : IsLeftLimit (fun s => g.toEquiv (fwdTrajFn hν x a s)) s (g.toEquiv z0) :=
      hz0.mono fun u hu => by simp [hu]
    have hzz : z = g.toEquiv z0 := IsLeftLimit.unique hs hz hz0'
    refine ⟨hs, hsT, z0, hz0, fun h => hne ?_⟩
    rw [hzz, h]
  · intro s hs z hz
    obtain ⟨z0, hz0⟩ := (fwdTrajFn_spec hν x a).1.2.1 s hs
    have hz0' : IsLeftLimit (fun s => g.toEquiv (fwdTrajFn hν x a s)) s (g.toEquiv z0) :=
      hz0.mono fun u hu => by simp [hu]
    rw [IsLeftLimit.unique hs hz hz0']
    exact swapRule_latticeMeasure g ((fwdTrajFn_spec hν x a).1.2.2.2 s hs z0 hz0)
  · simp [(fwdTrajFn_spec hν x a).2]

/-- Covariance under rotations of the circle. Covariance of trajectories(b). -/
theorem fwdTrajFn_rotateMeasure (hν : Good ν) (r : ℝ) (x : Fin d → ℤ) (a : ℝ) :
    fwdTrajFn (good_rotateMeasure r hν) x (a + r) = fwdTrajFn hν x a := by
  symm
  refine fwdTrajFn_eq (good_rotateMeasure r hν) ⟨⟨(fwdTrajFn_spec hν x a).1.1,
    (fwdTrajFn_spec hν x a).1.2.1, (fwdTrajFn_spec hν x a).1.2.2.1, ?_⟩,
    (fwdTrajFn_spec hν x a).2⟩
  intro s hs z hz
  rw [swapRule_rotateMeasure_iff, show a + r + (s : ℝ) - r = a + s by ring]
  exact (fwdTrajFn_spec hν x a).1.2.2.2 s hs z hz

/-- Real-time form of the rotation covariance:
`γ^{(ρ_r)_*ν}_{x,a+r}(t+r) = γ^ν_{x,a}(t)`. -/
theorem fwdTraj_rotateMeasure (hν : Good ν) (r : ℝ) (x : Fin d → ℤ) (a t : ℝ) :
    fwdTraj (good_rotateMeasure r hν) x (a + r) (t + r) = fwdTraj hν x a t := by
  unfold fwdTraj fwdReal
  rw [fwdTrajFn_rotateMeasure hν r x a, show t + r - (a + r) = t - a by ring]

/-- Real-time form of the lattice covariance. -/
theorem fwdTraj_latticeMeasure (hν : Good ν) (g : LatticeAut d) (x : Fin d → ℤ) (a t : ℝ) :
    fwdTraj (good_latticeMeasure g hν) (g.toEquiv x) a t = g.toEquiv (fwdTraj hν x a t) := by
  unfold fwdTraj fwdReal
  rw [fwdTrajFn_latticeMeasure hν g x a]

end ElboimSly.Interchange
