/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.H5Cov
public import ElboimSly.Foundations.Cyclic.CycWalkTraj
public import Mathlib

/-!
# The shifted environment `N*` of Lemma 7.8

Discovered bad blocks for two walks (ES22 §7), "`W^{N*}_{0,0} = W₂ - u`".

Covariance of the backward trajectories under lattice automorphisms and rotations, and the
two-sided identity `W^{N*}_{0,0}(s) = W^N_{u,q}(s) - u` for all `s ∈ ℝ`, where
`N* = stepShiftEnv u (-q) N`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Interchange ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- Lattice covariance of backward trajectories. -/
theorem bwdTrajFn_latticeMeasure (hν : Good ν) (g : LatticeAut d) (y : Fin d → ℤ) (b : ℝ) :
    bwdTrajFn (good_latticeMeasure g hν) (g.toEquiv y) b =
      fun s => g.toEquiv (bwdTrajFn hν y b s) := by
  symm
  have hη := (bwdTrajFn_spec hν y b).1
  refine bwdTrajFn_eq (good_latticeMeasure g hν) ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro s
    filter_upwards [hη.1 s] with u hu
    simp [hu]
  · intro s
    obtain ⟨z, hz⟩ := hη.2.1 s
    exact ⟨g.toEquiv z, hz.mono fun u hu => by simp [hu]⟩
  · intro T
    refine (hη.2.2.1 T).subset ?_
    rintro s ⟨hsT, z, hz, hne⟩
    obtain ⟨z0, hz0⟩ := hη.2.1 s
    have hz0' : IsRightLimit (fun s => g.toEquiv (bwdTrajFn hν y b s)) s (g.toEquiv z0) :=
      hz0.mono fun u hu => by simp [hu]
    have hzz : z = g.toEquiv z0 := IsRightLimit.unique hz hz0'
    refine ⟨hsT, z0, hz0, fun h => hne ?_⟩
    rw [hzz, h]
  · intro s z hz
    obtain ⟨z0, hz0⟩ := hη.2.1 s
    have hz0' : IsRightLimit (fun s => g.toEquiv (bwdTrajFn hν y b s)) s (g.toEquiv z0) :=
      hz0.mono fun u hu => by simp [hu]
    rw [IsRightLimit.unique hz hz0']
    exact swapRule_latticeMeasure g (hη.2.2.2 s z0 hz0)
  · simp [(bwdTrajFn_spec hν y b).2]

/-- Rotation covariance of backward trajectories. -/
theorem bwdTrajFn_rotateMeasure (hν : Good ν) (r : ℝ) (y : Fin d → ℤ) (b : ℝ) :
    bwdTrajFn (good_rotateMeasure r hν) y (b + r) = bwdTrajFn hν y b := by
  symm
  have hη := (bwdTrajFn_spec hν y b).1
  refine bwdTrajFn_eq (good_rotateMeasure r hν) ⟨⟨hη.1, hη.2.1, hη.2.2.1, ?_⟩,
    (bwdTrajFn_spec hν y b).2⟩
  intro s z hz
  rw [swapRule_rotateMeasure_iff, show b + r - (s : ℝ) - r = b - s by ring]
  exact hη.2.2.2 s z hz

/-- `W^{N*}_{0,0}(s) = W^N_{u,q}(s) - u` for all real `s`, where `N* = stepShiftEnv u (-q) N`. -/
theorem cycWalk_stepShiftEnv_all (hν : Good ν) (u : Fin d → ℤ) (q : ℝ) (s : ℝ) :
    cycWalk (stepShiftEnv u (-q) ν) 0 0 s = cycWalk ν u q s - u := by
  rcases le_or_gt 0 s with hs | hs
  · have := cycWalk_stepShiftEnv hν u u (-q) q hs
    rw [sub_self, add_neg_cancel] at this
    exact this
  · have hg := good_latticeMeasure (LatticeAut.translate (-u)) hν
    have e : (LatticeAut.translate (-u)).toEquiv u = 0 := by
      simp [LatticeAut.translate]
    have hz : (0 : Fin d → ℤ) = (LatticeAut.translate (-u)).toEquiv u := e.symm
    rw [cycWalk_of_nonpos (good_stepShiftEnv hν u (-q)) _ _ hs.le, cycWalk_of_nonpos hν _ _ hs.le]
    unfold bwdTraj bwdReal
    have h1 : bwdTrajFn (good_stepShiftEnv hν u (-q)) 0 0 = bwdTrajFn hg 0 q := by
      have := bwdTrajFn_rotateMeasure hg (-q) 0 q
      rw [add_neg_cancel] at this
      exact this
    have h2 := bwdTrajFn_latticeMeasure hν (LatticeAut.translate (-u)) u q
    rw [e] at h2
    rw [h1, h2]
    simp only [zero_add, zero_sub, sub_add_cancel_left]
    simp [LatticeAut.translate, sub_eq_add_neg]

end ElboimSly.Paper.Step

end
