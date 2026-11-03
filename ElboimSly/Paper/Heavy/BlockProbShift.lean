/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.GoodLocalLoc
public import ElboimSly.Foundations.Interchange.LawInvariance
public import ElboimSly.Foundations.Interchange.SymmCov
public import Mathlib

/-!
# Translation invariance of the walk laws

Invariance in law; Invariance on E×mathbbT_β, used in probability that a block is bad.

`shiftEnv u q ν` is the environment translated by `-u` in space and rotated by `-q` in time, so that
`W^{shiftEnv u q ν}_{0,0}(s) = W^ν_{u,q}(s) - u` for `s ≥ 0`.  For a Poisson point process `N` and
a measurable set `E` of configurations, `P(shiftEnv u q (N) ∈ E) = P(N ∈ E)`.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Translation of `ℤ^d` by `v` as a lattice automorphism. -/
def translateAut (d : ℕ) (v : Fin d → ℤ) : LatticeAut d where
  toEquiv := Equiv.addRight v
  adj u w := by simp [LatticeAdj]

/-- The environment translated by `-u` and rotated by `-q`. -/
noncomputable def shiftEnv (u : Fin d → ℤ) (q : ℝ) (ν : Measure (RingSpace d β)) :
    Measure (RingSpace d β) :=
  latticeMeasure (translateAut d (-u)) (rotateMeasure (-q) ν)

theorem good_shiftEnv {u : Fin d → ℤ} {q : ℝ} {ν : Measure (RingSpace d β)} (hν : Good ν) :
    Good (shiftEnv u q ν) :=
  good_latticeMeasure _ (good_rotateMeasure _ hν)

theorem cycWalk_shiftEnv {ν : Measure (RingSpace d β)} (hν : Good ν) (u : Fin d → ℤ) (q : ℝ)
    {s : ℝ} (hs : 0 ≤ s) : cycWalk (shiftEnv u q ν) 0 0 s = cycWalk ν u q s - u := by
  have hR := good_rotateMeasure (-q) hν
  rw [cycWalk_of_nonneg (good_shiftEnv (u := u) (q := q) hν) 0 0 hs, cycWalk_of_nonneg hν u q hs]
  have h0 : (0 : Fin d → ℤ) = (translateAut d (-u)).toEquiv u := by
    simp [translateAut]
  have e1 : fwdTraj (good_shiftEnv (u := u) (q := q) hν) 0 0 (0 + s) =
      fwdTraj (good_latticeMeasure (translateAut d (-u)) hR) ((translateAut d (-u)).toEquiv u) 0
        (0 + s) := by
    rw [← h0]; rfl
  rw [e1, fwdTraj_latticeMeasure hR]
  have e2 := fwdTraj_rotateMeasure hν (-q) u q (q + s)
  rw [show q + -q = 0 by ring, show q + s + -q = 0 + s by ring] at e2
  rw [e2]
  simp [translateAut, sub_eq_add_neg]

omit [Fact (0 < β)] in
theorem measurable_shiftEnv (u : Fin d → ℤ) (q : ℝ) :
    Measurable (shiftEnv (β := β) u q) := by
  unfold shiftEnv latticeMeasure rotateMeasure ringPush
  exact (measurable_map_measure (MeasurableEquiv.measurable _)).comp (measurable_map_measure (MeasurableEquiv.measurable _))

theorem prob_shiftEnv_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (RingSpace d β)} (hN : IsPoissonPointProcess N (ringIntensity d β) P)
    (u : Fin d → ℤ) (q : ℝ) {E : Set (Measure (RingSpace d β))} (hE : MeasurableSet E) :
    P {ω | shiftEnv u q (N ω) ∈ E} = P {ω | N ω ∈ E} := by
  have h1 := law_latticeMeasure (isPoissonPointProcess_rotate hN (-q)) (translateAut d (-u))
  have h2 := law_rotateMeasure hN (-q)
  have hm : Measurable fun ω => shiftEnv u q (N ω) := (measurable_shiftEnv u q).comp hN.measurable
  have e : P.map (fun ω => shiftEnv u q (N ω)) = P.map N := h1.trans h2
  have := congrArg (fun m : Measure (Measure (RingSpace d β)) => m E) e
  simp only [Measure.map_apply hm hE, Measure.map_apply hN.measurable hE] at this
  exact this

omit [Fact (0 < β)] in
theorem isRelaxedTimeWrt_sub_const {β : ℝ} {w : ℝ → Fin d → ℤ} (c : Fin d → ℤ) (a t : ℝ) :
    IsRelaxedTimeWrt β (fun s => w s - c) a t ↔ IsRelaxedTimeWrt β w a t := by
  have hv : visitedSet (fun s => w s - c) a t = (fun v => v - c) '' visitedSet w a t := by
    unfold visitedSet; rw [Set.image_image]
  have hinj : Function.Injective (fun v : Fin d → ℤ => v - c) := fun x y h => by simpa using h
  have hheavy : ∀ r : ℝ, IsHeavy (fun s => w s - c) a t (w t - c) r ↔ IsHeavy w a t (w t) r := by
    intro r
    unfold IsHeavy
    rw [hv]
    have : {v : Fin d → ℤ | ‖v - (w t - c)‖ ≤ r} ∩ (fun v => v - c) '' visitedSet w a t =
        (fun v => v - c) '' ({v : Fin d → ℤ | ‖v - w t‖ ≤ r} ∩ visitedSet w a t) := by
      rw [Set.image_inter hinj]
      congr 1
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · intro h; exact ⟨v + c, by rw [show v + c - w t = v - (w t - c) by abel]; exact h, by simp⟩
      · rintro ⟨x, hx, rfl⟩; simpa [sub_sub_sub_cancel_right] using hx
    rw [this, Set.ncard_image_of_injective _ hinj]
  unfold IsRelaxedTimeWrt
  simp only [hheavy, sub_sub_sub_cancel_right]

end ElboimSly.Paper.Heavy
