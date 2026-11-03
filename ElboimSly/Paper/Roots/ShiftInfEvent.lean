/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Ergodic.ZeroOne
public import ElboimSly.Foundations.Interchange.LatticeGroup
public import ElboimSly.Foundations.Interchange.SymmCov
public import ElboimSly.Foundations.Cyclic.CycEvents
public import ElboimSly.Frozen.Defs.InfEvent
public import ElboimSly.Frozen.Defs.FinZeroEvent
import Mathlib

/-!
# Translation invariance and measurability of the frozen event `Inf`

R2: Theorem 1 (proof), via covariance of trajectories, symmetries preserve good configurations, properties of translations and local σ-algebras(b).

These are the ingredients of `root_R2_of_R1` about the frozen events `ElboimSly.infEvent` and
`ElboimSly.finZeroEvent`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ElboimSly.Roots

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
/-- `ϑ_z` is the pushforward by the lattice translation by `z`. -/
theorem thetaShift_eq_latticeMeasure (z : Fin d → ℤ) (ν : Measure (RingSpace d β)) :
    thetaShift d β z ν = Interchange.latticeMeasure (Interchange.LatticeAut.translate z) ν := by
  unfold thetaShift Interchange.latticeMeasure Interchange.ringPush
  congr 1

/-- Translations map `Inf` into `Inf`. R2: Theorem 1 (invariance step). -/
theorem thetaShift_image_infEvent_subset (z : Fin d → ℤ) :
    thetaShift d β z '' infEvent d β ⊆ infEvent d β := by
  rintro _ ⟨ν, ⟨hν, x, hx⟩, rfl⟩
  rw [thetaShift_eq_latticeMeasure]
  set g := Interchange.LatticeAut.translate z
  refine ⟨Interchange.good_latticeMeasure g hν, g.toEquiv x, fun k hk => ?_⟩
  have key : ∀ k : ℕ, ∀ y, (interchangePi (Interchange.latticeMeasure g ν) β.toNNReal)^[k]
      (g.toEquiv y) = g.toEquiv ((interchangePi ν β.toNNReal)^[k] y) := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Interchange.interchangePi_eq (Interchange.good_latticeMeasure g hν),
        Interchange.interchangePi_eq hν, Interchange.fwdTraj_latticeMeasure hν g, ih]
  rw [key]
  exact fun h => hx k hk (g.toEquiv.injective h)

theorem isShiftInvariant_infEvent : IsShiftInvariant d β (infEvent d β) :=
  (isShiftInvariant_iff _).2 thetaShift_image_infEvent_subset

theorem measurableSet_infEvent : MeasurableSet (infEvent d β) :=
  Cyclic.measurableSet_infEvent

theorem measurableSet_finZeroEvent : MeasurableSet (finZeroEvent d β) :=
  Cyclic.measurableSet_finZeroEvent

/-- On good configurations, not being in `Inf` forces membership in `Fin₀`. -/
theorem mem_finZeroEvent_of_good_not_mem_infEvent {ν : Measure (RingSpace d β)}
    (hν : Good ν) (h : ν ∉ infEvent d β) : ν ∈ finZeroEvent d β := by
  refine ⟨hν, ?_⟩
  by_contra hc
  exact h ⟨hν, 0, fun k hk h0 => hc ⟨k, hk, h0⟩⟩

end ElboimSly.Roots

end
