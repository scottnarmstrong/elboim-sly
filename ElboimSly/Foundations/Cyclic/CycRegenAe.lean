/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenCut
public import ElboimSly.Foundations.Cyclic.DrivenCf
public import Mathlib

/-!
# The constructions of the regenerated walk (ii), (iii): the almost sure statements for canonical SRWs

The constructions of the regenerated walk (ii), (iii), with the driving paths the canonical SRWs built from
Poisson point processes (independent families). Every canonical path is a driving path
(`walkPath_isDriving`), hence a `CycPath` (`drivingCycPath`); almost surely it is coincidence-free
(`ae_canonical_mem_cycCF`), which is what `regRecWalk_drivenFinal_indep` and
`regRecWalk_drivenFinal_cut` need.

Not covered here: equality in law of the three constructions (needs several walks explored one after another)
and the ring-count claim (needs basic properties of world-lines (d)).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {d : ℕ}

/-- A driving path as an element of `CycPath d` (length `∞`). -/
noncomputable def drivingCycPath {x : ℝ≥0 → Fin d → ℤ} (hx : IsDrivingPath x) : CycPath d :=
  ⟨⟨⊤, x, hx.rc, hx.fin, fun s s' h _ => absurd h (by simp)⟩, fun s hs => by
    have hs0 : 0 < s := hs.1
    have := hx.unit s hs
    rw [CPath.left_eq_leftVal _ hs0]
    exact this⟩

/-- **the constructions of the regenerated walk (ii)**, almost surely, for independent canonical SRWs. -/
theorem ae_regRecWalk_indep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {β : ℝ}
    [Fact (0 < β)] {N : ℕ → Ω → Measure (Dir d × ℝ)}
    (hN : ∀ k, IsPoissonPointProcess (N k) (clockIntensity (Dir d)) P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      regRecWalk ((regPlan d β).drivenFinal (J := ℕ) (fun k _ => k)
        (fun k => drivingCycPath (walkPath_isDriving (N k ω)))) t =
        drivenRegenWalk β.toNNReal (fun k => canonical d (N k) ω) t := by
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  have h : ∀ᵐ ω ∂P, ∀ k, canonical d (N k) ω ∈ CycCF β.toNNReal :=
    ae_all_iff.2 fun k => ae_canonical_mem_cycCF (hN k) _ hb
  filter_upwards [h] with ω hω t
  exact regRecWalk_drivenFinal_indep _ hω t

/-- **the constructions of the regenerated walk (iii)**, almost surely, for one canonical SRW cut at the regeneration
times. -/
theorem ae_regRecWalk_cut {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {β : ℝ}
    [Fact (0 < β)] {N : Ω → Measure (Dir d × ℝ)}
    (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      regRecWalk ((regPlan d β).drivenFinal (J := Unit) (fun _ _ => ())
        (fun _ => drivingCycPath (walkPath_isDriving (N ω)))) t =
        drivenRegenWalkCut β.toNNReal (canonical d N ω) t := by
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  filter_upwards [ae_canonical_mem_cycCF hN _ hb] with ω hω t
  exact regRecWalk_drivenFinal_cut _ hω t

end ElboimSly.Cyclic

end
