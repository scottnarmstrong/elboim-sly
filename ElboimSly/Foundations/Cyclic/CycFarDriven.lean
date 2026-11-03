/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFarRegen
public import ElboimSly.Foundations.Cyclic.DrivenCf
public import ElboimSly.Foundations.SRW.WindowCount
public import ElboimSly.Foundations.SRW.Jumps
public import Mathlib

/-!
# ES22 Lemma 2.2, Steps 1-4 for the driven regenerated walk

ES22 Lemma 2.2, Steps 1-4 in construction (iii). For the canonical SRW `X` of a Poisson
point process, almost surely `‖W^X_reg(s)‖ ≤ 2 · M((0, t])` for all `s ≤ t`, where `M((0,t])` is
the number of points of the driver in `(0, t]` (`winCount`, a `Poi(2dt)` variable).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {d : ℕ}

/-- The number of jumps of the walk of `ν` in `(0, t]` is at most `M((0, t])`. -/
theorem card_jumps_canonical_le (ν : Measure (Dir d × ℝ)) (t : ℝ≥0) :
    (CDisc (fun u : ℝ≥0 => walk d ν (u : ℝ)) ∩ Iic t).ncard ≤ natOf (tot ν (Ioc 0 (t : ℝ))) := by
  obtain ⟨hfin, hcard⟩ := jumps_finite_card (ν := ν) (t : ℝ)
  refine le_trans (Set.ncard_le_ncard_of_injOn (fun u : ℝ≥0 => (u : ℝ)) (fun u hu => ?_)
    (fun u _ v _ h => NNReal.coe_injective h) hfin) hcard
  exact ⟨⟨by exact_mod_cast hu.1.1, by exact_mod_cast hu.2⟩, isJump_of_mem_CDisc ν hu.1⟩

/-- Pathwise: for a coincidence-free canonical path, `‖W^x_reg(s)‖ ≤ 2 M((0, t])` for `s ≤ t`. -/
theorem norm_drivenRegenFrom_le {b : ℝ≥0} (hb : 0 < b) {ν : Measure (Dir d × ℝ)}
    (hx : (fun u : ℝ≥0 => walk d ν (u : ℝ)) ∈ CycCF b) {s t : ℝ≥0} (hst : s ≤ t) :
    ‖drivenRegenFrom b (fun u : ℝ≥0 => walk d ν (u : ℝ)) s‖ ≤
      2 * (natOf (tot ν (Ioc 0 (t : ℝ))) : ℝ) := by
  set x := fun u : ℝ≥0 => walk d ν (u : ℝ) with hxdef
  have h1 := l1n_drivenRegenFrom_le hb hx s
  have h2 : (CDisc x ∩ Iic s).ncard ≤ (CDisc x ∩ Iic t).ncard :=
    Set.ncard_le_ncard (inter_subset_inter_right _ (Iic_subset_Iic.2 hst)) (hx.1.fin t)
  have h3 : (CDisc x ∩ Iic t).ncard ≤ natOf (tot ν (Ioc 0 (t : ℝ))) := card_jumps_canonical_le ν t
  have h4 : l1n (drivenRegenFrom b x s) ≤ 2 * natOf (tot ν (Ioc 0 (t : ℝ))) := by omega
  calc ‖drivenRegenFrom b x s‖ ≤ l1 (drivenRegenFrom b x s) := norm_le_l1 _
    _ = (l1n (drivenRegenFrom b x s) : ℝ) := by rw [l1_eq_natAbs]; rfl
    _ ≤ ((2 * natOf (tot ν (Ioc 0 (t : ℝ))) : ℕ) : ℝ) := by exact_mod_cast h4
    _ = 2 * (natOf (tot ν (Ioc 0 (t : ℝ))) : ℝ) := by push_cast; ring

end ElboimSly.Cyclic

end
