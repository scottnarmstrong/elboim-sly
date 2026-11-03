/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.JumpShift
public import ElboimSly.Paper.Heavy.PiecesPath
public import ElboimSly.Foundations.Cyclic.CycFarDriven
public import ElboimSly.Foundations.Cyclic.CycRegenAe
public import ElboimSly.Foundations.SRW.WindowCount
public import Mathlib

/-!
# Jump counts of the canonical SRW

Supporting material for fast jumping is unlikely, Step 1 (supplement).

* `srwReal ν`: the canonical SRW path of the driver `ν`, as a path on `ℝ`.
* `isCyclicPath_srwReal`: it is a cyclic path.
* `jge_srw_le_winCount`: `JGE (srwReal ν) k 0 b → k ≤ M((0, b])`.
* `srw_jge_prob`: `P(JGE (srwReal (N₀ ω)) k 0 2) ≤ exp (4 d (e - 1) - k)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic ElboimSly.SRW

variable {d : ℕ}

/-- The canonical SRW path of the driver `ν`, as a path on `ℝ`. -/
noncomputable def srwReal (ν : Measure (Dir d × ℝ)) : ℝ → Fin d → ℤ :=
  fun s => walk d ν ((s.toNNReal : ℝ≥0) : ℝ)

theorem isCyclicPath_srwReal (ν : Measure (Dir d × ℝ)) : IsCyclicPath (srwReal ν) :=
  isCyclicPath_of_cycPath (drivingCycPath (walkPath_isDriving ν)) _
    (fun s _ => rfl) (by simp [srwReal, walk_zero])

theorem cycJumpCount_srwReal_le (ν : Measure (Dir d × ℝ)) (t : ℝ≥0) :
    cycJumpCount (srwReal ν) 0 t ≤ natOf (tot ν (Ioc 0 (t : ℝ))) := by
  refine le_trans ?_ (card_jumps_canonical_le ν t)
  unfold cycJumpCount
  refine Set.ncard_le_ncard_of_injOn (fun r : ℝ => r.toNNReal) (fun r hr => ?_) ?_
    ((walkPath_isRegPath (d := d) ν).fin t)
  · obtain ⟨⟨hr0, hr⟩, hr1, hr2⟩ := hr
    refine ⟨⟨Real.toNNReal_pos.2 hr1, fun hev => hr ?_⟩, ?_⟩
    · have := eventually_nhdsLT_toNNReal hr1 hev
      filter_upwards [this, Ioo_mem_nhdsLT hr1] with u hu hu0
      simpa [srwReal, hu0.1.le, hr1.le] using hu
    · show r.toNNReal ≤ t
      exact Real.toNNReal_le_iff_le_coe.2 hr2
  · intro r hr r' hr' h
    have h1 : 0 < r := hr.2.1
    have h2 : 0 < r' := hr'.2.1
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    simpa [Real.coe_toNNReal _ h1.le, Real.coe_toNNReal _ h2.le] using this

/-- `JGE (srwReal ν) k 0 2` forces `k ≤ M((0, 2])`. -/
theorem jge_srw_le_natOf (ν : Measure (Dir d × ℝ)) {k : ℕ} (h : JGE (srwReal ν) k 0 2) :
    k ≤ natOf (tot ν (Ioc 0 2)) := by
  have h1 := ((jGE_iff (isCyclicPath_srwReal ν) le_rfl (by norm_num) k).1 h)
  have h2 := cycJumpCount_srwReal_le ν 2
  simpa using h1.trans h2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N₀ : Ω → Measure (Dir d × ℝ)}

/-- `P(JGE (srwReal (N₀ ω)) k 0 2) ≤ exp (4 d (e - 1) - k)`. -/
theorem srw_jge_prob (hN₀ : IsPoissonPointProcess N₀ (clockIntensity (Dir d)) P) (k : ℕ) :
    P.real {ω | JGE (srwReal (N₀ ω)) k 0 2} ≤
      Real.exp (4 * d * (Real.exp 1 - 1) - k) := by
  have hmono : P.real {ω | JGE (srwReal (N₀ ω)) k 0 2} ≤
      P.real {ω | (k : ℝ) ≤ (winCount N₀ 0 2 ω : ℝ)} := by
    have := hN₀.isProbabilityMeasure
    refine measureReal_mono (fun ω hω => ?_)
    exact_mod_cast jge_srw_le_natOf _ hω
  refine hmono.trans ((winCount_tail hN₀ le_rfl (by norm_num) k).trans (le_of_eq ?_))
  congr 1; ring

end ElboimSly.Paper.Heavy
