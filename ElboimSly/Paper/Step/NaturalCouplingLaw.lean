/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.NaturalCoupling
public import ElboimSly.Paper.Step.Windows
public import ElboimSly.Paper.Step.DrivenLaw
public import Mathlib

/-!
# Laws in the natural coupling

Laws in the natural coupling (b): the stopped walks `W_j = Z_j|_{[0, s_j]}` are
independent and `W_j` has the law of `W|_{[0, s_j]}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology ElboimSly.Cyclic ElboimSly.SRW
open scoped NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- A stopped driving path is a driving path. -/
theorem isDrivingPath_stopPath' {x : ℝ≥0 → Fin d → ℤ} (hx : IsDrivingPath x) (t : ℝ≥0) :
    IsDrivingPath (Cyclic.stopPath x t) where
  toIsRegPath := stopPath_isRegPath hx.toIsRegPath t
  zero := by simp [Cyclic.stopPath, hx.zero]
  unit s hs := by
    have hst : s ≤ t := by
      by_contra hlt
      rw [not_le] at hlt
      apply hs.2
      filter_upwards [Ioo_mem_nhdsLT hlt] with u hu
      simp only [Cyclic.stopPath, min_eq_right hu.1.le, min_eq_right hlt.le]
    have hcd : s ∈ CDisc x := (mem_CDisc_congr (fun u hu => by
      simp only [Cyclic.stopPath, min_eq_left (hu.trans hst)])).1 hs
    have h1 := hx.unit s hcd
    have hl : leftVal (Cyclic.stopPath x t) s = leftVal x s :=
      leftVal_congr (fun u hu => by simp only [Cyclic.stopPath, min_eq_left (hu.le.trans hst)])
    simpa [Cyclic.stopPath, hl, min_eq_left hst] using h1

/-- The window of a driving path is a driving path. -/
theorem isDrivingPath_stepWin {x : ℝ≥0 → Fin d → ℤ} (hx : IsDrivingPath x) (t s : ℝ≥0) :
    IsDrivingPath (stepWin t s x) :=
  isDrivingPath_stopPath' (isDrivingPath_shiftPath hx t) s

/-- The stopped regenerated walk of a path, `u ↦ W_reg^y(u ∧ s)`. -/
noncomputable def stepRegStopped (β : ℝ) (s : ℝ≥0) (y : ℝ≥0 → Fin d → ℤ) : ℝ≥0 → Fin d → ℤ :=
  fun u => stepReg β y (min u s)

/-- `W_j = Z_j|_{[0, s_j]}`, as a path stopped at `s_j`. -/
noncomputable def stepWj (β : ℝ) (a : ℝ≥0) (s : ℕ → ℝ≥0) (Y : ℝ≥0 → Fin d → ℤ) (j : ℕ) :
    ℝ≥0 → Fin d → ℤ :=
  fun u => stepWalkZ β a s Y j (min u (s j))

theorem stepPartial_succ (s : ℕ → ℝ≥0) (j : ℕ) :
    stepPartial s (j + 1) = stepPartial s j + s j := by
  simp [stepPartial, Finset.sum_range_succ]

variable {β : ℝ} [Fact (0 < β)]

/-- By causality, `W_j` is the stopped regenerated walk driven by the `j`-th window. -/
theorem stepWj_eq {Y : ℝ≥0 → Fin d → ℤ} (hY : Y ∈ StepPath d) (a : ℝ≥0) (s : ℕ → ℝ≥0) (j : ℕ) :
    stepWj β a s Y j = stepRegStopped β (s j) (stepWin (a + stepPartial s j) (s j) Y) := by
  funext u
  have hx : IsDrivingPath (shiftPath Y (a + stepPartial s j)) :=
    isDrivingPath_shiftPath hY _
  have hy : IsDrivingPath (stepWin (a + stepPartial s j) (s j) Y) :=
    isDrivingPath_stepWin hY _ _
  have hxy : ∀ v ≤ s j, shiftPath Y (a + stepPartial s j) v =
      stepWin (a + stepPartial s j) (s j) Y v := by
    intro v hv
    simp only [stepWin, SRW.stopPath, SRW.theta, shiftPath, min_eq_left hv]
  simp only [stepWj, stepRegStopped, stepWalkZ, stepReg, stepShift]
  exact drivenRegenFrom_causal toNNReal_pos' hx hy hxy (min_le_right _ _)

theorem measurable_stepRegStopped (s : ℝ≥0) :
    Measurable fun y : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x} => stepRegStopped β s y.1 :=
  measurable_pi_iff.2 fun u => measurable_drivenRegenFrom_subtype toNNReal_pos' (min u s)

/-- Independence passes to the subtype lift. -/
theorem iIndepFun_subtype_lift {Ω ι β' : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [MeasurableSpace β'] {p : β' → Prop} (V : ι → Ω → β') (hV : ∀ i ω, p (V i ω))
    (h : iIndepFun V P) :
    iIndepFun (fun i ω => (⟨V i ω, hV i ω⟩ : Subtype p)) P := by
  rw [iIndepFun_iff_iIndep] at h ⊢
  convert h using 2 with i
  show MeasurableSpace.comap _ (MeasurableSpace.comap _ _) = _
  rw [MeasurableSpace.comap_comp]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}

/-- **Independence of the windows** (laws in the natural coupling (b)): `W_1, …, W_ℓ` are
independent. -/
theorem iIndepFun_stepWj (hY : IsSRW P Y) (hYp : ∀ ω, Y ω ∈ StepPath d) (a : ℝ≥0)
    (s : ℕ → ℝ≥0) : iIndepFun (fun j ω => stepWj β a s (Y ω) j) P := by
  have hind := iIndepFun_stepWin hY (fun j => a + stepPartial s j) s (fun j => by
    rw [stepPartial_succ, ← add_assoc])
  have hreg : ∀ j ω, IsRegPath (stepWin (a + stepPartial s j) (s j) (Y ω)) := fun j ω =>
    (isDrivingPath_stepWin (hYp ω) _ _).toIsRegPath
  have hlift := iIndepFun_subtype_lift (p := IsRegPath) _ hreg hind
  have hcomp := hlift.comp (fun j y => stepRegStopped β (s j) y.1) (fun j =>
    measurable_stepRegStopped (β := β) (s j))
  refine hcomp.congr fun j => ?_
  filter_upwards with ω
  exact (stepWj_eq (hYp ω) a s j).symm

/-- **Laws of the windows** (laws in the natural coupling (b)): `W_j` has the law of
`W|_{[0, s_j]}`, where `W = W_reg^{Y}`. -/
theorem map_stepWj (hY : IsSRW P Y) (hYp : ∀ ω, Y ω ∈ StepPath d) (a : ℝ≥0)
    (s : ℕ → ℝ≥0) (j : ℕ) :
    P.map (fun ω => stepWj β a s (Y ω) j) =
      P.map (fun ω => stepRegStopped β (s j) (Y ω)) := by
  have hreg : ∀ ω, IsRegPath (stepWin (a + stepPartial s j) (s j) (Y ω)) := fun ω =>
    (isDrivingPath_stepWin (hYp ω) _ _).toIsRegPath
  have hreg' : ∀ ω, IsRegPath (SRW.stopPath (s j) (Y ω)) := fun ω =>
    stopPath_isRegPath (hYp ω).toIsRegPath _
  have h1 := map_comp_of_regular (P := P) (P' := P)
    (Y := fun ω => stepWin (a + stepPartial s j) (s j) (Y ω))
    (Z := fun ω => SRW.stopPath (s j) (Y ω))
    ((measurable_stepWin _ _).comp hY.1) ((measurable_stopPath _).comp hY.1) hreg hreg'
    (map_stepWin hY _ _) (stepRegStopped β (s j)) (measurable_stepRegStopped (β := β) (s j))
  have e1 : (fun ω => stepWj β a s (Y ω) j) =
      fun ω => stepRegStopped β (s j) (stepWin (a + stepPartial s j) (s j) (Y ω)) :=
    funext fun ω => stepWj_eq (hYp ω) a s j
  have e2 : (fun ω => stepRegStopped β (s j) (SRW.stopPath (s j) (Y ω))) =
      fun ω => stepRegStopped β (s j) (Y ω) := by
    funext ω
    funext u
    simp only [stepRegStopped]
    exact (drivenRegenFrom_causal toNNReal_pos' (hYp ω) (isDrivingPath_stopPath' (hYp ω) (s j))
      (fun v hv => by simp [Cyclic.stopPath, min_eq_left hv]) (min_le_right _ _)).symm
  rw [e1]
  exact h1.trans (by rw [e2])

end ElboimSly.Paper
