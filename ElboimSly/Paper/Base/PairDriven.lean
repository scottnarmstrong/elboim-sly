/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.PairRules
public import ElboimSly.Paper.Base.PairClock
public import ElboimSly.Paper.Base.TwoParticle
public import ElboimSly.Foundations.Cyclic.CycDrivenEvents
public import ElboimSly.Foundations.Cyclic.CycDrivenUnique
public import Mathlib

/-!
# The driven path of the first walk in cyclic walks within one lap

Cyclic walks within one lap (b), "Walk 1".

* `stepCPath`, `translateCPath`: the candidate paths as `CPath`s of length `∞`.
* `drivenPath_eq_of_rules`: a path satisfying the driven rules on `(0, L]` agrees with the driven
  path on `[0, L]` (this is `drv_eq_of_le`).
* `drivenPath_one`: with no earlier explored region, the driven path of a forward walk is `a + X`
  on `[0, L]`, `L < β`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base Function

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- A step path as a `CPath` of length `∞`. -/
noncomputable def stepCPath (y : ℝ≥0 → Fin d → ℤ) (hy : IsStepPath y) : CPath (Fin d → ℤ) :=
  ⟨⊤, y, hy.rc, hy.fin, fun _ _ h _ => absurd h (by simp)⟩

theorem stepCPath_left {y : ℝ≥0 → Fin d → ℤ} (hy : IsStepPath y) {r : ℝ≥0} (hr : 0 < r) :
    (stepCPath y hy).left r = leftLim y r :=
  (IsStepPath.leftLim_eq hr ((stepCPath y hy).eventually_left hr)).symm

theorem cpath_left_eq_leftLim (X : CPath (Fin d → ℤ)) {r : ℝ≥0} (hr : 0 < r) :
    X.left r = leftLim X.fn r :=
  (IsStepPath.leftLim_eq (f := X.fn) hr (X.eventually_left hr)).symm

theorem isStepPath_translate (a : Fin d → ℤ) (X : CPath (Fin d → ℤ)) :
    IsStepPath (fun t => a + X.fn t) := by
  refine ⟨fun s => ?_, fun T => (X.fin T).subset fun r ⟨hr, hrT⟩ => ⟨?_, hrT⟩⟩
  · filter_upwards [X.rc s] with u hu
    rw [hu]
  · refine ⟨hr.1, fun h => hr.2 ?_⟩
    filter_upwards [h] with u hu
    rw [hu]

/-- The path `a + X` as a `CPath` of length `∞`. -/
noncomputable def translateCPath (a : Fin d → ℤ) (X : CPath (Fin d → ℤ)) : CPath (Fin d → ℤ) :=
  stepCPath _ (isStepPath_translate a X)

theorem translateCPath_left (a : Fin d → ℤ) (X : CPath (Fin d → ℤ)) {r : ℝ≥0} (hr : 0 < r) :
    (translateCPath a X).left r = a + X.left r := by
  refine CPath.left_eq_of_eventually _ hr ?_
  filter_upwards [X.eventually_left hr] with u hu
  show a + X.fn u = _
  rw [hu]

/-- A path satisfying the driven rules on `(0, L]` agrees with the driven path on `[0, L]`. -/
theorem drivenPath_eq_of_rules {I : Type*} [MeasurableSpace I]
    {R Q : Set (I × RingSpace d β)} {δ : CycData I d} {X : CPath (Fin d → ℤ)} {a : ℝ≥0}
    (hXu : X.UnitJumps)
    (hQ : {θ : AddCircle β | ∃ e : Edge d, (δ.copy, (e, θ)) ∈ Q}.Finite)
    {L : ℝ≥0} (q : CPath (Fin d → ℤ)) (hq0 : q.fn 0 = δ.start)
    (hq : ∀ r, 0 < r → r ≤ L → DrvRule β R Q δ X a q r) :
    ∀ t ≤ L, (drivenPath β R Q δ X a).1.fn t = q.fn t := by
  have hp := drivenPath_spec (R := R) (a := a) hXu hQ
  exact drv_eq_of_le (by rw [hp.2.1, hq0]) (fun r hr _ => hp.2.2 r hr) hq

/-- The own history of a walk contains no element at the clock of a later time of the same window. -/
theorem notMem_own {δ : CycData Unit d} (hf : δ.fwd = true) {L : ℝ≥0} (hL : (L : ℝ) < β)
    {r : ℝ≥0} (hr : r ≤ L) (q : CPath (Fin d → ℤ)) (e : Edge d) :
    (((), (e, δ.clock β r)) : Unit × RingSpace d β) ∉ drvZown β δ q r ∧
      (((), (e, δ.clock β r)) : Unit × RingSpace d β) ∉ drvQown β δ q r := by
  constructor
  · rintro ⟨r', -, hr'r, -, hclk, -⟩
    have := (clock_eq_iff_of_lt hf hf rfl hL (hr'r.le.trans hr) hr).1 hclk.symm
    exact absurd this hr'r.ne
  · rintro ⟨r', -, hr'r, -, -, hclk, -⟩
    have := (clock_eq_iff_of_lt hf hf rfl hL (hr'r.le.trans hr) hr).1 hclk.symm
    exact absurd this hr'r.ne

/-- The driven rules hold for the translate `a + X` at a time `r ∈ (0, L]` at whose clock the
explored region and the known rings are empty. -/
theorem drvRule_translate {a : Fin d → ℤ} {ra : ℝ} {X : CPath (Fin d → ℤ)} {L : ℝ≥0}
    (hL : (L : ℝ) < β) (R Q : Set (Unit × RingSpace d β)) {r : ℝ≥0} (hr : 0 < r) (hrL : r ≤ L)
    (hR : ∀ e : Edge d, (((), (e, (CycData.clock β ((), a, ra, true) r))) :
      Unit × RingSpace d β) ∉ R)
    (hQ : ∀ e : Edge d, (((), (e, (CycData.clock β ((), a, ra, true) r))) :
      Unit × RingSpace d β) ∉ Q) :
    DrvRule β R Q ((), a, ra, true) X 0 (translateCPath a X) r := by
  have hf : CycData.fwd (((), a, ra, true) : CycData Unit d) = true := rfl
  unfold DrvRule
  refine ruleFn_none (fun e hq => ?_) (fun e hz => ?_) (fun hj => ?_) (fun hj => ?_)
  · rcases hq with h | h
    · exact hQ _ h
    · exact (notMem_own hf hL hrL (translateCPath a X) e).2 h
  · rcases hz with h | h
    · exact hR _ h
    · exact (notMem_own hf hL hrL (translateCPath a X) e).1 h
  · rw [translateCPath_left a X hr, zero_add]
    show a + X.fn r = _
    abel
  · rw [translateCPath_left a X hr]
    rw [zero_add] at hj
    have : X.fn r = X.left r := not_not.1 (fun h => hj (Ne.symm h))
    show a + X.fn r = _
    rw [this]

/-- **cyclic walks within one lap (b), walk 1**: with no earlier explored region the driven path is `a + X`
on `[0, L]`. -/
theorem drivenPath_one {a : Fin d → ℤ} {ra : ℝ} {X : CPath (Fin d → ℤ)} (hXu : X.UnitJumps)
    (hX0 : X.fn 0 = 0) {L : ℝ≥0} (hL : (L : ℝ) < β) (R Q : Set (Unit × RingSpace d β))
    (hR : ∀ e θ, (((), (e, θ)) : Unit × RingSpace d β) ∉ R)
    (hQ : ∀ e θ, (((), (e, θ)) : Unit × RingSpace d β) ∉ Q) :
    ∀ t ≤ L, (drivenPath β R Q ((), a, ra, true) X 0).1.fn t = a + X.fn t := by
  set δ : CycData Unit d := ((), a, ra, true) with hδ
  have hQf : {θ : AddCircle β | ∃ e : Edge d, (δ.copy, (e, θ)) ∈ Q}.Finite := by
    convert (finite_empty : (∅ : Set (AddCircle β)).Finite)
    ext θ
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists]
    exact fun e => hQ e θ
  refine drivenPath_eq_of_rules hXu hQf (translateCPath a X) (by simp [translateCPath, stepCPath,
    hX0, δ, CycData.start]) fun r hr hrL => ?_
  exact drvRule_translate hL R Q hr hrL (fun e => hR _ _) (fun e => hQ _ _)

end ElboimSly.Paper

end
