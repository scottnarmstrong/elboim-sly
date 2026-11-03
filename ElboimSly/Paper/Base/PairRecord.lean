/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.PairDriven2
public import ElboimSly.Paper.Base.PairPlan
public import ElboimSly.Foundations.Cyclic.CycDrivenLawFirst
public import ElboimSly.Foundations.Cyclic.CycDrivenRegion
public import ElboimSly.Foundations.Cyclic.CycRegenEnv
public import Mathlib

/-!
# The final records of the plan `𝔭` of cyclic walks within one lap

Cyclic walks within one lap (b), (c), "Environment record" and "Driven record".

For the plan `pairPlan d β a b ra rb L` with `L < β`:

* `pairPlan_coord`: the two coordinates of any final record are the ideal entries.
* `envFinal_coord_fn`: the environment record consists of the stopped cyclic walks
  `W^ν_{a,ra}(· ∧ L)` and `W^ν_{b,rb}(· ∧ L)` of the slice.
* `drivenFinal_coord_zero`, `drivenFinal_coord_one`, `drivenFinal_coord_one_far`: the driven
  record consists of `a + X₁` and of the two-particle path (respectively `b + X₂`) stopped at `L`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base Function

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem cut_fn_coe {V : Type*} (p : CPath V) (L s : ℝ≥0) :
    (p.cut (L : ℝ≥0∞)).fn s = p.fn (min s L) := by
  rw [CPath.cut_fn]
  congr 1

section coord

variable (a b : Fin d → ℤ) (ra rb : ℝ) (L : ℝ≥0)

omit [Fact (0 < β)] in
theorem pairPlan_E_len (path : PathRule Unit d) (k : ℕ) :
    ((pairPlan d β a b ra rb L).E path k).len = L := by
  unfold CycPlan.E CycPlan.nextEntry
  simp only [CycEntry.len, CycPath.cut]
  rw [pairPlan_stopLen]
  exact CPath.cut_len _ _

omit [Fact (0 < β)] in
theorem pairPlan_coord (path : PathRule Unit d) (junk : CycEntry Unit d) {k : ℕ} (hk : k < 2) :
    ((pairPlan d β a b ra rb L).cycFinal path).coord junk k =
      (pairPlan d β a b ra rb L).E path k := by
  have h := CycPlan.cycFinal_nth_gen (pairPlan d β a b ra rb L) path k
  have hc : (pairPlan d β a b ra rb L).Cont path k := by
    refine ⟨?_, fun i _ => ?_⟩
    · show (k : ℕ∞) < 2
      exact_mod_cast hk
    · rw [pairPlan_E_len]; exact ENNReal.coe_lt_top
  simp only [hc, ↓reduceIte] at h
  simp [CycRec.coord, h]

omit [Fact (0 < β)] in
theorem pairPlan_E_fn (path : PathRule Unit d) (k : ℕ) (s : ℝ≥0) :
    ((pairPlan d β a b ra rb L).E path k).path.fn s =
      (path k ((pairPlan d β a b ra rb L).ideal path k)).1.fn (min s L) := by
  unfold CycPlan.E CycPlan.nextEntry
  simp only [CycEntry.path, CycPath.cut]
  rw [pairPlan_stopLen]
  exact cut_fn_coe _ _ _

omit [Fact (0 < β)] in
theorem pairPlan_E_data (path : PathRule Unit d) (k : ℕ) :
    ((pairPlan d β a b ra rb L).E path k).data =
      (pairPlan d β a b ra rb L).start k ((pairPlan d β a b ra rb L).ideal path k) := rfl

end coord

section env

variable (a b : Fin d → ℤ) (ra rb : ℝ) (L : ℝ≥0)

omit [Fact (0 < β)] in
theorem envFn_fwd (ν : Measure (Unit × RingSpace d β)) (δ : CycData Unit d)
    (hf : δ.fwd = true) (s : ℝ≥0) :
    envFn ν δ s = ElboimSly.cycWalk (cycSlice () ν) δ.start δ.phase (s : ℝ) := by
  unfold envFn ElboimSly.cycWalk
  have h0 : (0 : ℝ) ≤ s := s.2
  simp only [h0, ↓reduceIte]
  rw [Real.toNNReal_coe]
  simp [envMeasure, hf, CycData.copy, CycData.sgn]

/-- The environment record, walk 1: the stopped cyclic walk `W^ν_{a, ra}(· ∧ L)`. -/
theorem envFinal_coord_zero {ν : Measure (Unit × RingSpace d β)} (hν : CycGood ν)
    (junk : CycEntry Unit d) (s : ℝ≥0) :
    (((pairPlan d β a b ra rb L).envFinal ν).coord junk 0).path.fn s =
      ElboimSly.cycWalk (cycSlice () ν) a ra ((min s L : ℝ≥0) : ℝ) := by
  unfold CycPlan.envFinal
  rw [pairPlan_coord a b ra rb L _ junk (by norm_num), pairPlan_E_fn]
  have := (envPath_len (δ := (pairPlan d β a b ra rb L).start 0 ((pairPlan d β a b ra rb L).ideal
    (fun k ρ => envPath ν ((pairPlan d β a b ra rb L).start k ρ)) 0)) (hν ())).2
  show (envPath ν _).1.fn _ = _
  rw [this]
  exact envFn_fwd ν _ rfl _

/-- The environment record, walk 2: the stopped cyclic walk `W^ν_{b, rb}(· ∧ L)`. -/
theorem envFinal_coord_one {ν : Measure (Unit × RingSpace d β)} (hν : CycGood ν)
    (junk : CycEntry Unit d) (s : ℝ≥0) :
    (((pairPlan d β a b ra rb L).envFinal ν).coord junk 1).path.fn s =
      ElboimSly.cycWalk (cycSlice () ν) b rb ((min s L : ℝ≥0) : ℝ) := by
  unfold CycPlan.envFinal
  rw [pairPlan_coord a b ra rb L _ junk (by norm_num), pairPlan_E_fn]
  have := (envPath_len (δ := (pairPlan d β a b ra rb L).start 1 ((pairPlan d β a b ra rb L).ideal
    (fun k ρ => envPath ν ((pairPlan d β a b ra rb L).start k ρ)) 1)) (hν ())).2
  show (envPath ν _).1.fn _ = _
  rw [this]
  exact envFn_fwd ν _ rfl _

end env

section driven

variable (a b : Fin d → ℤ) (ra rb : ℝ) (L : ℝ≥0)

/-- The driving assignment of the plan `𝔭`: walk `k + 1` is driven by `X_k`. -/
def pairJx : ∀ k : ℕ, CycRecN Unit d k → Fin 2 := fun k _ => if k = 0 then 0 else 1

/-- The path rule of the driven record of `𝔭`. -/
noncomputable def pairDrvRule (X : Fin 2 → CycPath d) : PathRule Unit d := fun k ρ =>
  drivenPath β (CycRec.region β (Sum.inl ⟨k, ρ⟩)) (CycRec.ringSet β (Sum.inl ⟨k, ρ⟩))
    ((pairPlan d β a b ra rb L).start k ρ) (X (pairJx k ρ)).1 (drvOffset pairJx ρ (pairJx k ρ))

theorem pairPlan_drivenFinal (X : Fin 2 → CycPath d) :
    (pairPlan d β a b ra rb L).drivenFinal pairJx X =
      (pairPlan d β a b ra rb L).cycFinal (pairDrvRule (β := β) a b ra rb L X) := rfl

omit [Fact (0 < β)] in
theorem pairPlan_start_zero (ρ : CycRecN Unit d 0) :
    (pairPlan d β a b ra rb L).start 0 ρ = ((), a, ra, true) := by simp [pairPlan]

omit [Fact (0 < β)] in
theorem pairPlan_start_one (ρ : CycRecN Unit d 1) :
    (pairPlan d β a b ra rb L).start 1 ρ = ((), b, rb, true) := by simp [pairPlan]

theorem pairJx_zero (ρ : CycRecN Unit d 0) : pairJx 0 ρ = 0 := by simp [pairJx]

theorem pairJx_one (ρ : CycRecN Unit d 1) : pairJx 1 ρ = 1 := by simp [pairJx]

theorem drvOffset_zero' (ρ : CycRecN Unit d 0) :
    drvOffset pairJx ρ (pairJx 0 ρ) = 0 := by simp [drvOffset]

theorem drvOffset_one (ρ : CycRecN Unit d 1) :
    drvOffset pairJx ρ (pairJx 1 ρ) = 0 := by
  unfold drvOffset
  refine Finset.sum_eq_zero fun i _ => ?_
  have : i = 0 := Subsingleton.elim _ _
  subst this
  simp [pairJx]

/-- The path of the first walk of the driven record: `a + X₁` on `[0, L]`. -/
theorem pairDrvRule_zero (X : Fin 2 → CycPath d) (hX0 : (X 0).1.fn 0 = 0) (hL : (L : ℝ) < β) :
    ∀ t ≤ L, (pairDrvRule (β := β) a b ra rb L X 0 Fin.elim0).1.fn t = a + (X 0).1.fn t := by
  have h := drivenPath_one (a := a) (ra := ra) (X := (X 0).1) (X 0).2 hX0 hL
    (CycRec.region β (Sum.inl ⟨0, (Fin.elim0 : CycRecN Unit d 0)⟩))
    (CycRec.ringSet β (Sum.inl ⟨0, (Fin.elim0 : CycRecN Unit d 0)⟩))
    (fun e θ => by rw [region_zero]; exact notMem_empty _)
    (fun e θ => by rw [ringSet_zero]; exact notMem_empty _)
  unfold pairDrvRule
  rw [pairPlan_start_zero, drvOffset_zero', pairJx_zero]
  exact h

theorem drivenFinal_coord_zero (X : Fin 2 → CycPath d) (hX0 : (X 0).1.fn 0 = 0)
    (hL : (L : ℝ) < β) (junk : CycEntry Unit d) (s : ℝ≥0) :
    (((pairPlan d β a b ra rb L).drivenFinal pairJx X).coord junk 0).path.fn s =
      a + (X 0).1.fn (min s L) := by
  rw [pairPlan_drivenFinal, pairPlan_coord a b ra rb L _ junk (by norm_num), pairPlan_E_fn]
  exact pairDrvRule_zero a b ra rb L X hX0 hL _ (min_le_right _ _)

theorem pairDrv_firstWalk (X : Fin 2 → CycPath d) (hX0 : (X 0).1.fn 0 = 0)
    (hL : (L : ℝ) < β) :
    FirstWalk ((pairPlan d β a b ra rb L).ideal (pairDrvRule (β := β) a b ra rb L X) 1) a ra
      (X 0).1 L := by
  set P := pairPlan d β a b ra rb L with hP
  set path := pairDrvRule (β := β) a b ra rb L X with hpath
  have h0 : P.ideal path 1 0 = P.E path 0 := P.ideal_apply path 1 0
  refine ⟨?_, ?_, fun t ht => ?_⟩
  · rw [h0, hP, pairPlan_E_data, pairPlan_start_zero]
  · rw [h0, hP, pairPlan_E_len]
  · rw [h0, hP, pairPlan_E_fn]
    have := pairDrvRule_zero a b ra rb L X hX0 hL (min t L) (min_le_right _ _)
    rw [min_eq_left ht] at this ⊢
    exact this

theorem pairDrvRule_one (X : Fin 2 → CycPath d) (hX0 : (X 0).1.fn 0 = 0)
    (hX1 : (X 1).1.fn 0 = 0) (hL : (L : ℝ) < β) :
    ∀ t ≤ L, (pairDrvRule (β := β) a b ra ra L X 1
      ((pairPlan d β a b ra ra L).ideal (pairDrvRule (β := β) a b ra ra L X) 1)).1.fn t =
        twoParticle a b (X 0).1.fn (X 1).1.fn t := by
  have hfw := pairDrv_firstWalk a b ra ra L X hX0 hL
  have h := drivenPath_two (b := b) (X 0).2 (X 1).2 hX0 hX1 hL hfw
  unfold pairDrvRule
  rw [pairPlan_start_one, drvOffset_one, pairJx_one]
  exact h

/-- **cyclic walks within one lap (b)**, driven record, walk 2: the two-particle path stopped at `L`. -/
theorem drivenFinal_coord_one (X : Fin 2 → CycPath d) (hX0 : (X 0).1.fn 0 = 0)
    (hX1 : (X 1).1.fn 0 = 0) (hL : (L : ℝ) < β) (junk : CycEntry Unit d) (s : ℝ≥0) :
    (((pairPlan d β a b ra ra L).drivenFinal pairJx X).coord junk 1).path.fn s =
      twoParticle a b (X 0).1.fn (X 1).1.fn (min s L) := by
  rw [pairPlan_drivenFinal, pairPlan_coord a b ra ra L _ junk (by norm_num), pairPlan_E_fn]
  exact pairDrvRule_one a b ra L X hX0 hX1 hL _ (min_le_right _ _)

theorem pairDrvRule_one_far (X : Fin 2 → CycPath d) (hX0 : (X 0).1.fn 0 = 0)
    (hX1 : (X 1).1.fn 0 = 0) (hL : (L : ℝ) < β) (h1 : ra + L < rb) (h2 : rb + L < ra + β) :
    ∀ t ≤ L, (pairDrvRule (β := β) a b ra rb L X 1
      ((pairPlan d β a b ra rb L).ideal (pairDrvRule (β := β) a b ra rb L X) 1)).1.fn t =
        b + (X 1).1.fn t := by
  have hfw := pairDrv_firstWalk a b ra rb L X hX0 hL
  have h := drivenPath_two_far (b := b) (X 1).2 hX1 hL hfw h1 h2
  unfold pairDrvRule
  rw [pairPlan_start_one, drvOffset_one, pairJx_one]
  exact h

/-- **cyclic walks within one lap (c)**, driven record, walk 2: `b + X₂` stopped at `L`, when the windows
are disjoint modulo `β`. -/
theorem drivenFinal_coord_one_far (X : Fin 2 → CycPath d) (hX0 : (X 0).1.fn 0 = 0)
    (hX1 : (X 1).1.fn 0 = 0) (hL : (L : ℝ) < β) (h1 : ra + L < rb) (h2 : rb + L < ra + β)
    (junk : CycEntry Unit d) (s : ℝ≥0) :
    (((pairPlan d β a b ra rb L).drivenFinal pairJx X).coord junk 1).path.fn s =
      b + (X 1).1.fn (min s L) := by
  rw [pairPlan_drivenFinal, pairPlan_coord a b ra rb L _ junk (by norm_num), pairPlan_E_fn]
  exact pairDrvRule_one_far a b ra rb L X hX0 hX1 hL h1 h2 _ (min_le_right _ _)

end driven

end ElboimSly.Paper

end
