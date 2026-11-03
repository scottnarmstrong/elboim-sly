/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycPlanSanity
public import ElboimSly.Foundations.Cyclic.CycMarkovLift
public import ElboimSly.Foundations.Cyclic.CycWalkTraj
public import Mathlib

/-!
# The records of the one-walk plan `𝒫_W`

Markov property of the environment at walk stopping times, proof ("Consider the plan `𝒫_W` with `I = {1}`, `K = 1`,
`start_1 = (1,0,0,+1)`, `dl_1 ≡ ∞`, `st_1 ≡ 0`"). This is `onePlan` of `CycPlanSanity`.

* `trunc_one`: truncation of a one-entry record of infinite length;
* `envFinal_onePlan`: the final record of `onePlan` is the single world-line `(δ₀, P^ν_{δ₀})`;
* `markovRec`: the truncated record `cycRec(s) = (δ₀, P^ν_{δ₀}(· ∧ s))`;
* `envFn_liftU`: the environment path of `liftU ν` is the cyclic walk `W^ν_{0,0}`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The start datum `δ₀ = (1, 0, 0, +1)` of the plan `𝒫_W`. -/
def markovData (d : ℕ) : CycData Unit d := ((), 0, 0, true)

theorem trunc_one (s : ℝ≥0) (g : CycRecN Unit d 1) (hg : (g 0).len = ⊤) :
    CycRec.trunc s (Sum.inl ⟨1, g⟩) = Sum.inl ⟨1, fun _ => (g 0).cut s⟩ := by
  classical
  have hcum0 : CycRec.cum (Sum.inl ⟨1, g⟩ : CycRec Unit d) 0 = 0 := by simp [CycRec.cum]
  have hcum1 : CycRec.cum (Sum.inl ⟨1, g⟩ : CycRec Unit d) 1 = ⊤ := by
    simp [CycRec.cum, CycRec.lenAt, CycRec.nth, hg]
  unfold CycRec.trunc
  have key : ∀ (m : ℕ) (F : Fin m → CycEntry Unit d), m = 1 →
      (∀ i, F i = (g 0).cut s) →
      (Sum.inl ⟨m, F⟩ : CycRec Unit d) = Sum.inl ⟨1, fun _ => (g 0).cut s⟩ := by
    rintro m F rfl hF
    congr
    funext i
    exact hF i
  have hc : (Finset.univ.filter fun i : Fin 1 =>
        CycRec.cum (Sum.inl ⟨1, g⟩ : CycRec Unit d) ↑i ≤ ↑s).card = 1 := by
    have : (Finset.univ.filter fun i : Fin 1 =>
        CycRec.cum (Sum.inl ⟨1, g⟩ : CycRec Unit d) ↑i ≤ ↑s) = Finset.univ := by
      ext i
      have : (i : ℕ) = 0 := by omega
      simp [hcum0]
    rw [this]; simp
  refine key _ _ hc ?_
  intro i
  have hi : (i : ℕ) = 0 := by have := i.2; omega
  simp only [CycRec.truncEntry, hi, hcum1, hcum0, zero_add]
  have : ¬ (⊤ : ℝ≥0∞) ≤ s := by simp
  simp only [this, ite_false, tsub_zero]
  congr 2
  exact Subsingleton.elim _ _

/-- The final record of the one-walk plan is the single world-line `(δ₀, P^ν_{δ₀})`. -/
theorem envFinal_onePlan (ν : Measure (Unit × RingSpace d β)) :
    CycPlan.envFinal (onePlan d β) ν =
      Sum.inl ⟨1, fun _ => (markovData d, (envPath ν (markovData d)).cut ⊤)⟩ := by
  classical
  set P := onePlan d β
  let path : PathRule Unit d := fun k ρ => envPath ν (P.start k ρ)
  have hs0 : P.cycState path 0 = CycRec.empty := rfl
  have hs1 : P.cycState path 1 = Sum.inl ⟨1, CycRec.snoc (Fin.elim0 : CycRecN Unit d 0)
      (P.start 0 Fin.elim0, (path 0 Fin.elim0).cut (P.stopLen 0 Fin.elim0 (path 0 Fin.elim0)))⟩ := by
    show P.cycStep path (P.cycState path 0) = _
    rw [hs0]
    unfold CycPlan.cycStep CycRec.empty
    have : ¬ P.Ended (Sum.inl ⟨0, Fin.elim0⟩) := by
      simp [CycPlan.Ended, P, onePlan]
    simp [this]
  have hend : P.Ended (P.cycState path 1) := by
    rw [hs1]; simp [CycPlan.Ended, P, onePlan]
  have hex : ∃ n, P.Ended (P.cycState path n) := ⟨1, hend⟩
  have hfind : Nat.find hex = 1 := by
    rw [Nat.find_eq_iff]
    refine ⟨hend, fun n hn => ?_⟩
    obtain rfl : n = 0 := by omega
    rw [hs0]; simp [CycRec.empty, CycPlan.Ended, P, onePlan]
  have hfin : CycPlan.envFinal P ν = P.cycState path 1 := by
    unfold CycPlan.envFinal CycPlan.cycFinal
    rw [dite_eq_left hex, hfind]
  rw [hfin, hs1]
  congr 2
  funext i
  have hi : i = Fin.last 0 := Fin.ext (by have := i.2; simp [Fin.last])
  subst hi
  have hsl : P.stopLen 0 Fin.elim0 (path 0 Fin.elim0) = ⊤ := onePlan_stopLen _ _ _
  simp only [CycRec.snoc, Fin.snoc_last]
  rw [hsl]
  rfl

/-- The record `cycRec(s)` of the plan `𝒫_W`: `(δ₀, P^ν_{δ₀}(· ∧ s))`. -/
noncomputable def markovEntry (ν : Measure (Unit × RingSpace d β)) (s : ℝ≥0) : CycEntry Unit d :=
  (markovData d, (envPath ν (markovData d)).cut s)

theorem markovEntry_len (ν : Measure (Unit × RingSpace d β)) (s : ℝ≥0) :
    (markovEntry ν s).len = s := by
  show ((envPath ν (markovData d)).cut s).1.len = s
  exact CPath.cut_len _ _

theorem markovEntry_fn (ν : Measure (Unit × RingSpace d β)) (s r : ℝ≥0) :
    (markovEntry ν s).path.fn r = (envPath ν (markovData d)).1.fn (min r s) := by
  show ((envPath ν (markovData d)).cut s).1.fn r = _
  rw [CycPath.cut]
  show ((envPath ν (markovData d)).1.cut s).fn r = _
  rw [CPath.cut_fn]
  congr 1

theorem trunc_envFinal_onePlan (ν : Measure (Unit × RingSpace d β)) (s : ℝ≥0) :
    CycRec.trunc s (CycPlan.envFinal (onePlan d β) ν) = Sum.inl ⟨1, fun _ => markovEntry ν s⟩ := by
  rw [envFinal_onePlan, trunc_one]
  · rfl
  · show ((envPath ν (markovData d)).cut ⊤).1.len = ⊤
    exact CPath.cut_len _ _

/-- The environment path of the lift is the cyclic walk. -/
theorem envFn_liftU (ν : Measure (RingSpace d β)) (r : ℝ≥0) :
    envFn (liftU ν) (markovData d) r = ElboimSly.cycWalk ν 0 0 (r : ℝ) := by
  have hm : envMeasure (liftU ν) (markovData d) = ν := by
    simp [envMeasure, markovData, CycData.fwd, CycData.copy]
  unfold envFn ElboimSly.cycWalk
  simp only [hm, NNReal.zero_le_coe, ite_true, Real.toNNReal_coe]
  have : (markovData d).sgn * (markovData d).phase = 0 := by
    simp [markovData, CycData.sgn, CycData.phase, CycData.fwd]
  rw [this]
  rfl

theorem envPath_fn_liftU {ν : Measure (RingSpace d β)} (hν : Good ν) (r : ℝ≥0) :
    (envPath (liftU ν) (markovData d)).1.fn r = ElboimSly.cycWalk ν 0 0 (r : ℝ) := by
  have hg : Good (cycSlice (markovData d).copy (liftU ν)) := by
    show Good (cycSlice () (liftU ν))
    rw [cycSlice_liftU]; exact hν
  rw [show (envPath (liftU ν) (markovData d)).1.fn = envFn (liftU ν) (markovData d) from
    (envPath_len hg).2]
  exact envFn_liftU ν r

end ElboimSly.Cyclic

end
