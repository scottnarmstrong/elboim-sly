/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvScheme
public import ElboimSly.Foundations.Cyclic.CycSchemeRegionZ
public import Mathlib

/-!
# The driving scheme (a), masking: the driving usage of a record

The driving scheme (a), masking. "The driving explored region contains, in copy `j'`,
only points with driving times at most the total driving time already used in copy `j'`."

`drvUse jx ρ j` is the total length of the entries `i` of `ρ` with driving index `𝖩_i = j`; the
driving time at which the current walk stands is `drvT = drvUse ρ (drvIdx st)` (`drvT_eq_drvUse`),
and `drvUse` never decreases along the environment recursion, increasing at the current index by
at least the step length (`drvUse_upd_ge`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {J : Type*} {jx : ∀ k : ℕ, CycRecN I d k → J}

/-- The total length of the entries of the record with driving index `j`. -/
noncomputable def drvUse (jx : ∀ k : ℕ, CycRecN I d k → J) (ρ : CycRec I d) (j : J) : ℝ≥0 :=
  match ρ with
  | Sum.inl ⟨_, f⟩ => drvOffset jx f j
  | Sum.inr _ => 0

omit [MeasurableSpace I] in
theorem drvOffset_succ {n : ℕ} (f : Fin (n + 1) → CycEntry I d) (j : J) :
    drvOffset jx f j = drvOffset jx (fun m : Fin n => f m.castSucc) j +
      (open scoped Classical in
        if jx n (fun m : Fin n => f m.castSucc) = j then (f (Fin.last n)).len.toNNReal else 0) := by
  classical
  unfold drvOffset
  rw [Fin.sum_univ_castSucc]
  rfl

omit [MeasurableSpace I] in
theorem drvOffset_le_succ {n : ℕ} (f : Fin (n + 1) → CycEntry I d) (j : J) :
    drvOffset jx (fun m : Fin n => f m.castSucc) j ≤ drvOffset jx f j := by
  rw [drvOffset_succ]
  exact le_self_add

omit [MeasurableSpace I] in
theorem drvOffset_update_last {n : ℕ} (f : Fin (n + 1) → CycEntry I d) (e : CycEntry I d) (j : J) :
    drvOffset jx (Function.update f (Fin.last n) e) j =
      drvOffset jx (fun m : Fin n => f m.castSucc) j +
      (open scoped Classical in
        if jx n (fun m : Fin n => f m.castSucc) = j then e.len.toNNReal else 0) := by
  classical
  rw [drvOffset_succ]
  have h1 : (fun m : Fin n => Function.update f (Fin.last n) e m.castSucc) =
      fun m : Fin n => f m.castSucc := by
    funext m
    exact Function.update_of_ne (Fin.castSucc_lt_last m).ne _ _
  simp only [h1, Function.update_self]

omit [MeasurableSpace I] in
theorem drvOffset_snoc_ge {n : ℕ} (f : Fin n → CycEntry I d) (e : CycEntry I d) (j : J) :
    drvOffset jx f j ≤ drvOffset jx (CycRec.snoc f e) j := by
  have := drvOffset_le_succ (jx := jx) (CycRec.snoc f e) j
  have h : (fun m : Fin n => CycRec.snoc f e m.castSucc) = f := by
    funext m; simp [CycRec.snoc]
  rwa [h] at this

namespace CycScheme

variable [Countable I] [MeasurableSingletonClass I] (P : CycPlan I d β) (sc : ℝ≥0∞)

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem drvT_eq_drvUse (j0 : J) {st : State I d} (hW : WF st) :
    drvT jx P st = (drvUse jx st.1 (drvIdx jx j0 st) : ℝ) := by
  obtain ⟨ρ, b⟩ := st
  obtain ⟨n, f, h1, h2⟩ := hW
  simp only at h1
  subst h1
  classical
  have hc := cur_inl (β := β) P n f b
  unfold drvT drvUse drvOff drvIdx
  simp only
  rw [drvOffset_succ, hc]
  simp only [ite_true]
  push_cast
  rfl

theorem drvUse_newRec (j0 : J) {st : State I d} (hW : WF st) (o : Outcome (CycS I d β)) (j : J) :
    drvUse jx (newRec P sc st o) j = drvUse jx st.1 j +
      (open scoped Classical in
        if drvIdx jx j0 st = j then (sStar P sc st o : ℝ≥0) else 0) := by
  classical
  obtain ⟨ρ, b⟩ := st
  obtain ⟨n, f, h1, h2⟩ := hW
  simp only at h1
  subst h1
  have hc := cur_inl (β := β) P n f b
  have hlen : (f (Fin.last n)).len = ((f (Fin.last n)).time : ℝ≥0∞) := CycEntry.len_eq_time h2
  unfold newRec newEntry
  simp only [hc]
  show drvOffset jx (Function.update f (Fin.last n) _) j = drvOffset jx f j + _
  rw [drvOffset_update_last, drvOffset_succ]
  unfold drvIdx
  simp only
  by_cases hj : jx n (fun m : Fin n => f m.castSucc) = j
  · simp only [hj, ite_true]
    have : ((f (Fin.last n)).len).toNNReal = (f (Fin.last n)).time := rfl
    rw [this, add_assoc]
    congr 1
  · simp [hj]

theorem drvUse_upd_ge (j0 : J) {st : State I d} (hW : WF st) (o : Outcome (CycS I d β)) (j : J) :
    drvUse jx st.1 j ≤ drvUse jx (upd P sc st o).1 j := by
  classical
  unfold upd
  by_cases hb : st.2 = true
  · simp [hb]
  · simp only [hb, ite_false, Bool.false_eq_true]
    have hN := drvUse_newRec (jx := jx) P sc j0 hW o j
    have hge : drvUse jx st.1 j ≤ drvUse jx (newRec P sc st o) j := by
      rw [hN]; exact le_self_add
    split_ifs with hs hK
    · refine hge.trans ?_
      have hN' := newRec_wf (P := P) (sc := sc) hW o
      obtain ⟨n, f, h1, -⟩ := hN'
      show _ ≤ drvUse jx (CycRec.push _ (newRec P sc st o)) j
      rw [h1]
      exact drvOffset_snoc_ge _ _ _
    · exact hge
    · exact hge

theorem drvUse_upd_idx (j0 : J) {st : State I d} (hW : WF st) (hb : st.2 = false)
    (o : Outcome (CycS I d β)) :
    drvT jx P st + (sStar P sc st o : ℝ) ≤
      (drvUse jx (upd P sc st o).1 (drvIdx jx j0 st) : ℝ) := by
  classical
  have hN := drvUse_newRec (jx := jx) P sc j0 hW o (drvIdx jx j0 st)
  simp only [ite_true] at hN
  have hT := drvT_eq_drvUse (jx := jx) P j0 hW
  have hle : drvUse jx st.1 (drvIdx jx j0 st) + (sStar P sc st o : ℝ≥0) ≤
      drvUse jx (upd P sc st o).1 (drvIdx jx j0 st) := by
    unfold upd
    simp only [hb, ite_false, Bool.false_eq_true]
    split_ifs with hs hK
    · refine le_trans (le_of_eq hN.symm) ?_
      have hN' := newRec_wf (P := P) (sc := sc) hW o
      obtain ⟨n, f, h1, -⟩ := hN'
      show _ ≤ drvUse jx (CycRec.push _ (newRec P sc st o)) _
      rw [h1]
      exact drvOffset_snoc_ge _ _ _
    · exact le_of_eq hN.symm
    · exact le_of_eq hN.symm
  rw [hT]
  exact_mod_cast hle

end CycScheme

end ElboimSly.Cyclic

end
