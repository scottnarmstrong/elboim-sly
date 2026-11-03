/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan5Stop
public import ElboimSly.Paper.Escape.Plan5Fin
public import ElboimSly.Paper.Escape.Plan5Entries
public import ElboimSly.Paper.Escape.Plan53Env
public import Mathlib

/-!
# The walks `W_ℓ` of `𝒫₅` are those of `𝒫_𝒜`

The connecting plan ("Walks `2, …, I + 1` have the same records as in `𝒫_𝒜`").

* `cany_shift`: the conditions (1)-(7) of walk `m + 1` read, in `𝒫₅` (offset `1`) and in `𝒫_𝒜`
  (offset `0`), the same data: the record of `𝒫₅` without its first entry is the record of `𝒫_𝒜`;
* `stopLen_shift`: hence the stopping lengths agree;
* `ent5_succ_eq_escEntry`: entry `m + 1` of the final record of `𝒫₅` is entry `m` of `𝒫_𝒜`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

theorem cany_shift (n : ℕ) (u : EscV k) {m : ℕ} (ρ : CycRecN ℕ (k + 2) (m + 1))
    (e : CycEntry ℕ (k + 2)) :
    (escRP n β u 1).Cany (m + 1) (CycRec.snoc ρ e) ↔
      (escRP n β u 0).Cany (m + 1) (CycRec.snoc (fun ℓ : Fin m => ρ ℓ.succ) e) := by
  unfold EscRP.Cany EscRP.Cpos
  have hv : (escRP n β u 1).Cvisit (m + 1) (CycRec.snoc ρ e) ↔
      (escRP n β u 0).Cvisit (m + 1) (CycRec.snoc (fun ℓ : Fin m => ρ ℓ.succ) e) := by
    unfold EscRP.Cvisit
    simp only [snoc_last']
    constructor
    · rintro ⟨ℓ', h1, h2, h, hc⟩
      have hidx : (escRP n β u 1).idx ℓ' = ℓ' := by simp [EscRP.idx, escRP]; omega
      have hidx0 : (escRP n β u 0).idx ℓ' = ℓ' - 1 := by simp [EscRP.idx, escRP]
      have hlt : (escRP n β u 0).idx ℓ' < m + 1 := by rw [hidx0]; omega
      refine ⟨ℓ', h1, h2, hlt, ?_⟩
      have e1 : CycRec.snoc ρ e ⟨(escRP n β u 1).idx ℓ', h⟩ = ρ ⟨ℓ', by omega⟩ := by
        have := snoc_castSucc' ρ e (i := (escRP n β u 1).idx ℓ') (by rw [hidx]; omega) h
        rw [this]; congr 1; exact Fin.ext hidx
      have e2 : CycRec.snoc (fun ℓ : Fin m => ρ ℓ.succ) e ⟨(escRP n β u 0).idx ℓ', hlt⟩ =
          ρ ⟨ℓ', by omega⟩ := by
        have := snoc_castSucc' (fun ℓ : Fin m => ρ ℓ.succ) e (i := (escRP n β u 0).idx ℓ')
          (by rw [hidx0]; omega) hlt
        rw [this]; congr 1; apply Fin.ext; simp [hidx0]; omega
      rw [e2]; rw [e1] at hc; exact hc
    · rintro ⟨ℓ', h1, h2, h, hc⟩
      have hidx : (escRP n β u 1).idx ℓ' = ℓ' := by simp [EscRP.idx, escRP]; omega
      have hidx0 : (escRP n β u 0).idx ℓ' = ℓ' - 1 := by simp [EscRP.idx, escRP]
      have hlt : (escRP n β u 1).idx ℓ' < m + 2 := by rw [hidx]; omega
      refine ⟨ℓ', h1, h2, hlt, ?_⟩
      have e1 : CycRec.snoc ρ e ⟨(escRP n β u 1).idx ℓ', hlt⟩ = ρ ⟨ℓ', by omega⟩ := by
        have := snoc_castSucc' ρ e (i := (escRP n β u 1).idx ℓ') (by rw [hidx]; omega) hlt
        rw [this]; congr 1; exact Fin.ext hidx
      have e2 : CycRec.snoc (fun ℓ : Fin m => ρ ℓ.succ) e ⟨(escRP n β u 0).idx ℓ', h⟩ =
          ρ ⟨ℓ', by omega⟩ := by
        have := snoc_castSucc' (fun ℓ : Fin m => ρ ℓ.succ) e (i := (escRP n β u 0).idx ℓ')
          (by rw [hidx0]; omega) h
        rw [this]; congr 1; apply Fin.ext; simp [hidx0]; omega
      rw [e1]; rw [e2] at hc; exact hc
  simp only [snoc_last']
  have hC1 : (escRP n β u 1).C4 (m + 1) e ↔ (escRP n β u 0).C4 (m + 1) e := Iff.rfl
  have hC6 : (escRP n β u 1).C6 e ↔ (escRP n β u 0).C6 e := Iff.rfl
  have hC2 : (escRP n β u 1).C2 (m + 1) e ↔ (escRP n β u 0).C2 (m + 1) e := Iff.rfl
  have hC3 : (escRP n β u 1).C3 e ↔ (escRP n β u 0).C3 e := Iff.rfl
  have hC7 : (escRP n β u 1).C7 e ↔ (escRP n β u 0).C7 e := Iff.rfl
  rw [hv, hC1, hC6, hC2, hC3, hC7]

theorem escSt_shift (n : ℕ) (u : EscV k) {m : ℕ} (ρ : CycRecN ℕ (k + 2) (m + 1))
    (e : CycEntry ℕ (k + 2)) :
    (escRP n β u 1).escSt (m + 1) (CycRec.snoc ρ e) =
      (escRP n β u 0).escSt (m + 1) (CycRec.snoc (fun ℓ : Fin m => ρ ℓ.succ) e) := by
  unfold EscRP.escSt
  exact decide_eq_decide.2 (cany_shift n u ρ e)

theorem escDl_shift (n : ℕ) (u : EscV k) {m : ℕ} (ρ : CycRecN ℕ (k + 2) (m + 1))
    (e : CycEntry ℕ (k + 2)) :
    (escRP n β u 1).escDl (m + 1) (CycRec.snoc ρ e) =
      (escRP n β u 0).escDl (m + 1) (CycRec.snoc (fun ℓ : Fin m => ρ ℓ.succ) e) := by
  unfold EscRP.escDl
  by_cases h : (escRP n β u 0).Cany (m + 1) (CycRec.snoc (fun ℓ : Fin m => ρ ℓ.succ) e)
  · have h' := (cany_shift n u ρ e).2 h
    rw [ite_eq_left h, ite_eq_left h']
  · have h' : ¬ (escRP n β u 1).Cany (m + 1) (CycRec.snoc ρ e) := fun hh =>
      h ((cany_shift n u ρ e).1 hh)
    rw [ite_eq_right h, ite_eq_right h']
    simp only [snoc_last', escRP]

theorem stopLen_shift (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β) {m : ℕ}
    (hm : m + 1 ≤ escIstar n (escJ n)) (ρ : CycRecN ℕ (k + 2) (m + 1)) (p : CycPath (k + 2)) :
    (plan5 n β tn u β' i hlog).stopLen (m + 1) ρ p =
      (planA n β u β' hlog).stopLen m (fun ℓ : Fin m => ρ ℓ.succ) p := by
  have hR5 := plan5_ruleAt (k := k) n tn u β' i hlog (m := m + 1) (by omega) hm
  have hRA := planA_ruleAt (k := k) n u β' hlog m
  have hstart : (plan5 n β tn u β' i hlog).start (m + 1) ρ =
      (planA n β u β' hlog).start m (fun ℓ : Fin m => ρ ℓ.succ) := by
    simp only [plan5, planA, plan5Start, escRP]
    simp [hm]
  have hst : ∀ a, (plan5 n β tn u β' i hlog).st (m + 1)
      ((plan5 n β tn u β' i hlog).hatRec (m + 1) ρ p a) =
      (planA n β u β' hlog).st m ((planA n β u β' hlog).hatRec m (fun ℓ : Fin m => ρ ℓ.succ) p a) := by
    intro a
    unfold CycPlan.hatRec
    rw [hR5.st, hRA.st, hstart]
    exact escSt_shift n u ρ _
  have hdl : ∀ a, (plan5 n β tn u β' i hlog).dl (m + 1)
      ((plan5 n β tn u β' i hlog).hatRec (m + 1) ρ p a) =
      (planA n β u β' hlog).dl m ((planA n β u β' hlog).hatRec m (fun ℓ : Fin m => ρ ℓ.succ) p a) := by
    intro a
    unfold CycPlan.hatRec
    rw [hR5.dl, hRA.dl, hstart]
    exact escDl_shift n u ρ _
  unfold CycPlan.stopLen
  congr 1
  ext t
  simp only [mem_union, mem_ofPred_eq, hst, hdl]

theorem ent5_succ_eq_escEntry (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
    (ν : Measure (CycS ℕ (k + 2) β)) :
    ∀ m : ℕ, m + 1 ≤ escIstar n (escJ n) →
      ent5 n tn u β' i hlog ν (m + 1) = escEntry n u β' hlog ν m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hideal : (fun ℓ : Fin m => ((plan5 n β tn u β' i hlog).ideal
        (rule (plan5 n β tn u β' i hlog) ν) (m + 1)) ℓ.succ) =
        (planA n β u β' hlog).ideal (envRuleA n u β' hlog ν) m := by
      funext ℓ
      rw [ideal_apply' (n := n) (u := u) (b := β') (hlog := hlog) (ν := ν) m ℓ]
      have h1 : ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) (m + 1))
          ℓ.succ = ent5 n tn u β' i hlog ν ((ℓ : ℕ) + 1) :=
        CycPlan.ideal_apply _ _ (m + 1) ℓ.succ
      rw [h1]
      exact ih ℓ ℓ.2 (by have := ℓ.2; omega)
    have hdat : (ent5 n tn u β' i hlog ν (m + 1)).data =
        (((0 : ℕ), escPoint n (escJ n) u (m + 1), (β' : ℝ), true) : CycData ℕ (k + 2)) :=
      ent5_data_mid n tn u β' i hlog ν (by omega) hm
    rw [ent5_eq] at hdat ⊢
    rw [escEntry_eq]
    have hdat' : dat (plan5 n β tn u β' i hlog) ν (m + 1) =
        (((0 : ℕ), escPoint n (escJ n) u (m + 1), (β' : ℝ), true) : CycData ℕ (k + 2)) := hdat
    have hstart : (planA n β u β' hlog).start m
        ((planA n β u β' hlog).ideal (envRuleA n u β' hlog ν) m) =
        (((0 : ℕ), escPoint n (escJ n) u (m + 1), (β' : ℝ), true) : CycData ℕ (k + 2)) := rfl
    have hpth : pth5 n tn u β' i hlog ν (m + 1) =
        envPath ν (((0 : ℕ), escPoint n (escJ n) u (m + 1), (β' : ℝ), true) : CycData ℕ (k + 2)) := by
      unfold pth5 pth
      rw [hdat']
    rw [hdat', hstart, hpth]
    congr 2
    have := stopLen_shift n tn u β' i hlog hm
      ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) (m + 1))
      (envPath ν (((0 : ℕ), escPoint n (escJ n) u (m + 1), (β' : ℝ), true) : CycData ℕ (k + 2)))
    rw [hideal] at this
    exact this

end ElboimSly.Paper.Escape
