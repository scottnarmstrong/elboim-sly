/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan5Fast
public import ElboimSly.Paper.Escape.Plan5
public import Mathlib

/-!
# The stopping length of the escape walks: no condition holds before it

The walks W_i and the stopping times tau_i ("on `𝒜_i` none of (1)-(6) holds at any `t ∈ (0, 4^n)`").

`stopLen_le_of_cond`: if one of the conditions (1)-(7) holds for the walk cut at time `t`, then
the stopping length of the walk is `≤ t`.  Equivalently, none of (1)-(7) holds strictly before the
stopping length.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The plan `P` uses the escape rule of the walk number `ℓ` at record index `m`. -/
structure RuleAt (P : CycPlan ℕ (k + 2) β) (D : EscRP k) (m ℓ : ℕ) : Prop where
  st : ∀ ρ : CycRecN ℕ (k + 2) (m + 1), P.st m ρ = D.escSt ℓ ρ
  dl : ∀ ρ : CycRecN ℕ (k + 2) (m + 1), P.dl m ρ = D.escDl ℓ ρ
  idx : D.idx ℓ = m
  pos : 1 ≤ ℓ

theorem entEnd_cut (δ : CycData ℕ (k + 2)) (p : CycPath (k + 2)) (r : ℝ≥0) :
    entEnd ((δ, p.cut (r : ℝ≥0∞)) : CycEntry ℕ (k + 2)) = p.1.fn r := by
  unfold entEnd CycEntry.path CycEntry.len CycPath.cut
  simp only [CPath.cut_len, ENNReal.toNNReal_coe, CPath.cut_fn, min_self, ENNReal.toNNReal_coe]

theorem tm_cut (δ : CycData ℕ (k + 2)) (p : CycPath (k + 2)) (r : ℝ≥0) :
    escTm ((δ, p.cut (r : ℝ≥0∞)) : CycEntry ℕ (k + 2)) = r := by
  unfold escTm CycEntry.len CycPath.cut
  simp only [CPath.cut_len, ENNReal.coe_toReal]

theorem cut_fn_apply (δ : CycData ℕ (k + 2)) (p : CycPath (k + 2)) (r s : ℝ≥0) :
    (CycEntry.path ((δ, p.cut (r : ℝ≥0∞)) : CycEntry ℕ (k + 2))).fn s = p.1.fn (min s r) := by
  unfold CycEntry.path CycPath.cut
  simp only [CPath.cut_fn]
  rw [← ENNReal.coe_min, ENNReal.toNNReal_coe]

theorem snoc_castSucc' {m : ℕ} (ρ : CycRecN ℕ (k + 2) m) (e : CycEntry ℕ (k + 2)) {i : ℕ}
    (hi : i < m) (h : i < m + 1) : CycRec.snoc ρ e ⟨i, h⟩ = ρ ⟨i, hi⟩ := by
  unfold CycRec.snoc
  exact Fin.snoc_castSucc (α := fun _ => CycEntry ℕ (k + 2)) (p := ρ) (x := e) ⟨i, hi⟩

theorem snoc_last' {m : ℕ} (ρ : CycRecN ℕ (k + 2) m) (e : CycEntry ℕ (k + 2)) :
    CycRec.snoc ρ e (Fin.last m) = e := by
  unfold CycRec.snoc
  exact Fin.snoc_last (α := fun _ => CycEntry ℕ (k + 2)) (p := ρ) e

section cong

variable (D : EscRP k) {m ℓ : ℕ} (hidx : D.idx ℓ = m) (hpos : 1 ≤ ℓ)
  (ρ : CycRecN ℕ (k + 2) m) {e₁ e₂ : CycEntry ℕ (k + 2)} (hend : entEnd e₁ = entEnd e₂)

include hidx hpos hend in
theorem Cpos_congr :
    D.Cpos ℓ (CycRec.snoc ρ e₁) ↔ D.Cpos ℓ (CycRec.snoc ρ e₂) := by
  have hlt : ∀ ℓ', 1 ≤ ℓ' → ℓ' < ℓ → D.idx ℓ' < m := by
    intro ℓ' h1 h2
    rw [← hidx]
    unfold EscRP.idx
    omega
  unfold EscRP.Cpos EscRP.Cvisit
  simp only [snoc_last']
  have hC1 : escC1 e₁ ↔ escC1 e₂ := by unfold escC1; rw [hend]
  have hC4 : D.C4 ℓ e₁ ↔ D.C4 ℓ e₂ := by unfold EscRP.C4; rw [hend]
  have hC6 : D.C6 e₁ ↔ D.C6 e₂ := by unfold EscRP.C6; rw [hend]
  have hV : (∃ ℓ' : ℕ, 1 ≤ ℓ' ∧ ℓ' < ℓ ∧ ∃ h : D.idx ℓ' < m + 1,
        escC5 e₁ (CycRec.snoc ρ e₁ ⟨D.idx ℓ', h⟩)) ↔
      (∃ ℓ' : ℕ, 1 ≤ ℓ' ∧ ℓ' < ℓ ∧ ∃ h : D.idx ℓ' < m + 1,
        escC5 e₂ (CycRec.snoc ρ e₂ ⟨D.idx ℓ', h⟩)) := by
    constructor
    · rintro ⟨ℓ', h1, h2, h, hc⟩
      refine ⟨ℓ', h1, h2, h, ?_⟩
      rw [snoc_castSucc' ρ e₁ (hlt ℓ' h1 h2) h] at hc
      rw [snoc_castSucc' ρ e₂ (hlt ℓ' h1 h2) h]
      unfold escC5 at hc ⊢; rwa [← hend]
    · rintro ⟨ℓ', h1, h2, h, hc⟩
      refine ⟨ℓ', h1, h2, h, ?_⟩
      rw [snoc_castSucc' ρ e₂ (hlt ℓ' h1 h2) h] at hc
      rw [snoc_castSucc' ρ e₁ (hlt ℓ' h1 h2) h]
      unfold escC5 at hc ⊢; rwa [hend]
  rw [hC1, hC4, hC6, hV]

end cong

theorem escL_mono {β : ℝ} (hlog : 1 < Real.log β) {r r' : ℝ} (h : r ≤ r') :
    escL β r ≤ escL β r' := by
  unfold escL
  have h1 : 1 < max r (Real.log β) := lt_max_of_lt_right hlog
  have h2 : Real.log (max r (Real.log β)) ≤ Real.log (max r' (Real.log β)) :=
    Real.log_le_log (by linarith) (max_le_max h le_rfl)
  have h3 := Real.log_pos h1
  exact pow_le_pow_left₀ h3.le h2 2

/-- Condition (3) at a later time implies condition (3) at the last event. -/
theorem C3_of_later (D : EscRP k) (hlog : 1 < Real.log D.β) (δ : CycData ℕ (k + 2))
    (p : CycPath (k + 2)) {ς t : ℝ≥0} (hςt : ς ≤ t)
    (hconst : ∀ x : ℝ≥0, ς ≤ x → x ≤ t → p.1.fn x = p.1.fn ς)
    (h : D.C3 ((δ, p.cut (t : ℝ≥0∞)) : CycEntry ℕ (k + 2))) :
    D.C3 ((δ, p.cut (ς : ℝ≥0∞)) : CycEntry ℕ (k + 2)) := by
  by_contra hn
  unfold EscRP.C3 at hn h
  rw [tm_cut] at hn h
  rw [not_le] at hn
  have hw1 := isCyclicPath_shift (p.cut (ς : ℝ≥0∞))
  have hw2 := isCyclicPath_shift (p.cut (t : ℝ≥0∞))
  have key := lt_pathTfast_of_const hw1 hw2 (ς := (ς : ℝ)) (t := (t : ℝ))
    (L₁ := Real.log (max (ς : ℝ) (Real.log D.β)) ^ 2)
    (L₂ := Real.log (max (t : ℝ) (Real.log D.β)) ^ 2) ς.2 (by exact_mod_cast hςt)
    (escL_pos hlog _) (escL_mono hlog (by exact_mod_cast hςt)) ?_ ?_ hn
  · exact absurd key (not_lt.2 h)
  · intro x hx0 hxς
    have hxς' : x.toNNReal ≤ ς := by
      rw [← Real.toNNReal_coe (r := ς)]; exact Real.toNNReal_le_toNNReal hxς
    have h0 : (0 : ℝ≥0) ≤ ς := zero_le
    have h0' : (0 : ℝ≥0) ≤ t := zero_le
    have hxt : x.toNNReal ≤ t := hxς'.trans hςt
    show (CycPath.cut p (ς : ℝ≥0∞)).1.fn x.toNNReal - (CycPath.cut p (ς : ℝ≥0∞)).1.fn 0 =
      (CycPath.cut p (t : ℝ≥0∞)).1.fn x.toNNReal - (CycPath.cut p (t : ℝ≥0∞)).1.fn 0
    have e1 := cut_fn_apply δ p ς x.toNNReal
    have e2 := cut_fn_apply δ p t x.toNNReal
    have e3 := cut_fn_apply δ p ς 0
    have e4 := cut_fn_apply δ p t 0
    unfold CycEntry.path at e1 e2 e3 e4
    simp only at e1 e2 e3 e4
    rw [e1, e2, e3, e4, min_eq_left hxς', min_eq_left hxt, min_eq_left h0, min_eq_left h0']
  · intro x hxς hxt
    have hxς' : ς ≤ x.toNNReal := by
      rw [← Real.toNNReal_coe (r := ς)]; exact Real.toNNReal_le_toNNReal hxς
    have hxt' : x.toNNReal ≤ t := by
      rw [← Real.toNNReal_coe (r := t)]; exact Real.toNNReal_le_toNNReal hxt
    show (CycPath.cut p (t : ℝ≥0∞)).1.fn x.toNNReal - (CycPath.cut p (t : ℝ≥0∞)).1.fn 0 =
      (CycPath.cut p (t : ℝ≥0∞)).1.fn (ς : ℝ).toNNReal - (CycPath.cut p (t : ℝ≥0∞)).1.fn 0
    have e1 := cut_fn_apply δ p t x.toNNReal
    have e2 := cut_fn_apply δ p t (ς : ℝ).toNNReal
    unfold CycEntry.path at e1 e2
    simp only at e1 e2
    rw [e1, e2, Real.toNNReal_coe, min_eq_left hxt', min_eq_left hςt]
    rw [hconst _ hxς' hxt']

theorem cnt_zero' {V : Type*} (p : CPath V) : p.cnt 0 = 0 := by
  unfold CPath.cnt
  have : CDisc p.fn ∩ Iic (0 : ℝ≥0) = ∅ := by
    ext s
    simp only [mem_inter_iff, mem_Iic, mem_empty_iff_false, iff_false, not_and]
    intro hs hs0
    exact absurd (hs.1) (not_lt.2 hs0)
  rw [this]; simp

omit [Fact (0 < β)] in
/-- **No condition holds before the stopping length.**  If one of the conditions (1)-(7) holds for
the walk cut at time `t`, the stopping length is `≤ t`. -/
theorem stopLen_le_of_cond {P : CycPlan ℕ (k + 2) β} {D : EscRP k} {m ℓ : ℕ}
    (hR : RuleAt P D m ℓ) (hlog : 1 < Real.log D.β)
    (ρ : CycRecN ℕ (k + 2) m) (p : CycPath (k + 2)) (t : ℝ≥0)
    (hcond : D.Cany ℓ (CycRec.snoc ρ (P.start m ρ, p.cut (t : ℝ≥0∞)))) :
    P.stopLen m ρ p ≤ t := by
  classical
  set a := p.1.cnt t with ha
  have hjt_le : p.1.jt a ≤ (t : ℝ≥0∞) := (p.1.jt_le_iff a t).2 le_rfl
  have hjt_lt : (t : ℝ≥0∞) < p.1.jt (a + 1) := by
    by_contra h
    rw [not_lt] at h
    have := (p.1.jt_le_iff (a + 1) t).1 h
    omega
  have hfin : p.1.jt a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hjt_le
  set ς : ℝ≥0 := (p.1.jt a).toNNReal with hς
  have hςeq : (ς : ℝ≥0∞) = p.1.jt a := ENNReal.coe_toNNReal hfin
  have hςt : ς ≤ t := by
    have : (ς : ℝ≥0∞) ≤ t := hςeq ▸ hjt_le
    exact_mod_cast this
  have hpos : p.1.fn t = p.1.fn ς := by
    rw [CPath.fn_eq_jv p.1 t, ← ha]; rfl
  have hconst : ∀ x : ℝ≥0, ς ≤ x → x ≤ t → p.1.fn x = p.1.fn ς := by
    intro x hx1 hx2
    have h1 : a ≤ p.1.cnt x := by
      rw [← p.1.jt_le_iff a x, ← hςeq]; exact_mod_cast hx1
    have h2 : p.1.cnt x ≤ a := p.1.cnt_mono hx2
    have : p.1.cnt x = a := le_antisymm h2 h1
    rw [CPath.fn_eq_jv p.1 x, this]; rfl
  set δ := P.start m ρ with hδ
  have hend : entEnd ((δ, p.cut (t : ℝ≥0∞)) : CycEntry ℕ (k + 2)) =
      entEnd ((δ, p.cut (ς : ℝ≥0∞)) : CycEntry ℕ (k + 2)) := by
    rw [entEnd_cut, entEnd_cut, hpos]
  have hhat : P.hatRec m ρ p a = CycRec.snoc ρ (δ, p.cut (ς : ℝ≥0∞)) := by
    unfold CycPlan.hatRec; rw [hςeq]
  by_cases hA : D.Cany ℓ (CycRec.snoc ρ (δ, p.cut (ς : ℝ≥0∞)))
  · -- an event candidate (or the deadline `0` at the start)
    by_cases ha0 : a = 0
    · have hjt0 : p.1.jt 0 ≤ 0 := by
        have := (p.1.jt_le_iff 0 0).2 (Nat.zero_le _)
        simpa using this
      have hjt0' : p.1.jt 0 = 0 := le_antisymm hjt0 (zero_le)
      have hdl : P.dl m (P.hatRec m ρ p 0) = 0 := by
        rw [hR.dl]
        have : P.hatRec m ρ p 0 = CycRec.snoc ρ (δ, p.cut (ς : ℝ≥0∞)) := by
          rw [← hhat, ha0]
        rw [this]
        unfold EscRP.escDl
        rw [ite_eq_left_iff.2 (fun h => absurd hA h)]
      have h1lt : (0 : ℝ≥0∞) < p.1.jt (0 + 1) := by
        by_contra h
        rw [not_lt, nonpos_iff_eq_zero] at h
        have := (p.1.jt_le_iff 1 0).1 (by simpa using h.le)
        rw [cnt_zero'] at this
        omega
      refine le_trans (sInf_le (a := p.1.jt 0 + P.dl m (P.hatRec m ρ p 0)) ?_) ?_
      · refine Or.inr ⟨0, ?_, rfl, ?_⟩
        · rw [hjt0']; exact ENNReal.zero_lt_top
        · rw [hdl, hjt0', add_zero]; exact h1lt
      · rw [hdl, hjt0', add_zero]; exact zero_le
    · refine le_trans (sInf_le (a := p.1.jt a) ?_) hjt_le
      refine Or.inl ⟨a, Nat.one_le_iff_ne_zero.2 ha0, ?_, ?_, rfl⟩
      · exact lt_of_le_of_lt hjt_le ENNReal.coe_lt_top
      · rw [hR.st, hhat]
        unfold EscRP.escSt
        simp [hA]
  · -- no event candidate: a deadline candidate
    have hcT : D.Cany ℓ (CycRec.snoc ρ (δ, p.cut (t : ℝ≥0∞))) := hcond
    have hcase : D.C2 ℓ ((δ, p.cut (t : ℝ≥0∞)) : CycEntry ℕ (k + 2)) ∨
        D.C7 ((δ, p.cut (t : ℝ≥0∞)) : CycEntry ℕ (k + 2)) := by
      unfold EscRP.Cany at hcT
      rcases hcT with h1 | h2 | h3 | h7
      · exact absurd ((Cpos_congr D hR.idx hR.pos ρ hend).1 h1) (fun h => hA (Or.inl h))
      · simp only [snoc_last'] at h2; exact Or.inl h2
      · simp only [snoc_last'] at h3
        exact absurd (C3_of_later D hlog δ p hςt hconst h3)
          (fun h => hA (Or.inr (Or.inr (Or.inl (by simpa [snoc_last'] using h)))))
      · simp only [snoc_last'] at h7; exact Or.inr h7
    have hlen : CycEntry.len ((δ, p.cut (ς : ℝ≥0∞)) : CycEntry ℕ (k + 2)) = ς := by
      unfold CycEntry.len CycPath.cut
      simp only [CPath.cut_len]
    have hdl : P.dl m (P.hatRec m ρ p a) ≤ (t : ℝ≥0∞) - p.1.jt a := by
      rw [hR.dl, hhat]
      unfold EscRP.escDl
      rw [ite_eq_right hA]
      simp only [snoc_last']
      rw [← hςeq]
      rcases hcase with h2 | h7
      · refine (min_le_left _ _).trans (tsub_le_tsub_right ?_ _)
        unfold escT2
        refine sInf_le ⟨(t : ℝ), by simp, ?_, ?_⟩
        · rw [tm_cut]
          refine max_le (by exact_mod_cast hςt) ?_
          have := h2.1; rw [tm_cut] at this; exact this
        · have := h2.2
          rw [tm_cut, entEnd_cut] at this
          rw [entEnd_cut]; rw [← hpos]; exact this
      · refine (min_le_right _ _).trans (le_of_eq ?_)
        have : (4 : ℝ) ^ D.n = (t : ℝ) := by
          have := h7; unfold EscRP.C7 at this; rw [tm_cut] at this; exact this.symm
        rw [this, ENNReal.ofReal_coe_nnreal, hlen]
    have hlt : p.1.jt a + P.dl m (P.hatRec m ρ p a) < p.1.jt (a + 1) := by
      refine lt_of_le_of_lt ?_ hjt_lt
      calc p.1.jt a + P.dl m (P.hatRec m ρ p a) ≤ p.1.jt a + ((t : ℝ≥0∞) - p.1.jt a) :=
            add_le_add le_rfl hdl
        _ = t := add_tsub_cancel_of_le hjt_le
    refine le_trans (sInf_le (a := p.1.jt a + P.dl m (P.hatRec m ρ p a))
      (Or.inr ⟨a, lt_of_le_of_lt hjt_le ENNReal.coe_lt_top, rfl, hlt⟩)) ?_
    calc p.1.jt a + P.dl m (P.hatRec m ρ p a) ≤ p.1.jt a + ((t : ℝ≥0∞) - p.1.jt a) :=
          add_le_add le_rfl hdl
      _ = t := add_tsub_cancel_of_le hjt_le

/-- Entries `1, …, I` of `𝒫₅` use the escape rule of the walk `m`. -/
theorem plan5_ruleAt (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
    {m : ℕ} (hm0 : m ≠ 0) (hm : m ≤ escIstar n (escJ n)) :
    RuleAt (plan5 n β tn u β' i hlog) (escRP n β u 1) m m where
  st ρ := by simp [plan5, hm0, hm]
  dl ρ := by simp [plan5, hm0, hm]
  idx := by simp only [EscRP.idx, escRP]; omega
  pos := Nat.one_le_iff_ne_zero.2 hm0

/-- Entries `0, …, I - 1` of `𝒫_𝒜` use the escape rule of the walk `m + 1`. -/
theorem planA_ruleAt (n : ℕ) (u : EscV k) (β' : ℕ) (hlog : 1 < Real.log β) (m : ℕ) :
    RuleAt (planA n β u β' hlog) (escRP n β u 0) m (m + 1) where
  st ρ := rfl
  dl ρ := rfl
  idx := by simp [EscRP.idx, escRP]
  pos := Nat.le_add_left _ _

omit [Fact (0 < β)] in
/-- If the stopping length is `4^n`, none of the conditions (1)-(7) holds at a time `t < 4^n`. -/
theorem not_cond_of_stopLen {P : CycPlan ℕ (k + 2) β} {D : EscRP k} {m ℓ : ℕ}
    (hR : RuleAt P D m ℓ) (hlog : 1 < Real.log D.β)
    (ρ : CycRecN ℕ (k + 2) m) (p : CycPath (k + 2)) (hlen : P.stopLen m ρ p = (4 : ℝ≥0∞) ^ D.n)
    {t : ℝ≥0} (ht : (t : ℝ) < 4 ^ D.n) :
    ¬ D.Cany ℓ (CycRec.snoc ρ (P.start m ρ, p.cut (t : ℝ≥0∞))) := by
  intro h
  have h1 := stopLen_le_of_cond hR hlog ρ p t h
  rw [hlen] at h1
  have : ((4 : ℝ≥0) ^ D.n : ℝ≥0) ≤ t := by exact_mod_cast h1
  have h2 : (4 : ℝ) ^ D.n ≤ t := by exact_mod_cast this
  linarith

omit [Fact (0 < β)] in
/-- The hypotheses (1), (2), (6) of the inclusion at ES22 §5 on `𝒜_i = {τ_i = 4^n}`, in terms of the
path `p` of the walk. -/
theorem inclusion_hyps_of_stopLen {P : CycPlan ℕ (k + 2) β} {D : EscRP k} {m ℓ : ℕ}
    (hR : RuleAt P D m ℓ) (hlog : 1 < Real.log D.β)
    (ρ : CycRecN ℕ (k + 2) m) (p : CycPath (k + 2)) (hlen : P.stopLen m ρ p = (4 : ℝ≥0∞) ^ D.n) :
    (∀ t : ℝ, 0 ≤ t → t < 4 ^ D.n → p.1.fn t.toNNReal ≠ 0) ∧
    (∀ t : ℝ, 0 ≤ t → t < 4 ^ D.n → Real.log D.β ≤ t →
      2 * Real.sqrt t / Real.log t < ‖p.1.fn t.toNNReal - D.P ℓ‖) ∧
    (∀ t : ℝ, 0 ≤ t → t < 4 ^ D.n → (2 : ℝ) ^ D.j / 8 < Metric.infDist
        (fun c => ((p.1.fn t.toNNReal c : ℤ) : ℝ)) ((fun x c => ((x c : ℤ) : ℝ)) '' D.Bm)) := by
  have key : ∀ t : ℝ, 0 ≤ t → t < 4 ^ D.n →
      ¬ D.Cany ℓ (CycRec.snoc ρ (P.start m ρ, p.cut ((t.toNNReal : ℝ≥0) : ℝ≥0∞))) := by
    intro t ht0 ht
    exact not_cond_of_stopLen hR hlog ρ p hlen (by rwa [Real.coe_toNNReal t ht0])
  refine ⟨fun t ht0 ht h0 => key t ht0 ht ?_, fun t ht0 ht hl => ?_, fun t ht0 ht => ?_⟩
  · refine Or.inl (Or.inl ?_)
    simp only [snoc_last']
    unfold escC1; rw [entEnd_cut]; exact h0
  · by_contra hc
    rw [not_lt] at hc
    refine key t ht0 ht (Or.inr (Or.inl ?_))
    simp only [snoc_last']
    refine ⟨?_, ?_⟩
    · rw [tm_cut, Real.coe_toNNReal t ht0]; exact hl
    · rw [tm_cut, entEnd_cut, Real.coe_toNNReal t ht0]; exact hc
  · by_contra hc
    rw [not_lt] at hc
    refine key t ht0 ht (Or.inl (Or.inr (Or.inr (Or.inr ?_))))
    simp only [snoc_last']
    unfold EscRP.C6; rw [entEnd_cut]; exact hc

end ElboimSly.Paper.Escape
