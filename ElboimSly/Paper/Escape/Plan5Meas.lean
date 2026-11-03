/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan5Rules
public import ElboimSly.Paper.Heavy.PiecesPath
public import ElboimSly.Paper.Heavy.MeasFast
public import ElboimSly.Foundations.Cyclic.CycSchemeRec
public import Mathlib

/-!
# Measurability of the stopping rules (1)-(7)

The connecting plan (the maps `start`, `dl`, `st` are measurable).

* `isCyclicPath_shift`: the path of a world-line, translated to start at `0`, is a cyclic path.
* `measurableSet_pair`: a predicate of a countably-valued measurable map and a real measurable map.
* `measurableSet_C1`, …: each of the conditions (1)-(7) is a measurable set of records.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ}

/-- A foundational `CycPath` is a cyclic path (on `[0, ∞)`) after translation to start at `0`. -/
theorem isCyclicPath_shift {d : ℕ} (p : CycPath d) :
    IsCyclicPath (fun t : ℝ => p.1.fn t.toNNReal - p.1.fn 0) := by
  set w : ℝ → Fin d → ℤ := fun t => p.1.fn t.toNNReal - p.1.fn 0 with hwdef
  have hw : ∀ s : ℝ, 0 ≤ s → w s = p.1.fn s.toNNReal - p.1.fn 0 := fun s _ => rfl
  have hcancel : ∀ x y : Fin d → ℤ, x = y → x - p.1.fn 0 = y - p.1.fn 0 := fun x y h => by rw [h]
  have hdiff : ∀ x y : Fin d → ℤ, (x - p.1.fn 0) - (y - p.1.fn 0) = x - y := fun x y => by abel
  refine
    { zero := by simp [hwdef]
      rc := fun s hs => ?_
      fin := fun T => ?_
      jump_size := fun r hr => ?_ }
  · have := eventually_nhdsGE_toNNReal (r := s) (p.1.rc s.toNNReal)
    filter_upwards [this] with u hu
    exact hcancel _ _ hu
  · have hsub : cycJumpSet w ∩ Iic T ⊆
        (fun x : ℝ≥0 => (x : ℝ)) '' (CDisc p.1.fn ∩ Iic T.toNNReal) := by
      rintro r ⟨⟨hr0, hr⟩, hrT⟩
      refine ⟨r.toNNReal, ⟨⟨?_, ?_⟩, Real.toNNReal_le_toNNReal hrT⟩, Real.coe_toNNReal r hr0.le⟩
      · exact Real.toNNReal_pos.2 hr0
      · intro hev
        apply hr
        have := eventually_nhdsLT_toNNReal hr0 hev
        filter_upwards [this] with u hu
        exact hcancel _ _ hu
    exact ((p.1.fin T.toNNReal).image _).subset hsub
  · obtain ⟨hr0, hnev⟩ := hr
    have hr' : 0 < r.toNNReal := Real.toNNReal_pos.2 hr0
    have hmem : r.toNNReal ∈ CDisc p.1.fn := by
      refine ⟨hr', fun hev => hnev ?_⟩
      have := eventually_nhdsLT_toNNReal hr0 hev
      filter_upwards [this] with u hu
      exact hcancel _ _ hu
    have hsum := p.2 _ hmem
    have hev := eventually_nhdsLT_toNNReal hr0 (p.1.eventually_left hr')
    filter_upwards [hev, Ioo_mem_nhdsLT hr0] with u hu hu0
    have e1 : w r = p.1.fn r.toNNReal - p.1.fn 0 := rfl
    have e2 : w u = p.1.fn u.toNNReal - p.1.fn 0 := rfl
    rw [e1, e2]
    simp only [Pi.sub_apply, sub_sub_sub_cancel_right]
    rw [hu]
    exact hsum


/-- A predicate of a countably-valued measurable map and a real measurable map. -/
theorem measurableSet_pair {α V : Type*} [MeasurableSpace α] [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] {g : α → V} (hg : Measurable g) {h : α → ℝ} (hh : Measurable h)
    (S : V → Set ℝ) (hS : ∀ v, MeasurableSet (S v)) : MeasurableSet {a | h a ∈ S (g a)} := by
  have : {a | h a ∈ S (g a)} = ⋃ v, g ⁻¹' {v} ∩ h ⁻¹' S v := by
    ext a; simp
  rw [this]
  exact MeasurableSet.iUnion fun v => (hg (measurableSet_singleton v)).inter (hh (hS v))

theorem measurable_entPath {d : ℕ} : Measurable fun e : CycEntry ℕ d => e.path :=
  measurable_subtype_coe.comp measurable_snd

theorem measurable_entEval {d : ℕ} (s : ℝ≥0) : Measurable fun e : CycEntry ℕ d => e.path.fn s :=
  (CPath.measurable_eval s).comp measurable_entPath

theorem measurable_entEnd : Measurable (entEnd (k := k)) :=
  measurable_fn_at (fun e : CycEntry ℕ (k + 2) => e.path) measurable_entPath
    (fun e => e.len.toNNReal) (ENNReal.measurable_toNNReal.comp measurable_entry_len')

theorem measurable_escTm : Measurable (escTm (k := k)) :=
  ENNReal.measurable_toReal.comp measurable_entry_len'


section conds

variable (D : EscRP k)

theorem measurableSet_of_end (S : Set (EscV k)) :
    MeasurableSet {e : CycEntry ℕ (k + 2) | entEnd e ∈ S} :=
  measurable_entEnd (Set.to_countable S).measurableSet

theorem measurableSet_C1 : MeasurableSet {e : CycEntry ℕ (k + 2) | escC1 e} :=
  measurableSet_of_end {v | v = 0}

theorem measurableSet_C4 (ℓ : ℕ) : MeasurableSet {e : CycEntry ℕ (k + 2) | D.C4 ℓ e} :=
  measurableSet_of_end {v | ∃ ℓ', 1 ≤ ℓ' ∧ ℓ' ≤ D.I ∧ ℓ' ≠ ℓ ∧ ‖v - D.P ℓ'‖ ≤ (D.n : ℝ) ^ 17 / 6}

theorem measurableSet_C6 : MeasurableSet {e : CycEntry ℕ (k + 2) | D.C6 e} :=
  measurableSet_of_end {v | Metric.infDist (fun c => ((v c : ℤ) : ℝ))
    ((fun x c => ((x c : ℤ) : ℝ)) '' D.Bm) ≤ (2 : ℝ) ^ D.j / 8}

theorem measurableSet_C7 : MeasurableSet {e : CycEntry ℕ (k + 2) | D.C7 e} :=
  measurable_escTm (measurableSet_singleton ((4 : ℝ) ^ D.n))

theorem measurableSet_C2 (ℓ : ℕ) : MeasurableSet {e : CycEntry ℕ (k + 2) | D.C2 ℓ e} := by
  have := measurableSet_pair (measurable_entEnd (k := k)) measurable_escTm
    (fun v => {r : ℝ | Real.log D.β ≤ r ∧ ‖v - D.P ℓ‖ ≤ 2 * Real.sqrt r / Real.log r}) fun v =>
      (measurableSet_le measurable_const measurable_id).inter
        (measurableSet_le measurable_const
          ((measurable_const.mul Real.continuous_sqrt.measurable).div Real.measurable_log))
  exact this


/-- The threshold `ln² max(t, ln β)` of condition (3). -/
noncomputable def escL (β t : ℝ) : ℝ := Real.log (max t (Real.log β)) ^ 2

theorem escL_pos {β : ℝ} (hlog : 1 < Real.log β) (t : ℝ) : 0 < escL β t := by
  unfold escL
  have : 1 < max t (Real.log β) := lt_max_of_lt_right hlog
  have := Real.log_pos this
  positivity

theorem escTm_nonneg (e : CycEntry ℕ (k + 2)) : 0 ≤ escTm e := ENNReal.toReal_nonneg

theorem escTm_toNNReal (e : CycEntry ℕ (k + 2)) : (escTm e).toNNReal = e.len.toNNReal := by
  unfold escTm
  exact Real.toNNReal_coe

/-- Rational form of condition (3). -/
theorem C3_iff_rational (hlog : 1 < Real.log D.β) (e : CycEntry ℕ (k + 2)) :
    D.C3 e ↔
      ((∃ q : ℚ, 0 < escTm e ∧ escTm e - 1 ≤ (q : ℝ) ∧ (q : ℝ) < escTm e ∧
          escL D.β (escTm e) ≤ ‖e.path.fn (escTm e).toNNReal - e.path.fn (max (q : ℝ) 0).toNNReal‖) ∨
       (∃ t q : ℚ, 0 < (t : ℝ) ∧ (t : ℝ) < escTm e ∧ (t : ℝ) - 1 ≤ (q : ℝ) ∧ (q : ℝ) < t ∧
          escL D.β (escTm e) ≤ ‖e.path.fn (t : ℝ).toNNReal - e.path.fn (max (q : ℝ) 0).toNNReal‖)) := by
  have hcp := isCyclicPath_shift e.2
  have key := pathTfast_le_iff_rational hcp (escL_pos hlog (escTm e)) (T := escTm e)
    (escTm_nonneg e)
  have hC3 : D.C3 e ↔ pathTfast (fun t : ℝ => e.path.fn t.toNNReal - e.path.fn 0)
      (escL D.β (escTm e)) ≤ ENNReal.ofReal (escTm e) := Iff.rfl
  refine hC3.trans (key.trans ?_)
  have hsub : ∀ a b : Fin (k + 2) → ℤ, a - e.2.1.fn 0 - (b - e.2.1.fn 0) = a - b := fun a b => by
    abel
  simp only [hsub]
  constructor
  · rintro ⟨t, ht, q, hq1, hq2, hL⟩
    rcases ht with ⟨hT, rfl⟩ | ⟨r, hr0, hr1, rfl⟩
    · exact Or.inl ⟨q, hT, hq1, hq2, hL⟩
    · exact Or.inr ⟨r, q, hr0, hr1, hq1, hq2, hL⟩
  · rintro (⟨q, hT, hq1, hq2, hL⟩ | ⟨r, q, hr0, hr1, hq1, hq2, hL⟩)
    · exact ⟨escTm e, Or.inl ⟨hT, rfl⟩, q, hq1, hq2, hL⟩
    · exact ⟨r, Or.inr ⟨r, hr0, hr1, rfl⟩, q, hq1, hq2, hL⟩

theorem measurableSet_C3 (hlog : 1 < Real.log D.β) :
    MeasurableSet {e : CycEntry ℕ (k + 2) | D.C3 e} := by
  have hset : {e : CycEntry ℕ (k + 2) | D.C3 e} =
      (⋃ q : ℚ, {e | escTm e ∈ {r : ℝ | 0 < r ∧ r - 1 ≤ (q : ℝ) ∧ (q : ℝ) < r ∧
          escL D.β r ≤ ‖(entEnd e, e.path.fn (max (q : ℝ) 0).toNNReal).1 -
            (entEnd e, e.path.fn (max (q : ℝ) 0).toNNReal).2‖}}) ∪
      ⋃ t : ℚ, ⋃ q : ℚ, ⋃ (_ : 0 < (t : ℝ) ∧ (t : ℝ) - 1 ≤ (q : ℝ) ∧ (q : ℝ) < t),
        {e | escTm e ∈ {r : ℝ | (t : ℝ) < r ∧
          escL D.β r ≤ ‖(e.path.fn (t : ℝ).toNNReal, e.path.fn (max (q : ℝ) 0).toNNReal).1 -
            (e.path.fn (t : ℝ).toNNReal, e.path.fn (max (q : ℝ) 0).toNNReal).2‖}} := by
    ext e
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, C3_iff_rational D hlog e, exists_prop]
    have h1 : entEnd e = e.path.fn (escTm e).toNNReal := by
      unfold entEnd; rw [escTm_toNNReal]
    constructor
    · rintro (⟨q, h0, h1', h2', h3⟩ | ⟨t, q, h0, h1', h2', h3', h4⟩)
      · exact Or.inl ⟨q, h0, h1', h2', by rw [h1]; exact h3⟩
      · exact Or.inr ⟨t, q, ⟨h0, h2', h3'⟩, h1', h4⟩
    · rintro (⟨q, h0, h1', h2', h3⟩ | ⟨t, q, ⟨h0, h2', h3'⟩, h1', h4⟩)
      · exact Or.inl ⟨q, h0, h1', h2', by rw [← h1]; exact h3⟩
      · exact Or.inr ⟨t, q, h0, h1', h2', h3', h4⟩
  have hLm : Measurable (escL D.β) := by
    unfold escL
    exact Measurable.pow_const (Real.measurable_log.comp (measurable_id.max measurable_const)) 2
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.iUnion fun q => ?_)
    (MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => ?_)
  · refine measurableSet_pair
      ((measurable_entEnd (k := k)).prodMk (measurable_entEval _)) measurable_escTm
      (fun v => {r : ℝ | 0 < r ∧ r - 1 ≤ (q : ℝ) ∧ (q : ℝ) < r ∧ escL D.β r ≤ ‖v.1 - v.2‖}) fun v => ?_
    refine MeasurableSet.inter (s₁ := {r : ℝ | 0 < r}) (s₂ := {r : ℝ | r - 1 ≤ (q : ℝ) ∧ (q : ℝ) < r ∧
      escL D.β r ≤ ‖v.1 - v.2‖}) (measurableSet_lt measurable_const measurable_id) ?_
    refine MeasurableSet.inter (s₁ := {r : ℝ | r - 1 ≤ (q : ℝ)}) (s₂ := {r : ℝ | (q : ℝ) < r ∧
      escL D.β r ≤ ‖v.1 - v.2‖}) (measurableSet_le (measurable_id.sub_const 1) measurable_const) ?_
    exact MeasurableSet.inter (s₁ := {r : ℝ | (q : ℝ) < r}) (s₂ := {r : ℝ | escL D.β r ≤ ‖v.1 - v.2‖})
      (measurableSet_lt measurable_const measurable_id) (measurableSet_le hLm measurable_const)
  · refine measurableSet_pair
      ((measurable_entEval _).prodMk (measurable_entEval _)) measurable_escTm
      (fun v => {r : ℝ | (t : ℝ) < r ∧ escL D.β r ≤ ‖v.1 - v.2‖}) fun v => ?_
    exact MeasurableSet.inter (s₁ := {r : ℝ | (t : ℝ) < r}) (s₂ := {r : ℝ | escL D.β r ≤ ‖v.1 - v.2‖})
      (measurableSet_lt measurable_const measurable_id) (measurableSet_le hLm measurable_const)

end conds


/-- Condition (5) through the jump list of the earlier walk. -/
theorem escC5_iff_jumps (e e' : CycEntry ℕ (k + 2)) :
    escC5 e e' ↔ ∃ a : ℕ, e'.path.jt a ≠ ⊤ ∧ e'.path.jt a ≤ e'.len ∧
      ‖entEnd e - e'.path.jv a‖ ≤ 1 := by
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨e'.path.cnt s, ?_, ?_, ?_⟩
    · have := (e'.path.jt_le_iff (e'.path.cnt s) s).2 le_rfl
      exact ne_top_of_le_ne_top ENNReal.coe_ne_top this
    · exact ((e'.path.jt_le_iff (e'.path.cnt s) s).2 le_rfl).trans hs
    · rw [← CPath.fn_eq_jv]; exact h
  · rintro ⟨a, h1, h2, h3⟩
    refine ⟨(e'.path.jt a).toNNReal, ?_, ?_⟩
    · rw [ENNReal.coe_toNNReal h1]; exact h2
    · exact h3

theorem measurableSet_C5 :
    MeasurableSet {x : CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2) | escC5 x.1 x.2} := by
  have hset : {x : CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2) | escC5 x.1 x.2} =
      ⋃ a : ℕ, {x | x.2.path.jt a ≠ ⊤ ∧ x.2.path.jt a ≤ x.2.len} ∩
        {x | (entEnd x.1, x.2.path.jv a) ∈ {v : EscV k × EscV k | ‖v.1 - v.2‖ ≤ 1}} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, escC5_iff_jumps, and_assoc]
  rw [hset]
  refine MeasurableSet.iUnion fun a => MeasurableSet.inter ?_ ?_
  · have hjt : Measurable fun x : CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2) => x.2.path.jt a :=
      (CPath.measurable_jt a).comp (measurable_entPath.comp measurable_snd)
    have hl : Measurable fun x : CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2) => x.2.len :=
      measurable_entry_len'.comp measurable_snd
    exact (hjt (measurableSet_singleton _).compl).inter (measurableSet_le hjt hl)
  · have : Measurable fun x : CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2) =>
        (entEnd x.1, x.2.path.jv a) :=
      (measurable_entEnd.comp measurable_fst).prodMk
        ((CPath.measurable_jv a).comp (measurable_entPath.comp measurable_snd))
    exact this (Set.to_countable _).measurableSet

section records

variable (D : EscRP k) {m : ℕ}

theorem measurable_last : Measurable fun ρ : CycRecN ℕ (k + 2) (m + 1) => ρ (Fin.last m) :=
  measurable_pi_apply _

theorem measurableSet_Cvisit (ℓ : ℕ) :
    MeasurableSet {ρ : CycRecN ℕ (k + 2) (m + 1) | D.Cvisit ℓ ρ} := by
  have hset : {ρ : CycRecN ℕ (k + 2) (m + 1) | D.Cvisit ℓ ρ} =
      ⋃ ℓ' : ℕ, ⋃ (_ : 1 ≤ ℓ' ∧ ℓ' < ℓ), ⋃ h : D.idx ℓ' < m + 1,
        (fun ρ : CycRecN ℕ (k + 2) (m + 1) => (ρ (Fin.last m), ρ ⟨D.idx ℓ', h⟩)) ⁻¹'
          {x | escC5 x.1 x.2} := by
    ext ρ
    simp only [mem_ofPred_eq, mem_iUnion, mem_preimage, EscRP.Cvisit, exists_prop, and_assoc]
  rw [hset]
  refine MeasurableSet.iUnion fun ℓ' => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun h => ?_
  exact ((measurable_pi_apply _).prodMk (measurable_pi_apply _)) measurableSet_C5

theorem measurableSet_Cpos (ℓ : ℕ) :
    MeasurableSet {ρ : CycRecN ℕ (k + 2) (m + 1) | D.Cpos ℓ ρ} := by
  have h1 : MeasurableSet {ρ : CycRecN ℕ (k + 2) (m + 1) | escC1 (ρ (Fin.last m))} :=
    measurable_last (measurableSet_C1 (k := k))
  have h4 : MeasurableSet {ρ : CycRecN ℕ (k + 2) (m + 1) | D.C4 ℓ (ρ (Fin.last m))} :=
    measurable_last (measurableSet_C4 D ℓ)
  have h6 : MeasurableSet {ρ : CycRecN ℕ (k + 2) (m + 1) | D.C6 (ρ (Fin.last m))} :=
    measurable_last (measurableSet_C6 D)
  exact (h1.union (h4.union ((measurableSet_Cvisit D ℓ).union h6)))

theorem measurableSet_Cany (hlog : 1 < Real.log D.β) (ℓ : ℕ) :
    MeasurableSet {ρ : CycRecN ℕ (k + 2) (m + 1) | D.Cany ℓ ρ} := by
  have h2 : MeasurableSet {ρ : CycRecN ℕ (k + 2) (m + 1) | D.C2 ℓ (ρ (Fin.last m))} :=
    measurable_last (measurableSet_C2 D ℓ)
  have h3 : MeasurableSet {ρ : CycRecN ℕ (k + 2) (m + 1) | D.C3 (ρ (Fin.last m))} :=
    measurable_last (measurableSet_C3 D hlog)
  have h7 : MeasurableSet {ρ : CycRecN ℕ (k + 2) (m + 1) | D.C7 (ρ (Fin.last m))} :=
    measurable_last (measurableSet_C7 D)
  exact (measurableSet_Cpos D ℓ).union (h2.union (h3.union h7))


theorem monotone_escT2 (p w : EscV k) : Monotone (escT2 p w) := by
  intro M M' h
  unfold escT2
  refine sInf_le_sInf ?_
  rintro t ⟨r, hr, hM, hc⟩
  exact ⟨r, hr, h.trans hM, hc⟩

theorem measurable_escT2 (p : EscV k) :
    Measurable fun x : ℝ × EscV k => escT2 p x.2 x.1 := by
  refine measurable_from_prod_countable_left (fun w => ?_)
  exact (monotone_escT2 p w).measurable

theorem measurable_escSt (hlog : 1 < Real.log D.β) (ℓ : ℕ) :
    Measurable fun ρ : CycRecN ℕ (k + 2) (m + 1) => D.escSt ℓ ρ := by
  classical
  unfold EscRP.escSt
  exact measurable_to_bool (by
    have : (fun ρ : CycRecN ℕ (k + 2) (m + 1) => decide (D.Cany ℓ ρ)) ⁻¹' {true} =
        {ρ | D.Cany ℓ ρ} := by ext ρ; simp
    rw [this]; exact measurableSet_Cany D hlog ℓ)

theorem measurable_escDl (hlog : 1 < Real.log D.β) (ℓ : ℕ) :
    Measurable fun ρ : CycRecN ℕ (k + 2) (m + 1) => D.escDl ℓ ρ := by
  classical
  unfold EscRP.escDl
  refine Measurable.ite (measurableSet_Cany D hlog ℓ) measurable_const ?_
  have hlen : Measurable fun ρ : CycRecN ℕ (k + 2) (m + 1) => (ρ (Fin.last m)).len :=
    measurable_entry_len'.comp measurable_last
  refine Measurable.min (Measurable.sub ?_ hlen) (measurable_const.sub hlen)
  have hl : Measurable fun ρ : CycRecN ℕ (k + 2) (m + 1) => (ρ (Fin.last m)) :=
    measurable_last
  have h2 := (measurable_escT2 (k := k) (D.P ℓ)).comp
    (((measurable_escTm.comp hl).max (measurable_const (a := Real.log D.β))).prodMk
      (measurable_entEnd.comp hl))
  exact h2

end records

end ElboimSly.Paper.Escape
