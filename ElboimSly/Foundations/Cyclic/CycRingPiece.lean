/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegionMeas
public import ElboimSly.Frozen.Defs.EdgeMk
public import ElboimSly.Frozen.Defs.LatticeAdj
public import Mathlib

/-!
# Measurability of record functionals (a), part 2: the known rings of an entry through its jump list

A jump of `p` at `r` is a jump time `r = ς_{a+1}`, with `p(r-) = p(ς_a)` and `p(r) = p(ς_{a+1})`.
The ring at that jump is `(ι, {p(ς_a), p(ς_{a+1})}, c_δ(ς_{a+1}))`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.cnt_jt_succ (p : CPath V) {a : ℕ} (h : p.jt (a + 1) < ⊤) :
    p.cnt (p.jt (a + 1)).toNNReal = a + 1 := by
  have h1 : a + 1 ≤ p.cnt (p.jt (a + 1)).toNNReal := p.cnt_ge_of_jt h
  by_contra hne
  have h2 : a + 2 ≤ p.cnt (p.jt (a + 1)).toNNReal := by omega
  have h3 := (p.jt_le_iff (a + 2) _).mpr h2
  rw [ENNReal.coe_toNNReal h.ne] at h3
  have h4 : p.jt (a + 2) < ⊤ := lt_of_le_of_lt h3 h
  exact absurd (p.jt_lt_succ (a := a + 1) h4) (not_lt.mpr h3)

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
/-- A jump of the path at `r` is a jump time `ς_{a+1}`. -/
theorem CPath.exists_jump_idx (p : CPath V) {r : ℝ≥0} (hr : 0 < r) (hne : p.left r ≠ p.fn r) :
    ∃ a : ℕ, (r : ℝ≥0∞) = p.jt (a + 1) ∧ p.left r = p.jv a ∧ p.fn r = p.jv (a + 1) := by
  obtain ⟨a, ha1, ha2⟩ := p.exists_idx hr
  have hleft : p.left r = p.jv a := p.left_eq_jv ha1 ha2
  rcases ha2.lt_or_eq with hlt | heq
  · exfalso
    apply hne
    have h1 : p.cnt r ≤ a := by
      by_contra hc
      have := (p.jt_le_iff (a + 1) r).mpr (by omega)
      exact absurd hlt (not_lt.mpr this)
    have h2 : a ≤ p.cnt r := (p.jt_le_iff a r).mp ha1.le
    rw [hleft, p.fn_eq_jv, show p.cnt r = a by omega]
  · have hfin : p.jt (a + 1) < ⊤ := heq ▸ ENNReal.coe_lt_top
    have hr' : (p.jt (a + 1)).toNNReal = r := by rw [← heq]; simp
    refine ⟨a, heq, hleft, ?_⟩
    rw [p.fn_eq_jv, ← hr', p.cnt_jt_succ hfin]

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
/-- Conversely, at `r = ς_{a+1}` the left limit is `p(ς_a)` and the value is `p(ς_{a+1})`. -/
theorem CPath.left_fn_jt_succ (p : CPath V) {a : ℕ} (h : p.jt (a + 1) < ⊤) :
    0 < (p.jt (a + 1)).toNNReal ∧ p.left (p.jt (a + 1)).toNNReal = p.jv a ∧
      p.fn (p.jt (a + 1)).toNNReal = p.jv (a + 1) := by
  have hlt := p.jt_lt_succ h
  have hr : p.jt a < (p.jt (a + 1)).toNNReal := by rwa [ENNReal.coe_toNNReal h.ne]
  refine ⟨?_, p.left_eq_jv hr (by rw [ENNReal.coe_toNNReal h.ne]), ?_⟩
  · have : (0 : ℝ≥0∞) < ((p.jt (a + 1)).toNNReal : ℝ≥0∞) := lt_of_le_of_lt bot_le hr
    exact_mod_cast this
  · rw [p.fn_eq_jv, p.cnt_jt_succ h]

section Entry

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem latticeAdj_symm {u v : Fin d → ℤ} (h : LatticeAdj d u v) : LatticeAdj d v u := by
  unfold LatticeAdj at *
  simpa only [abs_sub_comm] using h

/-- The edge `{u, v}` if `u ~ v`, and the junk edge `e0` otherwise. -/
noncomputable def edgeOf (e0 : Edge d) (u v : Fin d → ℤ) : Edge d :=
  open scoped Classical in
  if h : LatticeAdj d u v then Edge.mk' u v h else e0

/-- The piece `a` of the known rings of an entry: the ring at the jump time `ς_{a+1}`. -/
def ringValid (E : CycEntry I d) (a : ℕ) : Prop :=
  E.path.jt (a + 1) < ⊤ ∧ E.path.jt (a + 1) ≤ E.len ∧ E.path.jv a ≠ E.path.jv (a + 1) ∧
    LatticeAdj d (E.path.jv a) (E.path.jv (a + 1))

/-- The ring at the jump time `ς_{a+1}`. -/
noncomputable def ringPt (e0 : Edge d) (E : CycEntry I d) (a : ℕ) : I × RingSpace d β :=
  (E.data.copy, (edgeOf e0 (E.path.jv a) (E.path.jv (a + 1)),
    E.data.clock β (E.path.jt (a + 1)).toNNReal))

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem CycEntry.mem_ringSet_iff (e0 : Edge d) (E : CycEntry I d) (x : I × RingSpace d β) :
    x ∈ E.ringSet β ↔ ∃ a, ringValid E a ∧ x = ringPt e0 E a := by
  constructor
  · rintro ⟨r, hr0, hrl, hne, h1, h2, h3⟩
    obtain ⟨a, hra, hl, hf⟩ := E.path.exists_jump_idx hr0 hne
    have hfin : E.path.jt (a + 1) < ⊤ := hra ▸ ENNReal.coe_lt_top
    have hr' : (E.path.jt (a + 1)).toNNReal = r := by rw [← hra]; simp
    have hadj : LatticeAdj d (E.path.jv a) (E.path.jv (a + 1)) := by
      obtain ⟨u, v, huv, hadj⟩ := x.2.1.2
      rw [h3, hl, hf] at huv
      rcases Sym2.eq_iff.mp huv with ⟨h5, h6⟩ | ⟨h5, h6⟩
      · rw [h5, h6]; exact hadj
      · rw [h5, h6]; exact latticeAdj_symm hadj
    refine ⟨a, ⟨hfin, hra ▸ hrl, ?_, hadj⟩, ?_⟩
    · rw [← hl, ← hf]; exact hne
    · unfold ringPt edgeOf
      rw [dite_eq_left hadj, hr']
      refine Prod.ext h1 (Prod.ext (Subtype.ext ?_) h2)
      show x.2.1.1 = s(E.path.jv a, E.path.jv (a + 1))
      rw [h3, hl, hf]
  · rintro ⟨a, ⟨hfin, hle, hne, hadj⟩, rfl⟩
    obtain ⟨hpos, hl, hf⟩ := E.path.left_fn_jt_succ hfin
    refine ⟨(E.path.jt (a + 1)).toNNReal, hpos, ?_, ?_, rfl, rfl, ?_⟩
    · rwa [ENNReal.coe_toNNReal hfin.ne]
    · rw [hl, hf]; exact hne
    · unfold ringPt edgeOf
      rw [dite_eq_left hadj, hl, hf]
      rfl

end Entry

end ElboimSly.Cyclic

end
