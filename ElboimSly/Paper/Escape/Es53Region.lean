/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan53Rec
public import Mathlib

/-!
# The region explored by `W_1, …, W_{i-1}` and the fresh walk

ES22 Lemma 5.3, "A common point at a time `r' ≤ r` means `‖P̃(r'-) - W_ℓ(r''-)‖ ≤ 1`".

* `escVisNbr ν m`: the vertices within `ℓ∞`-distance `1` of a vertex visited by `W_1, …, W_m` up to
  their stopping times (this is `A'`);
* `region_trunc_cum`: a point of the region `R_{Λ_m}` is read by one of the walks `W_1, …, W_m`;
* `disjoint_region`: if the fresh path avoids `A'` up to `r`, it reads no point of `R_{Λ_m}`
  during `(0, r]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n : ℕ} {u : Fin (k + 2) → ℤ} {b : ℕ}
  {hlog : 1 < Real.log β}

/-- `A'`: vertices within `1` of a vertex visited by `W_1, …, W_m` before their stopping times. -/
def escVisNbr (n : ℕ) (u : Fin (k + 2) → ℤ) (b : ℕ) (hlog : 1 < Real.log β)
    (ν : Measure (CycS ℕ (k + 2) β)) (m : ℕ) : Set (Fin (k + 2) → ℤ) :=
  {y | ∃ j : ℕ, j < m ∧ ∃ s : ℝ≥0, (s : ℝ≥0∞) ≤ (escEntry n u b hlog ν j).len ∧
    ‖y - (escEntry n u b hlog ν j).path.fn s‖ ≤ 1}

theorem region_trunc_cum (ν : Measure (CycS ℕ (k + 2) β)) {m : ℕ}
    (hm : m < escIstar n (escJ n)) (x : CycS ℕ (k + 2) β)
    (hx : x ∈ (CycRec.trunc (((planA n β u b hlog).envFinal ν).cum m).toNNReal
      ((planA n β u b hlog).envFinal ν)).region β) :
    ∃ j : ℕ, j < m ∧ ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ≥0∞) ≤ (escEntry n u b hlog ν j).len ∧
      Edge.Mem ((escEntry n u b hlog ν j).path.left r) x.2.1 := by
  rw [CycRec.mem_region_trunc_iff (planA n β u b hlog).junk] at hx
  obtain ⟨j, hj, r, hr0, hrl, hcum, -, -, hmem⟩ := hx
  rw [num_envFinal] at hj
  have hjI : j < escIstar n (escJ n) := by exact_mod_cast hj
  have hcoord : ((planA n β u b hlog).envFinal ν).coord (planA n β u b hlog).junk j =
      escEntry n u b hlog ν j := by
    unfold CycRec.coord
    rw [envFinal_nth, ite_eq_left hjI]; rfl
  rw [hcoord] at hrl hmem
  have hfin : ((planA n β u b hlog).envFinal ν).cum m ≠ ⊤ := cum_envFinal_ne_top ν hm.le
  have hjlt : j < m := by
    by_contra hge
    rw [not_lt] at hge
    have hmono : ((planA n β u b hlog).envFinal ν).cum m ≤
        ((planA n β u b hlog).envFinal ν).cum j := CycRec.cum_mono _ hge
    have hfinj : ((planA n β u b hlog).envFinal ν).cum j ≠ ⊤ :=
      cum_envFinal_ne_top ν hjI.le
    rw [ENNReal.coe_toNNReal hfin] at hcum
    have : ((planA n β u b hlog).envFinal ν).cum j + (r : ℝ≥0∞) ≤
        ((planA n β u b hlog).envFinal ν).cum j + 0 := by
      rw [add_zero]; exact hcum.trans hmono
    have h0 := (ENNReal.add_le_add_iff_left hfinj).1 this
    have : (r : ℝ≥0∞) = 0 := le_antisymm h0 zero_le
    exact hr0.ne' (by exact_mod_cast this)
  exact ⟨j, hjlt, r, hr0, hrl, hmem⟩

theorem exists_lt_eq_left {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    (p : CPath V) {r : ℝ≥0} (hr : 0 < r) :
    ∃ s : ℝ≥0, s < r ∧ p.fn s = p.left r := by
  have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
  obtain ⟨s, hs1, hs2⟩ := ((p.eventually_left hr).and (Ioo_mem_nhdsLT hr)).exists
  exact ⟨s, hs2.2, hs1⟩

theorem disjoint_region (ν : Measure (CycS ℕ (k + 2) β)) {m : ℕ} (hm : m < escIstar n (escJ n))
    (δ : CycData ℕ (k + 2)) (pF : CycPath (k + 2)) (r : ℝ≥0)
    (hA : ∀ s : ℝ≥0, s ≤ r → pF.1.fn s ∉ escVisNbr n u b hlog ν m) :
    Disjoint (CycEntry.region β ((δ, pF.cut (r : ℝ≥0∞)) : CycEntry ℕ (k + 2)))
      ((CycRec.trunc (((planA n β u b hlog).envFinal ν).cum m).toNNReal
        ((planA n β u b hlog).envFinal ν)).region β) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  obtain ⟨r', hr'0, hr'l, -, -, hmem1⟩ := hx1
  obtain ⟨j, hjm, r'', hr''0, hr''l, hmem2⟩ := region_trunc_cum ν hm x hx2
  have hr'r : r' ≤ r := by
    have : (r' : ℝ≥0∞) ≤ r := by
      simpa [CycEntry.len, CycPath.cut, CPath.cut_len] using hr'l
    exact_mod_cast this
  -- the left limit of the fresh path at `r'`
  have ha : ((CycEntry.path ((δ, pF.cut (r : ℝ≥0∞)) : CycEntry ℕ (k + 2))).left r') =
      pF.1.left r' := by
    unfold CycEntry.path CycPath.cut
    exact CPath.left_cut pF.1 (r : ℝ≥0∞) hr'0 (by exact_mod_cast hr'r)
  rw [ha] at hmem1
  obtain ⟨s1, hs1lt, hs1⟩ := exists_lt_eq_left pF.1 hr'0
  obtain ⟨s2, hs2lt, hs2⟩ := exists_lt_eq_left (escEntry n u b hlog ν j).path hr''0
  have hnorm := norm_le_one_of_mem_edge hmem1 hmem2
  rw [← hs1, ← hs2] at hnorm
  refine hA s1 (hs1lt.le.trans hr'r) ?_
  refine ⟨j, hjm, s2, ?_, hnorm⟩
  exact (ENNReal.coe_le_coe.2 hs2lt.le).trans hr''l

end ElboimSly.Paper.Escape
