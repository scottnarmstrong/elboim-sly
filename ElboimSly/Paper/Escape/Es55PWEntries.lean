/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55PWGeom
public import ElboimSly.Paper.Escape.Plan5Entries
public import ElboimSly.Paper.Escape.C57Env
public import ElboimSly.Paper.Escape.C56Det
public import Mathlib

/-!
# Step 1 of ES22 Lemma 5.5: positions of the entries of the record at `S₃`

ES22 Lemma 5.5, Step 1 ("the left limits of walk `1` at times `≤ ℓ₁` are outside `B`; those
of `W₁, …, W_I` lie at distance `> 2^{j-3}` from `B⁻`; those of `W_i^←` at times `≤ r_i` lie in
`𝒬`").

* `stopLen_plan5_back_le`: the backward walk stops no later than a time at which it is outside `𝒬`;
* `ent5_back_fn_mem`, `ent5_back_left_mem`: the backward walk stays in `𝒬` before its length;
* `ent5_walk1_fn_lt`: walk `1` is outside `B` before its length;
* `ent5_mid_far`: the left limits of `W_m`, `1 ≤ m ≤ I`, are at distance `> 2^j/8` from `B⁻`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- A path position outside `𝒬` forces the stopping length of the backward walk. -/
theorem stopLen_plan5_back_le (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
    (ρ : CycRecN ℕ (k + 2) (escIstar n (escJ n) + 1)) (p : CycPath (k + 2)) (s : ℝ≥0)
    (h0 : p.1.fn 0 ∈ escQ (escJ n) u) (hs : p.1.fn s ∉ escQ (escJ n) u) :
    (plan5 n β tn u β' i hlog).stopLen (escIstar n (escJ n) + 1) ρ p ≤ s := by
  classical
  set P := plan5 n β tn u β' i hlog with hP
  set a := p.1.cnt s with ha
  have hjt_le : p.1.jt a ≤ (s : ℝ≥0∞) := (p.1.jt_le_iff a s).2 le_rfl
  have hfin : p.1.jt a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hjt_le
  set ς : ℝ≥0 := (p.1.jt a).toNNReal with hς
  have hςeq : (ς : ℝ≥0∞) = p.1.jt a := ENNReal.coe_toNNReal hfin
  have hpos : p.1.fn s = p.1.fn ς := by
    rw [CPath.fn_eq_jv p.1 s, ← ha]; rfl
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hs
    rw [hpos]
    have : ς = 0 := by
      have : p.1.jt 0 = 0 := by
        have h := (p.1.jt_le_iff 0 0).2 (Nat.zero_le _)
        exact le_antisymm (by simpa using h) zero_le
      rw [hς, ha0, this]; simp
    rw [this]; exact h0
  set δ := P.start (escIstar n (escJ n) + 1) ρ with hδ
  have hhat : P.hatRec (escIstar n (escJ n) + 1) ρ p a = CycRec.snoc ρ (δ, p.cut (ς : ℝ≥0∞)) := by
    unfold CycPlan.hatRec; rw [hςeq]
  have hend : entEnd ((δ, p.cut (ς : ℝ≥0∞)) : CycEntry ℕ (k + 2)) ∉ escQ (escJ n) u := by
    rw [entEnd_cut, ← hpos]; exact hs
  refine le_trans (sInf_le (a := p.1.jt a) ?_) hjt_le
  refine Or.inl ⟨a, Nat.one_le_iff_ne_zero.2 ha0, ?_, ?_, rfl⟩
  · exact lt_of_le_of_lt hjt_le ENNReal.coe_lt_top
  · rw [hhat]
    have hne1 : escIstar n (escJ n) + 1 ≠ 0 := Nat.succ_ne_zero _
    have hne2 : ¬ escIstar n (escJ n) + 1 ≤ escIstar n (escJ n) := by omega
    simp only [hP, plan5, ite_eq_right hne1, ite_eq_right hne2, ite_true]
    unfold plan5StB
    simp only [snoc_last']
    simp [hend]

section entries

variable (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
  (ν : Measure (CycS ℕ (k + 2) β))

/-- The backward walk is in `𝒬` before its stopping length. -/
theorem ent5_back_fn_mem (hν : CycGood ν) (hpQ : escPoint n (escJ n) u i ∈ escQ (escJ n) u)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).len) :
    (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).path.fn s ∈ escQ (escJ n) u := by
  by_contra hno
  rw [ent5_fn n tn u β' i hlog ν _ hs.le] at hno
  have h0 : (pth5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).1.fn 0 ∈ escQ (escJ n) u := by
    unfold pth5 pth
    rw [envPath_zero (hν _)]
    have : dat (plan5 n β tn u β' i hlog) ν (escIstar n (escJ n) + 1) =
        (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2)) := ent5_data_back n tn u β' i hlog ν
    rw [this]; exact hpQ
  have h1 := stopLen_plan5_back_le n tn u β' i hlog
    ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) (escIstar n (escJ n) + 1))
    (pth5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)) s h0 hno
  rw [← ent5_len] at h1
  exact absurd hs (not_lt.2 h1)

/-- The left limits of the backward walk at times `≤` its length lie in `𝒬`. -/
theorem ent5_back_left_mem (hν : CycGood ν) (hpQ : escPoint n (escJ n) u i ∈ escQ (escJ n) u)
    {r : ℝ≥0} (hr : 0 < r)
    (hl : (r : ℝ≥0∞) ≤ (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).len) :
    (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).path.left r ∈ escQ (escJ n) u := by
  have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
  obtain ⟨s, hs, hsr⟩ := ((ent5_left_eventually n tn u β' i hlog ν _ hr hl).and
    (self_mem_nhdsWithin (a := r) (s := Iio r))).exists
  have hsl : (s : ℝ≥0∞) < (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).len :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hsr) hl
  rw [← hs, ← ent5_fn n tn u β' i hlog ν _ hsl.le]
  exact ent5_back_fn_mem n tn u β' i hlog ν hν hpQ hsl

/-- Walk `1` is outside `B` before its stopping length. -/
theorem ent5_walk1_fn_lt {s : ℝ≥0} (hs : (s : ℝ≥0∞) < (ent5 n tn u β' i hlog ν 0).len) :
    (ent5 n tn u β' i hlog ν 0).path.fn s ∉ escBlock (escJ n) u := by
  intro hB
  rw [ent5_fn n tn u β' i hlog ν 0 hs.le] at hB
  have h1 := stopLen_plan5_zero_le n tn (β := β) u β' i hlog
    ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) 0)
    (pth5 n tn u β' i hlog ν 0) s hB
  rw [← ent5_len] at h1
  exact absurd hs (not_lt.2 h1)

/-- The left limits of `W_m`, `1 ≤ m ≤ I`, are at distance `> 2^j/8` from `B⁻`. -/
theorem ent5_mid_far {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ escIstar n (escJ n)) {r : ℝ≥0} (hr : 0 < r)
    (hl : (r : ℝ≥0∞) ≤ (ent5 n tn u β' i hlog ν m).len) {y : EscV k}
    (hy : y ∈ escBlockMinus (escJ n) u) :
    (2 : ℝ) ^ escJ n / 8 < ‖(ent5 n tn u β' i hlog ν m).path.left r - y‖ := by
  have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
  obtain ⟨s, hs, hsr⟩ := ((ent5_left_eventually n tn u β' i hlog ν m hr hl).and
    (self_mem_nhdsWithin (a := r) (s := Iio r))).exists
  have hsl : (s : ℝ≥0∞) < (ent5 n tn u β' i hlog ν m).len :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hsr) hl
  by_contra hle
  push Not at hle
  refine ent5_not_cond n tn u β' i hlog ν hm1 hm hsl (Or.inl (Or.inr (Or.inr (Or.inr ?_))))
  unfold EscRP.C6
  simp only [snoc_last', entEnd_cut]
  have hne : ((fun x c => ((x c : ℤ) : ℝ)) '' (escRP n β u 1 : EscRP k).Bm).Nonempty :=
    ⟨_, y, hy, rfl⟩
  refine le_trans (Metric.infDist_le_dist_of_mem (x := fun c => (((pth5 n tn u β' i hlog ν m).1.fn s c : ℤ) : ℝ)) ⟨y, hy, rfl⟩) ?_
  rw [dist_eq_norm]
  have := c56_norm_escCast_sub ((pth5 n tn u β' i hlog ν m).1.fn s) y
  unfold escCast at this
  rw [this, hs]
  exact hle

end entries

end ElboimSly.Paper.Escape
