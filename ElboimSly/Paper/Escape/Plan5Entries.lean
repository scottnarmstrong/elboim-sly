/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan5Fin
public import ElboimSly.Paper.Escape.Plan5Stop
public import ElboimSly.Paper.Escape.Visits
public import ElboimSly.Paper.Escape.ReadDisjoint
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvInv
public import Mathlib

/-!
# The entries of the final record of `𝒫₅` in an environment

The connecting plan; The walks W_i and the stopping times tau_i.

For a good environment `ν`, `ent5 ν m` is entry `m` of the final record of `plan5`:

* `m = 0`: walk `1` to the block (`ent5_walk1_left`: its left limits lie outside `B`);
* `1 ≤ m ≤ I`: the walks `W_m`, with data `(0, p_m, β', +1)` (`ent5_data_mid`) and the properties of
  Vertices visited by an explored walk (a) and density of the explored walks around p_i (`ent5_HV`, `ent5_HD`);
* `m = I + 1`: the backward walk, with data `(0, p_i, β', -1)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

section walk1

/-- A path position in the block forces the stopping length of the first walk. -/
theorem stopLen_plan5_zero_le (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
    (ρ : CycRecN ℕ (k + 2) 0) (p : CycPath (k + 2)) (s : ℝ≥0)
    (hs : p.1.fn s ∈ escBlock (escJ n) u) :
    (plan5 n β tn u β' i hlog).stopLen 0 ρ p ≤ s := by
  classical
  set P := plan5 n β tn u β' i hlog with hP
  set a := p.1.cnt s with ha
  have hjt_le : p.1.jt a ≤ (s : ℝ≥0∞) := (p.1.jt_le_iff a s).2 le_rfl
  have hjt_lt : (s : ℝ≥0∞) < p.1.jt (a + 1) := by
    by_contra h
    rw [not_lt] at h
    have := (p.1.jt_le_iff (a + 1) s).1 h
    omega
  have hfin : p.1.jt a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hjt_le
  set ς : ℝ≥0 := (p.1.jt a).toNNReal with hς
  have hςeq : (ς : ℝ≥0∞) = p.1.jt a := ENNReal.coe_toNNReal hfin
  have hςs : ς ≤ s := by
    have : (ς : ℝ≥0∞) ≤ s := hςeq ▸ hjt_le
    exact_mod_cast this
  have hpos : p.1.fn s = p.1.fn ς := by
    rw [CPath.fn_eq_jv p.1 s, ← ha]; rfl
  set δ := P.start 0 ρ with hδ
  have hhat : P.hatRec 0 ρ p a = CycRec.snoc ρ (δ, p.cut (ς : ℝ≥0∞)) := by
    unfold CycPlan.hatRec; rw [hςeq]
  have hend : entEnd ((δ, p.cut (ς : ℝ≥0∞)) : CycEntry ℕ (k + 2)) ∈ escBlock (escJ n) u := by
    rw [entEnd_cut, ← hpos]; exact hs
  by_cases ha0 : a = 0
  · have hjt0 : p.1.jt 0 ≤ 0 := by
      have := (p.1.jt_le_iff 0 0).2 (Nat.zero_le _)
      simpa using this
    have hjt0' : p.1.jt 0 = 0 := le_antisymm hjt0 (zero_le)
    have hdl : P.dl 0 (P.hatRec 0 ρ p 0) = 0 := by
      have : P.hatRec 0 ρ p 0 = CycRec.snoc ρ (δ, p.cut (ς : ℝ≥0∞)) := by
        rw [← hhat, ha0]
      rw [this]
      simp only [hP, plan5, ite_true]
      unfold plan5Dl0
      rw [ite_eq_left]
      have h2 : entEnd (CycRec.snoc ρ (δ, p.cut (ς : ℝ≥0∞)) (Fin.last 0)) ∈
          escBlock (escJ n) u := by rw [snoc_last']; exact hend
      exact h2
    have h1lt : (0 : ℝ≥0∞) < p.1.jt (0 + 1) := by
      by_contra h
      rw [not_lt, nonpos_iff_eq_zero] at h
      have := (p.1.jt_le_iff 1 0).1 (by simpa using h.le)
      rw [cnt_zero'] at this
      omega
    refine le_trans (sInf_le (a := p.1.jt 0 + P.dl 0 (P.hatRec 0 ρ p 0)) ?_) ?_
    · refine Or.inr ⟨0, ?_, rfl, ?_⟩
      · rw [hjt0']; exact ENNReal.zero_lt_top
      · rw [hdl, hjt0', add_zero]; exact h1lt
    · rw [hdl, hjt0', add_zero]; exact zero_le
  · refine le_trans (sInf_le (a := p.1.jt a) ?_) hjt_le
    refine Or.inl ⟨a, Nat.one_le_iff_ne_zero.2 ha0, ?_, ?_, rfl⟩
    · exact lt_of_le_of_lt hjt_le ENNReal.coe_lt_top
    · rw [hhat]
      simp only [hP, plan5, ite_true]
      unfold plan5St0
      simp only [snoc_last']
      simp [hend]

end walk1

section entries

variable (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
  (ν : Measure (CycS ℕ (k + 2) β))

/-- Entry `m` of the final record of `𝒫₅` in the environment `ν`. -/
noncomputable def ent5 (m : ℕ) : CycEntry ℕ (k + 2) :=
  (plan5 n β tn u β' i hlog).E (rule (plan5 n β tn u β' i hlog) ν) m

/-- The full path of walk `m` of `𝒫₅` in `ν`. -/
noncomputable abbrev pth5 (m : ℕ) : CycPath (k + 2) := pth (plan5 n β tn u β' i hlog) ν m

theorem ent5_eq (m : ℕ) :
    ent5 n tn u β' i hlog ν m =
      (dat (plan5 n β tn u β' i hlog) ν m,
        (pth5 n tn u β' i hlog ν m).cut
          ((plan5 n β tn u β' i hlog).stopLen m
            ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) m)
            (pth5 n tn u β' i hlog ν m))) := by
  unfold ent5
  rw [E_eq]
  rfl

theorem ent5_len (m : ℕ) :
    (ent5 n tn u β' i hlog ν m).len =
      (plan5 n β tn u β' i hlog).stopLen m
        ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) m)
        (pth5 n tn u β' i hlog ν m) :=
  len_E_eq ν _ m

theorem ent5_data (m : ℕ) :
    (ent5 n tn u β' i hlog ν m).data =
      plan5Start (escRP n β u 1 : EscRP k) i β' m := by
  rw [ent5_eq]
  rfl

theorem ent5_data_zero :
    (ent5 n tn u β' i hlog ν 0).data = (((0 : ℕ), (0 : EscV k), (0 : ℝ), true) : CycData ℕ (k + 2)) := by
  rw [ent5_data]
  simp [plan5Start]

theorem ent5_data_mid {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ escIstar n (escJ n)) :
    (ent5 n tn u β' i hlog ν m).data =
      (((0 : ℕ), escPoint n (escJ n) u m, (β' : ℝ), true) : CycData ℕ (k + 2)) := by
  rw [ent5_data]
  have : m ≠ 0 := by omega
  simp [plan5Start, this, hm, escRP]

theorem ent5_data_back :
    (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).data =
      (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2)) := by
  rw [ent5_data]
  simp [plan5Start, escRP]

/-- The path of an entry agrees with the full path up to its length. -/
theorem ent5_fn (m : ℕ) {s : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ (ent5 n tn u β' i hlog ν m).len) :
    (ent5 n tn u β' i hlog ν m).path.fn s = (pth5 n tn u β' i hlog ν m).1.fn s := by
  rw [ent5_eq]
  unfold CycEntry.path CycPath.cut
  simp only
  rw [CPath.cut_fn]
  rw [ent5_len] at hs
  rw [min_eq_left hs]; simp

theorem ent5_left (m : ℕ) {r : ℝ≥0} (hr : 0 < r)
    (hl : (r : ℝ≥0∞) ≤ (ent5 n tn u β' i hlog ν m).len) :
    (ent5 n tn u β' i hlog ν m).path.left r = (pth5 n tn u β' i hlog ν m).1.left r := by
  rw [ent5_eq]
  unfold CycEntry.path CycPath.cut
  simp only
  rw [ent5_len] at hl
  exact CPath.left_cut _ _ hr hl

/-- A left limit of an entry is the value of the full path slightly before. -/
theorem ent5_left_eventually (m : ℕ) {r : ℝ≥0} (hr : 0 < r)
    (hl : (r : ℝ≥0∞) ≤ (ent5 n tn u β' i hlog ν m).len) :
    ∀ᶠ s in 𝓝[<] r, (pth5 n tn u β' i hlog ν m).1.fn s =
      (ent5 n tn u β' i hlog ν m).path.left r := by
  rw [ent5_left n tn u β' i hlog ν m hr hl]
  exact (pth5 n tn u β' i hlog ν m).1.eventually_left hr

/-- Walk `1` leaves no point of `B` before its stopping length: its left limits lie outside `B`. -/
theorem ent5_walk1_left {r : ℝ≥0} (hr : 0 < r)
    (hl : (r : ℝ≥0∞) ≤ (ent5 n tn u β' i hlog ν 0).len) :
    (ent5 n tn u β' i hlog ν 0).path.left r ∉ escBlock (escJ n) u := by
  intro hB
  have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
  obtain ⟨s, hs, hsr⟩ := ((ent5_left_eventually n tn u β' i hlog ν 0 hr hl).and
    (self_mem_nhdsWithin (a := r) (s := Iio r))).exists
  have hsB : (pth5 n tn u β' i hlog ν 0).1.fn s ∈ escBlock (escJ n) u := by rw [hs]; exact hB
  have h1 := stopLen_plan5_zero_le n tn (β := β) u β' i hlog
    ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) 0)
    (pth5 n tn u β' i hlog ν 0) s hsB
  rw [ent5_len] at hl
  have h2 : (r : ℝ≥0∞) ≤ s := hl.trans h1
  exact absurd (ENNReal.coe_le_coe.1 h2) (not_le.2 hsr)

/-- Before the stopping length of walk `m` none of the conditions (1)-(7) holds. -/
theorem ent5_not_cond {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ escIstar n (escJ n)) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < (ent5 n tn u β' i hlog ν m).len) :
    ¬ (escRP n β u 1 : EscRP k).Cany m (CycRec.snoc
        ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) m)
        ((plan5 n β tn u β' i hlog).start m
          ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) m),
          (pth5 n tn u β' i hlog ν m).cut (t : ℝ≥0∞))) := by
  intro h
  have h1 := stopLen_le_of_cond (plan5_ruleAt n tn u β' i hlog (by omega) hm) hlog
    ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) m)
    (pth5 n tn u β' i hlog ν m) t h
  rw [ent5_len] at ht
  exact absurd ht (not_lt.2 h1)

theorem ent5_not_C2 {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ escIstar n (escJ n)) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < (ent5 n tn u β' i hlog ν m).len) :
    ¬ (Real.log β ≤ (t : ℝ) ∧
      ‖(pth5 n tn u β' i hlog ν m).1.fn t - escPoint n (escJ n) u m‖ ≤
        2 * Real.sqrt t / Real.log t) := by
  rintro ⟨h1, h2⟩
  refine ent5_not_cond n tn u β' i hlog ν hm1 hm ht (Or.inr (Or.inl ⟨?_, ?_⟩))
  · simp only [snoc_last', tm_cut]; exact h1
  · simp only [snoc_last', tm_cut, entEnd_cut]; exact h2

theorem ent5_not_C4 {m ℓ : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ escIstar n (escJ n)) (hℓ1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ escIstar n (escJ n)) (hne : ℓ ≠ m) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < (ent5 n tn u β' i hlog ν m).len) :
    (n : ℝ) ^ 17 / 6 < ‖(pth5 n tn u β' i hlog ν m).1.fn t - escPoint n (escJ n) u ℓ‖ := by
  by_contra hle
  rw [not_lt] at hle
  refine ent5_not_cond n tn u β' i hlog ν hm1 hm ht (Or.inl (Or.inr (Or.inl ?_)))
  unfold EscRP.C4
  simp only [snoc_last', entEnd_cut]
  exact ⟨ℓ, hℓ1, hℓ, hne, by simpa [escRP] using hle⟩

/-- Vertices visited by an explored walk (a) for the left limits of walk `m`. -/
theorem ent5_HV {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ escIstar n (escJ n)) {R : ℝ}
    (hR : max (Real.log β) 10 ≤ R) {r : ℝ≥0} (hr : 0 < r)
    (hl : (r : ℝ≥0∞) ≤ (ent5 n tn u β' i hlog ν m).len)
    (hin : ‖(ent5 n tn u β' i hlog ν m).path.left r - escPoint n (escJ n) u m‖ ≤ R) :
    (r : ℝ) ≤ 4 * R ^ 2 * Real.log R ^ 2 := by
  by_contra hgt
  push Not at hgt
  have hR10 : 10 ≤ R := le_trans (le_max_right _ _) hR
  have hlb : Real.log β ≤ R := le_trans (le_max_left _ _) hR
  have hRT := R_le_T hR10
  have hT0 : 0 ≤ 4 * R ^ 2 * Real.log R ^ 2 := by positivity
  have hlt : (4 * R ^ 2 * Real.log R ^ 2).toNNReal < r := by
    rw [Real.toNNReal_lt_iff_lt_coe hT0]; exact hgt
  have hne : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
  obtain ⟨s, hs, hsI⟩ := (((ent5_left_eventually n tn u β' i hlog ν m hr hl).and
    (Ioo_mem_nhdsLT hlt))).exists
  have hsr : s < r := hsI.2
  have hsT : 4 * R ^ 2 * Real.log R ^ 2 < s := by
    have := hsI.1
    rwa [Real.toNNReal_lt_iff_lt_coe hT0] at this
  have hsl : (s : ℝ≥0∞) < (ent5 n tn u β' i hlog ν m).len :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hsr) hl
  refine ent5_not_C2 n tn u β' i hlog ν hm1 hm hsl ⟨by linarith, ?_⟩
  rw [hs]
  exact hin.trans (sqrt_div_log_ge hR10 hsT.le)

/-- Density of the explored walks around p_i for the left limits of walk `m ≠ i`. -/
theorem ent5_HD {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ escIstar n (escJ n)) (hi1 : 1 ≤ i)
    (hiI : i ≤ escIstar n (escJ n)) (hmi : m ≠ i) {r : ℝ≥0} (hr : 0 < r)
    (hl : (r : ℝ≥0∞) ≤ (ent5 n tn u β' i hlog ν m).len) :
    (n : ℝ) ^ 17 / 6 - 2 < ‖(ent5 n tn u β' i hlog ν m).path.left r - escPoint n (escJ n) u i‖ := by
  have hne : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
  obtain ⟨s, hs, hsr⟩ := (((ent5_left_eventually n tn u β' i hlog ν m hr hl)).and
    (self_mem_nhdsWithin (a := r) (s := Iio r))).exists
  have hsl : (s : ℝ≥0∞) < (ent5 n tn u β' i hlog ν m).len :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hsr) hl
  have := ent5_not_C4 n tn u β' i hlog ν hm1 hm hi1 hiI (Ne.symm hmi) hsl
  rw [hs] at this
  linarith

end entries

end ElboimSly.Paper.Escape
