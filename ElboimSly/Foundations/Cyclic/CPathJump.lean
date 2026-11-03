/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CPathCount
import Mathlib

/-!
# Jump times of a path

Paths (a): `ς_a` is measurable, and `p(ς_a-) = p(ς_{a-1})`.

`ς_a(p) = inf {s : a ≤ n_s(p)}` (`⊤` if there are fewer than `a` jumps, `ς_0 = 0`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {V : Type*}

theorem CPath.cnt_mono (p : CPath V) {s t : ℝ≥0} (h : s ≤ t) : p.cnt s ≤ p.cnt t :=
  Set.ncard_le_ncard (inter_subset_inter_right _ (Iic_subset_Iic.mpr h)) (p.fin t)

/-- Right-continuity of the jump count. -/
theorem CPath.exists_gap (p : CPath V) (s : ℝ≥0) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ r ∈ CDisc p.fn, s < r → s + ε < r := by
  classical
  have hF : (CDisc p.fn ∩ Ioc s (s + 1)).Finite := (p.fin (s + 1)).subset
    (fun r hr => ⟨hr.1, hr.2.2⟩)
  by_cases hne : (CDisc p.fn ∩ Ioc s (s + 1)).Nonempty
  · set m := hF.toFinset.min' (by simpa using hne) with hm
    have hmem : m ∈ CDisc p.fn ∩ Ioc s (s + 1) := by
      simpa using hF.toFinset.min'_mem (by simpa using hne)
    refine ⟨(m - s) / 2, ?_, fun r hr hsr => ?_⟩
    · have := hmem.2.1
      exact half_pos (tsub_pos_of_lt this)
    · by_cases hr1 : r ≤ s + 1
      · have hrF : r ∈ hF.toFinset := by simpa using ⟨hr, hsr, hr1⟩
        have hmr : m ≤ r := hF.toFinset.min'_le r hrF
        have hms : s < m := hmem.2.1
        have : (m - s) / 2 < m - s := half_lt_self (tsub_pos_of_lt hms)
        calc s + (m - s) / 2 < s + (m - s) := by gcongr
          _ = m := by rw [add_tsub_cancel_of_le hms.le]
          _ ≤ r := hmr
      · refine lt_of_le_of_lt ?_ (not_le.mp hr1)
        have hms : s < m := hmem.2.1
        have : (m - s) / 2 ≤ m - s := by exact (half_lt_self (tsub_pos_of_lt hms)).le
        calc s + (m - s) / 2 ≤ s + (m - s) := by gcongr
          _ = m := by rw [add_tsub_cancel_of_le hms.le]
          _ ≤ s + 1 := hmem.2.2
  · refine ⟨1, one_pos, fun r hr hsr => ?_⟩
    by_contra hle
    exact hne ⟨r, hr, hsr, not_lt.mp hle⟩

theorem CPath.cnt_rightCont (p : CPath V) (s : ℝ≥0) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ t, s ≤ t → t < s + ε → p.cnt t = p.cnt s := by
  obtain ⟨ε, hε, hgap⟩ := p.exists_gap s
  refine ⟨ε, hε, fun t hst hts => ?_⟩
  unfold CPath.cnt
  congr 1
  ext r
  simp only [Set.mem_inter_iff, Set.mem_Iic]
  constructor
  · rintro ⟨hr, hrt⟩
    refine ⟨hr, ?_⟩
    by_contra hrs
    exact absurd (hgap r hr (not_le.mp hrs)) (not_lt.mpr (hrt.trans hts.le))
  · rintro ⟨hr, hrs⟩
    exact ⟨hr, hrs.trans hst⟩

/-- The `a`-th jump time `ς_a`. -/
noncomputable def CPath.jt (p : CPath V) (a : ℕ) : ℝ≥0∞ :=
  ⨅ s : {s : ℝ≥0 // a ≤ p.cnt s}, (s.1 : ℝ≥0∞)

theorem CPath.jt_le_iff (p : CPath V) (a : ℕ) (s : ℝ≥0) :
    p.jt a ≤ (s : ℝ≥0∞) ↔ a ≤ p.cnt s := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨ε, hε, hc⟩ := p.cnt_rightCont s
    have : ((s + ε : ℝ≥0) : ℝ≥0∞) ≤ p.jt a := by
      refine le_iInf fun ⟨t, ht⟩ => ?_
      simp only [ENNReal.coe_le_coe]
      by_contra htlt
      rcases le_or_gt s t with hst | hts
      · have := hc t hst (not_le.mp htlt)
        omega
      · have := p.cnt_mono hts.le
        omega
    have h2 := this.trans h
    rw [ENNReal.coe_le_coe] at h2
    exact absurd h2 (not_le.mpr (lt_add_of_pos_right s hε))
  · intro h
    exact iInf_le (fun s : {s : ℝ≥0 // a ≤ p.cnt s} => (s.1 : ℝ≥0∞)) ⟨s, h⟩

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

theorem CPath.measurable_jt (a : ℕ) : Measurable (fun p : CPath V => p.jt a) := by
  refine measurable_of_Iic fun c => ?_
  rcases eq_or_ne c ⊤ with rfl | hc
  · simp
  · lift c to ℝ≥0 using hc
    have : (fun p : CPath V => p.jt a) ⁻¹' Iic (c : ℝ≥0∞) = {p | p.jt a ≤ (c : ℝ≥0∞)} := rfl
    simp only [this, CPath.jt_le_iff]
    exact measurableSet_le measurable_const (CPath.measurable_cnt c)

/-- The dyadic approximation from above. -/
noncomputable def dyUp (m : ℕ) (x : ℝ≥0) : ℝ≥0 := (⌈x * 2 ^ m⌉₊ : ℝ≥0) / 2 ^ m

theorem le_dyUp (m : ℕ) (x : ℝ≥0) : x ≤ dyUp m x := by
  unfold dyUp
  rw [le_div_iff₀ (by positivity)]
  exact Nat.le_ceil _

theorem dyUp_lt (m : ℕ) (x : ℝ≥0) : dyUp m x < x + (1 / 2) ^ m := by
  unfold dyUp
  rw [div_lt_iff₀ (by positivity)]
  have h := Nat.ceil_lt_add_one (show (0 : ℝ≥0) ≤ x * 2 ^ m by positivity)
  calc (⌈x * 2 ^ m⌉₊ : ℝ≥0) < x * 2 ^ m + 1 := h
    _ = (x + (1 / 2) ^ m) * 2 ^ m := by
      rw [add_mul, ← mul_pow]; norm_num

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.exists_left_gap (p : CPath V) {c : ℝ≥0} (hc : 0 < c) :
    ∃ t, t < c ∧ ∀ r ∈ CDisc p.fn, t < r → r < c → False := by
  classical
  have hF : (CDisc p.fn ∩ Iio c).Finite := (p.fin c).subset (fun r hr => ⟨hr.1, hr.2.le⟩)
  by_cases hne : (CDisc p.fn ∩ Iio c).Nonempty
  · refine ⟨hF.toFinset.max' (by simpa using hne), ?_, fun r hr h1 h2 => ?_⟩
    · have := hF.toFinset.max'_mem (by simpa using hne)
      simp
    · have hrF : r ∈ hF.toFinset := by simpa using ⟨hr, h2⟩
      exact absurd (hF.toFinset.le_max' r hrF) (not_le.mpr h1)
  · exact ⟨0, hc, fun r hr _ h2 => hne ⟨r, hr, h2⟩⟩

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.cnt_ge_of_jt (p : CPath V) {a : ℕ} (h : p.jt a < ⊤) :
    a ≤ p.cnt (p.jt a).toNNReal := by
  rw [← p.jt_le_iff]
  exact (ENNReal.coe_toNNReal h.ne).symm.le

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.cnt_lt_of_lt_jt (p : CPath V) {a : ℕ} {t : ℝ≥0} (h : (t : ℝ≥0∞) < p.jt a) :
    p.cnt t < a := by
  by_contra hle
  exact absurd ((p.jt_le_iff a t).mpr (not_lt.mp hle)) (not_le.mpr h)

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.jt_mono (p : CPath V) {a : ℕ} (h : p.jt (a + 1) < ⊤) : p.jt a ≤ p.jt (a + 1) := by
  have hc := p.cnt_ge_of_jt h
  have := (p.jt_le_iff a (p.jt (a + 1)).toNNReal).mpr (by omega)
  rwa [ENNReal.coe_toNNReal h.ne] at this

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.jt_lt_succ (p : CPath V) {a : ℕ} (h : p.jt (a + 1) < ⊤) : p.jt a < p.jt (a + 1) := by
  classical
  refine lt_of_le_of_ne (p.jt_mono h) fun heq => ?_
  set c := (p.jt (a + 1)).toNNReal with hcdef
  have hc1 : a + 1 ≤ p.cnt c := p.cnt_ge_of_jt h
  have hceq : p.jt (a + 1) = (c : ℝ≥0∞) := (ENNReal.coe_toNNReal h.ne).symm
  have hc0 : 0 < c := by
    rcases eq_or_ne c 0 with h0 | h0
    · exfalso
      have : p.cnt 0 = 0 := by
        unfold CPath.cnt
        have : CDisc p.fn ∩ Iic 0 = ∅ := by
          ext r; simp only [CDisc, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iic,
            Set.mem_empty_iff_false, iff_false, not_and]
          intro h1 h2; exact absurd h2 (not_le.mpr h1.1)
        rw [this]; simp
      rw [h0] at hc1; omega
    · exact pos_iff_ne_zero.mpr h0
  obtain ⟨t, htc, ht⟩ := p.exists_left_gap hc0
  have hlt : (t : ℝ≥0∞) < p.jt a := by rw [heq, hceq]; exact_mod_cast htc
  have h1 := p.cnt_lt_of_lt_jt hlt
  -- at most one discontinuity in `(t, c]`
  have h2 : p.cnt c ≤ p.cnt t + 1 := by
    have hsub : CDisc p.fn ∩ Iic c ⊆ insert c (CDisc p.fn ∩ Iic t) := by
      intro r hr
      by_cases hrc : r = c
      · exact Or.inl hrc
      · right
        refine ⟨hr.1, ?_⟩
        by_contra hrt
        exact ht r hr.1 (not_le.mp hrt) (lt_of_le_of_ne hr.2 hrc)
    exact (Set.ncard_le_ncard hsub ((p.fin t).insert c)).trans (Set.ncard_insert_le _ _)
  omega

/-- The value `p(ς_a)` (junk when `ς_a = ∞`). -/
noncomputable def CPath.jv (p : CPath V) (a : ℕ) : V := p.fn (p.jt a).toNNReal

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.exists_dyUp_eq (p : CPath V) (x : ℝ≥0) :
    ∃ m0 : ℕ, ∀ m, m0 ≤ m → p.fn (dyUp m x) = p.fn x := by
  obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (p.rc x)
  have hT : Tendsto (fun m : ℕ => ((1 / 2 : ℝ≥0)) ^ m) atTop (𝓝 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by
      rw [one_div]; exact inv_lt_one_of_one_lt₀ (by norm_num))
  have hpos : (0 : ℝ≥0) < u' - x := tsub_pos_of_lt hu'
  obtain ⟨m0, hm0⟩ := (hT.eventually_lt_const hpos).exists_forall_of_atTop
  refine ⟨m0, fun m' hm' => ?_⟩
  have h1 := le_dyUp m' x
  have h2 := dyUp_lt m' x
  have h3 : dyUp m' x < u' := by
    refine h2.trans_le ?_
    have := hm0 m' hm'
    calc x + (1 / 2) ^ m' ≤ x + (u' - x) := by gcongr
      _ = u' := add_tsub_cancel_of_le hu'.le
  exact hsub ⟨h1, h3⟩

theorem measurable_fn_at {α : Type*} [MeasurableSpace α] (P : α → CPath V) (hP : Measurable P)
    (g : α → ℝ≥0) (hg : Measurable g) : Measurable fun a => (P a).fn (g a) := by
  have hF : ∀ m : ℕ, Measurable fun a => (P a).fn (dyUp m (g a)) := by
    intro m
    have h1 : Measurable fun a => (⌈g a * 2 ^ m⌉₊, P a) :=
      ((Nat.measurable_ceil.comp (hg.mul_const _)).prodMk hP)
    have h2 : Measurable fun q : ℕ × CPath V => q.2.fn ((q.1 : ℝ≥0) / 2 ^ m) :=
      measurable_from_prod_countable_right fun k => CPath.measurable_eval ((k : ℝ≥0) / 2 ^ m)
    exact h2.comp h1
  refine measurable_to_countable' fun v => ?_
  have : (fun a => (P a).fn (g a)) ⁻¹' {v} =
      ⋃ m : ℕ, ⋂ m' : ℕ, ⋂ (_ : m ≤ m'), (fun a => (P a).fn (dyUp m' (g a))) ⁻¹' {v} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_iInter]
    obtain ⟨m0, hm0⟩ := (P a).exists_dyUp_eq (g a)
    constructor
    · intro hv
      exact ⟨m0, fun m' hm' => (hm0 m' hm').trans hv⟩
    · rintro ⟨m, hm⟩
      rw [← hm0 (max m m0) (le_max_right _ _)]
      exact hm _ (le_max_left _ _)
  rw [this]
  exact MeasurableSet.iUnion fun m => MeasurableSet.iInter fun m' => MeasurableSet.iInter fun _ =>
    hF m' (measurableSet_singleton v)

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.fn_eq_jv (p : CPath V) (s : ℝ≥0) : p.fn s = p.jv (p.cnt s) := by
  have hle : p.jt (p.cnt s) ≤ (s : ℝ≥0∞) := (p.jt_le_iff _ _).mpr le_rfl
  have hfin : p.jt (p.cnt s) < ⊤ := hle.trans_lt ENNReal.coe_lt_top
  set c' := (p.jt (p.cnt s)).toNNReal with hc'
  have hc's : c' ≤ s := by
    have : (c' : ℝ≥0∞) ≤ s := by rwa [hc', ENNReal.coe_toNNReal hfin.ne]
    exact_mod_cast this
  have hcnt : p.cnt s ≤ p.cnt c' := p.cnt_ge_of_jt hfin
  symm
  show p.fn c' = p.fn s
  refine (eq_of_no_disc p.rc hc's (fun r hr hd => ?_)).symm
  have h2 : p.cnt c' + 1 ≤ p.cnt r := by
    have hsub : insert r (CDisc p.fn ∩ Iic c') ⊆ CDisc p.fn ∩ Iic r := by
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨hd, le_rfl⟩
      · exact ⟨hx.1, hx.2.trans hr.1.le⟩
    have := Set.ncard_le_ncard hsub (p.fin r)
    rwa [Set.ncard_insert_of_notMem (fun hh => absurd hh.2 (not_le.mpr hr.1)) (p.fin c')] at this
  have := p.cnt_mono hr.2
  omega

/-- The jump list `J(ℓ, p) = (ℓ, (ς_a, p(ς_a))_a)`. -/
noncomputable def CPath.jumpList (p : CPath V) : ℝ≥0∞ × (ℕ → ℝ≥0∞ × V) :=
  (p.len, fun a => (p.jt a, p.jv a))

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
/-- The jump list determines the path. Paths (b). -/
theorem CPath.jumpList_injective : Function.Injective (fun p : CPath V => p.jumpList) := by
  intro p q h
  have hlen : p.len = q.len := congrArg Prod.fst h
  have hj : ∀ a, p.jt a = q.jt a := fun a => congrArg Prod.fst (congrFun (congrArg Prod.snd h) a)
  have hv : ∀ a, p.jv a = q.jv a := fun a => congrArg Prod.snd (congrFun (congrArg Prod.snd h) a)
  have hcnt : ∀ s, p.cnt s = q.cnt s := fun s => by
    apply le_antisymm
    · rw [← q.jt_le_iff, ← hj]; exact (p.jt_le_iff _ _).mpr le_rfl
    · rw [← p.jt_le_iff, hj]; exact (q.jt_le_iff _ _).mpr le_rfl
  have hfn : p.fn = q.fn := funext fun s => by rw [p.fn_eq_jv, q.fn_eq_jv, hcnt, hv]
  cases p; cases q
  simp only at hlen hfn
  subst hlen; subst hfn; rfl

theorem CPath.measurable_jv (a : ℕ) : Measurable (fun p : CPath V => p.jv a) :=
  measurable_fn_at id measurable_id _ (ENNReal.measurable_toNNReal.comp (CPath.measurable_jt a))

end ElboimSly.Cyclic

end
