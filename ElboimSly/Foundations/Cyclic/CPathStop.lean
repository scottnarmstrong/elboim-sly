/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CPathJump
public import ElboimSly.Foundations.SRW.Stopping
public import Mathlib

/-!
# Stopped paths and stopping times

Paths (c).

`CPath.stop p t` is the path `p(· ∧ t)` of length `t`. For a process `Y` whose paths lie in
`CPath V`, adapted to a filtration, and a stopping time `T`, the map `ω ↦ (T, Y(· ∧ T))` is
`F_T`-measurable (Mathlib's `IsStoppingTime.measurableSpace`). We state it as a map on all of `Ω`
by using `stopReal T` (the finite part of `T`, `0` on `{T = ⊤}`) as the stopping level; on
`{T < ⊤}` this is the written proof statement, and on `{T = ⊤}` the junk value is the constant
path `Y(0)` of length `0`, which is `F_T`-measurable as well.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {V : Type*}

/-- The stopped path `p(· ∧ t)`, of length `t`. -/
def CPath.stop (p : CPath V) (t : ℝ≥0) : CPath V where
  len := t
  fn s := p.fn (min s t)
  rc s := by
    rcases lt_or_ge s t with hst | hts
    · have h1 : ∀ᶠ u in 𝓝[≥] s, u < t :=
        eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hst)
      filter_upwards [p.rc s, h1] with u hu hut
      rw [min_eq_left hut.le, min_eq_left hst.le]; exact hu
    · filter_upwards [self_mem_nhdsWithin (a := s) (s := Ici s)] with u hu
      rw [min_eq_right (hts.trans hu), min_eq_right hts]
  fin T := by
    refine (p.fin T).subset fun s hs => ⟨?_, hs.2⟩
    obtain ⟨hs0, hs1⟩ := hs.1
    refine ⟨hs0, fun hev => hs1 ?_⟩
    rcases le_or_gt s t with hst | hts
    · filter_upwards [hev, self_mem_nhdsWithin (a := s) (s := Iio s)] with u hu hus
      have hut : u ≤ t := le_trans (le_of_lt (Set.mem_Iio.mp hus)) hst
      rw [min_eq_left hut, min_eq_left hst]
      exact hu
    · have h1 : ∀ᶠ u in 𝓝[<] s, t < u :=
        eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hts)
      filter_upwards [h1] with u hu
      rw [min_eq_right hu.le, min_eq_right hts.le]
  const s s' h h' := by
    have h1 : t ≤ s := by exact_mod_cast h
    have h2 : t ≤ s' := by exact_mod_cast h'
    simp only [min_eq_right h1, min_eq_right h2]

@[simp] theorem CPath.stop_fn (p : CPath V) (t s : ℝ≥0) : (p.stop t).fn s = p.fn (min s t) := rfl

/-- Right-continuity at dyadic approximations from above: all points between `x` and
`dyUp m x` see the value at `x` for large `m`. -/
theorem CPath.exists_dyUp_between (p : CPath V) (x : ℝ≥0) :
    ∃ m0 : ℕ, ∀ m, m0 ≤ m → ∀ s, x ≤ s → s ≤ dyUp m x → p.fn s = p.fn x := by
  obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (p.rc x)
  have hT : Tendsto (fun m : ℕ => ((1 / 2 : ℝ≥0)) ^ m) atTop (𝓝 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by
      rw [one_div]; exact inv_lt_one_of_one_lt₀ (by norm_num))
  have hpos : (0 : ℝ≥0) < u' - x := tsub_pos_of_lt hu'
  obtain ⟨m0, hm0⟩ := (hT.eventually_lt_const hpos).exists_forall_of_atTop
  refine ⟨m0, fun m' hm' s hxs hs => ?_⟩
  have h2 := dyUp_lt m' x
  have h3 : dyUp m' x < u' := by
    refine h2.trans_le ?_
    have := hm0 m' hm'
    calc x + (1 / 2) ^ m' ≤ x + (u' - x) := by gcongr
      _ = u' := add_tsub_cancel_of_le hu'.le
  exact hsub ⟨hxs, lt_of_le_of_lt hs h3⟩

section measurability

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
variable {Ω : Type*}

/-- A path evaluated at a bounded random time, in a σ-algebra `𝒢` for which all the coordinates
at times `≤ C` are measurable. -/
theorem measurable_fn_bounded {𝒢 : MeasurableSpace Ω} (P : Ω → CPath V) (σ : Ω → ℝ≥0) (C : ℝ≥0)
    (hσ : Measurable[𝒢] σ) (hC : ∀ ω, σ ω ≤ C)
    (hP : ∀ t ≤ C, Measurable[𝒢] fun ω => (P ω).fn t) :
    Measurable[𝒢] fun ω => (P ω).fn (σ ω) := by
  let _ : MeasurableSpace Ω := 𝒢
  have hF : ∀ m : ℕ, Measurable fun ω => (P ω).fn (min (dyUp m (σ ω)) C) := by
    intro m
    have h1 : Measurable fun ω => (⌈σ ω * 2 ^ m⌉₊, ω) :=
      ((Nat.measurable_ceil.comp (hσ.mul_const _)).prodMk measurable_id)
    have h2 : Measurable fun q : ℕ × Ω => (P q.2).fn (min ((q.1 : ℝ≥0) / 2 ^ m) C) :=
      measurable_from_prod_countable_right fun k => hP (min ((k : ℝ≥0) / 2 ^ m) C) (min_le_right _ _)
    exact h2.comp h1
  refine measurable_to_countable' fun v => ?_
  have : (fun ω => (P ω).fn (σ ω)) ⁻¹' {v} =
      ⋃ m : ℕ, ⋂ m' : ℕ, ⋂ (_ : m ≤ m'),
        (fun ω => (P ω).fn (min (dyUp m' (σ ω)) C)) ⁻¹' {v} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_iInter]
    obtain ⟨m0, hm0⟩ := (P ω).exists_dyUp_between (σ ω)
    have key : ∀ m, m0 ≤ m → (P ω).fn (min (dyUp m (σ ω)) C) = (P ω).fn (σ ω) := fun m hm =>
      hm0 m hm _ (le_min (le_dyUp m _) (hC ω)) (min_le_left _ _)
    constructor
    · intro hv
      exact ⟨m0, fun m' hm' => (key m' hm').trans hv⟩
    · rintro ⟨m, hm⟩
      rw [← key (max m m0) (le_max_right _ _)]
      exact hm _ (le_max_left _ _)
  rw [this]
  exact MeasurableSet.iUnion fun m => MeasurableSet.iInter fun m' => MeasurableSet.iInter fun _ =>
    hF m' (measurableSet_singleton v)

end measurability

section stopping

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {f : Filtration ℝ≥0 mΩ} {T : Ω → WithTop ℝ≥0}

theorem measurable_stopReal_iSup (hT : IsStoppingTime f T) :
    Measurable[⨆ t, f t] (ElboimSly.SRW.stopReal T) := by
  have hle : ∀ t, f t ≤ ⨆ t, f t := fun t => le_iSup f t
  refine measurable_of_Iic fun c => ?_
  have h1 : MeasurableSet[⨆ t, f t] {ω | T ω ≤ (c : WithTop ℝ≥0)} := hle c _ (hT c)
  have h2 : MeasurableSet[⨆ t, f t] {ω | T ω = ⊤} := by
    have : {ω | T ω = ⊤} = (⋃ n : ℕ, {ω | T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)})ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, not_exists, not_le]
      constructor
      · intro h n; rw [h]; exact WithTop.coe_lt_top _
      · intro h
        by_contra hne
        obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hne
        obtain ⟨n, hn⟩ := exists_nat_ge a
        have := h n
        rw [← ha] at this
        exact absurd (WithTop.coe_le_coe.2 hn) (not_le.2 this)
    rw [this]
    exact (MeasurableSet.iUnion fun n : ℕ => hle _ _ (hT n)).compl
  have : ElboimSly.SRW.stopReal T ⁻¹' Iic c = {ω | T ω ≤ (c : WithTop ℝ≥0)} ∪ {ω | T ω = ⊤} := by
    ext ω
    simp only [ElboimSly.SRW.stopReal, mem_preimage, mem_Iic, mem_union, mem_ofPred_eq]
    cases hh : T ω using WithTop.recTopCoe with
    | top => simp
    | coe a =>
      change a ≤ c ↔ (a : WithTop ℝ≥0) ≤ (c : WithTop ℝ≥0) ∨ (a : WithTop ℝ≥0) = ⊤
      exact ⟨fun h => Or.inl (WithTop.coe_le_coe.2 h),
        fun h => h.elim WithTop.coe_le_coe.1 (fun h => absurd h WithTop.coe_ne_top)⟩
  rw [this]
  exact h1.union h2

theorem measurable_stopReal_stop (hT : IsStoppingTime f T) :
    Measurable[hT.measurableSpace] (ElboimSly.SRW.stopReal T) := by
  refine measurable_of_Iic fun c => ?_
  have hm : Measurable[⨆ t, f t] (ElboimSly.SRW.stopReal T) := measurable_stopReal_iSup hT
  refine ⟨hm measurableSet_Iic, fun i => ?_⟩
  have : ElboimSly.SRW.stopReal T ⁻¹' Iic c ∩ {ω | T ω ≤ (i : WithTop ℝ≥0)} =
      {ω | T ω ≤ ((min c i : ℝ≥0) : WithTop ℝ≥0)} ∩ {ω | T ω ≤ (i : WithTop ℝ≥0)} := by
    ext ω
    simp only [ElboimSly.SRW.stopReal, mem_inter_iff, mem_preimage, mem_Iic, mem_ofPred_eq]
    cases hh : T ω using WithTop.recTopCoe with
    | top => constructor <;> rintro ⟨_, h⟩ <;> exact absurd (top_le_iff.mp h) WithTop.coe_ne_top
    | coe a =>
      change (a ≤ c ∧ (a : WithTop ℝ≥0) ≤ i) ↔ (a : WithTop ℝ≥0) ≤ ((min c i : ℝ≥0) : WithTop ℝ≥0) ∧
        (a : WithTop ℝ≥0) ≤ i
      simp only [WithTop.coe_le_coe, le_min_iff]
      tauto
  rw [this]
  exact (f.mono (min_le_right c i) _ (hT _)).inter (hT i)

/-- Paths (c). Let `Y` be a process whose paths lie in `CPath V`, adapted to a
filtration `f`, and `T` a stopping time. Then `ω ↦ (T, Y(· ∧ T))` is `F_T`-measurable (a total
function: on `{T = ⊤}` the junk value is the length-`0` path `Y(0)`). Hence `Y(T)`, `ς_a(Y) ∧ T` and
`1{ς_a(Y) ≤ T}` are `F_T`-measurable on `{T < ⊤}`. -/
theorem measurable_stoppedPath (Y : Ω → CPath V)
    (hY : ∀ s, Measurable[f s] fun ω => (Y ω).fn s) (hT : IsStoppingTime f T) :
    Measurable[hT.measurableSpace] fun ω => (Y ω).stop (ElboimSly.SRW.stopReal T ω) := by
  rw [@CPath.measurable_iff V _ Ω hT.measurableSpace _]
  refine ⟨?_, fun s => ?_⟩
  · exact measurable_coe_nnreal_ennreal.comp (measurable_stopReal_stop hT)
  · simp only [CPath.stop_fn]
    refine @measurable_to_countable' V Ω _ _ hT.measurableSpace _ fun v => ?_
    have hle : ∀ t, f t ≤ ⨆ t, f t := fun t => le_iSup f t
    set g : Ω → V := fun ω => (Y ω).fn (min s (ElboimSly.SRW.stopReal T ω)) with hg
    have hg1 : Measurable[⨆ t, f t] g :=
      measurable_fn_bounded (𝒢 := ⨆ t, f t) Y _ s
        (measurable_const.min (measurable_stopReal_iSup hT)) (fun ω => min_le_left _ _)
        (fun t _ => (hY t).mono (hle t) le_rfl)
    refine ⟨hg1 (measurableSet_singleton v), fun i => ?_⟩
    have hgi : Measurable[f i] fun ω => (Y ω).fn (min s (ElboimSly.SRW.stopMin T i ω)) :=
      measurable_fn_bounded (𝒢 := f i) Y _ i
        (measurable_const.min (hT.measurable_stopMin i))
        (fun ω => (min_le_right _ _).trans (min_le_right _ _))
        (fun t ht => (hY t).mono (f.mono ht) le_rfl)
    have : g ⁻¹' {v} ∩ {ω | T ω ≤ (i : WithTop ℝ≥0)} =
        (fun ω => (Y ω).fn (min s (ElboimSly.SRW.stopMin T i ω))) ⁻¹' {v} ∩
          {ω | T ω ≤ (i : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq, hg]
      cases hh : T ω using WithTop.recTopCoe with
      | top => constructor <;> rintro ⟨_, h⟩ <;> exact absurd (top_le_iff.mp h) WithTop.coe_ne_top
      | coe a =>
        have e1 : ElboimSly.SRW.stopReal T ω = a := by unfold ElboimSly.SRW.stopReal; rw [hh]; rfl
        have e2 : ElboimSly.SRW.stopMin T i ω = min a i := by
          unfold ElboimSly.SRW.stopMin; rw [hh]; rfl
        rw [e1, e2]
        constructor
        · rintro ⟨h1, h2⟩
          have ha : a ≤ i := WithTop.coe_le_coe.1 h2
          exact ⟨by rwa [min_eq_left ha], h2⟩
        · rintro ⟨h1, h2⟩
          have ha : a ≤ i := WithTop.coe_le_coe.1 h2
          exact ⟨by rwa [min_eq_left ha] at h1, h2⟩
    rw [this]
    exact (hgi (measurableSet_singleton v)).inter (hT i)

end stopping

end ElboimSly.Cyclic

end
