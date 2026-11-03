/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRecMeasStop
public import ElboimSly.Foundations.Cyclic.DrivenMeas
public import Mathlib

/-!
# Path extension by one event

The environment scheme of a plan (the path `p'`: `p` on `[0, r)`, `w` on `[r, r + s*)`, and the new
value `v` at `r + s*` and after).

`CPath.extend p T v` is the path of length `T` equal to `p` on `[0, T)` and to the guarded value
`CPath.extVal p T v` on `[T, ∞)`. If `p` is constant after its length `r ≤ T` this is the written proof's
`p'`. The guard makes the construction total: the jump at `T` is only kept if it has `ℓ¹`-size `1`
(otherwise the value is the left limit `p(T-)`, so there is no jump), hence
`CycPath.extend p T v` is a `CycPath` for every `p : CycPath d`, `T` and `v` without any
hypothesis (`CPath.UnitJumps.extend`). The correctness side (that for the states reached by the
recursion the guard is true and `p(T-) = w`) belongs to the environment scheme.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ}

theorem CPath.left_zero {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    (p : CPath V) : p.left 0 = p.jv 0 := by
  unfold CPath.left
  have : CDisc p.fn ∩ Iio (0 : ℝ≥0) = ∅ := by
    ext s; simp
  simp

theorem CPath.left_eq_leftVal_of_pos (p : CPath (Fin d → ℤ)) {r : ℝ≥0} (hr : 0 < r) :
    p.left r = leftVal p.fn r :=
  (leftVal_eq_of_eventually hr (p.eventually_left hr)).symm

/-- The guarded new value: `v` if it is at `ℓ¹`-distance `1` from `p(T-)`, and `p(T-)` otherwise. -/
noncomputable def CPath.extVal (p : CPath (Fin d → ℤ)) (T : ℝ≥0) (v : Fin d → ℤ) : Fin d → ℤ :=
  open scoped Classical in
  if 0 < T ∧ ∑ i, |v i - p.left T i| = 1 then v else p.left T

/-- The path of length `T`: `p` on `[0, T)` and the guarded value from `T` on. -/
noncomputable def CPath.extend (p : CPath (Fin d → ℤ)) (T : ℝ≥0) (v : Fin d → ℤ) :
    CPath (Fin d → ℤ) where
  len := T
  fn t := open scoped Classical in if T ≤ t then p.extVal T v else p.fn t
  rc s := by
    classical
    rcases le_or_gt T s with hTs | hsT
    · filter_upwards [self_mem_nhdsWithin (a := s) (s := Ici s)] with u hu
      simp [hTs.trans hu, hTs]
    · have h1 : ∀ᶠ u in 𝓝[≥] s, u < T :=
        eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hsT)
      filter_upwards [p.rc s, h1] with u hu hut
      simp [not_le.2 hut, not_le.2 hsT]
      exact hu
  fin X := by
    classical
    refine ((p.fin X).union (Set.finite_singleton T)).subset fun s hs => ?_
    obtain ⟨⟨hs0, hs1⟩, hsX⟩ := hs
    rcases lt_trichotomy s T with hsT | rfl | hTs
    · refine Or.inl ⟨⟨hs0, fun hev => hs1 ?_⟩, hsX⟩
      have h1 : ∀ᶠ u in 𝓝[<] s, u < T :=
        eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hsT)
      filter_upwards [hev, h1, h1] with u hu hut _
      simp [not_le.2 hut, not_le.2 hsT]
      exact hu
    · exact Or.inr rfl
    · exfalso
      apply hs1
      have h1 : ∀ᶠ u in 𝓝[<] s, T < u := eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hTs)
      filter_upwards [h1] with u hu
      simp [hu.le, hTs.le]
  const s s' h h' := by
    classical
    have h1 : T ≤ s := by exact_mod_cast h
    have h2 : T ≤ s' := by exact_mod_cast h'
    simp [h1, h2]

@[simp] theorem CPath.extend_len (p : CPath (Fin d → ℤ)) (T : ℝ≥0) (v : Fin d → ℤ) :
    (p.extend T v).len = T := rfl

theorem CPath.extend_fn_of_lt (p : CPath (Fin d → ℤ)) (T : ℝ≥0) (v : Fin d → ℤ) {t : ℝ≥0}
    (ht : t < T) : (p.extend T v).fn t = p.fn t := by
  classical
  show (if T ≤ t then _ else _) = _
  simp [not_le.2 ht]

theorem CPath.extend_fn_of_le (p : CPath (Fin d → ℤ)) (T : ℝ≥0) (v : Fin d → ℤ) {t : ℝ≥0}
    (ht : T ≤ t) : (p.extend T v).fn t = p.extVal T v := by
  classical
  show (if T ≤ t then _ else _) = _
  simp [ht]

theorem CPath.left_extend_of_lt (p : CPath (Fin d → ℤ)) (T : ℝ≥0) (v : Fin d → ℤ) {s : ℝ≥0}
    (hs : 0 < s) (hsT : s ≤ T) : (p.extend T v).left s = p.left s := by
  refine (p.extend T v).left_eq_of_eventually hs ?_
  have h1 : ∀ᶠ u in 𝓝[<] s, u < T := by
    refine eventually_nhdsWithin_of_forall fun u hu => lt_of_lt_of_le hu hsT
  filter_upwards [h1, p.eventually_left hs] with u hu hu'
  rw [p.extend_fn_of_lt T v hu]
  exact hu'

theorem CPath.left_extend_self (p : CPath (Fin d → ℤ)) {T : ℝ≥0} (hT : 0 < T) (v : Fin d → ℤ) :
    (p.extend T v).left T = p.left T :=
  p.left_extend_of_lt T v hT le_rfl

theorem CPath.extend_fn_self (p : CPath (Fin d → ℤ)) (T : ℝ≥0) (v : Fin d → ℤ) :
    (p.extend T v).fn T = p.extVal T v :=
  p.extend_fn_of_le T v le_rfl

theorem CPath.UnitJumps.extend {p : CPath (Fin d → ℤ)} (hp : p.UnitJumps) (T : ℝ≥0)
    (v : Fin d → ℤ) : (p.extend T v).UnitJumps := by
  classical
  intro s hs
  have hs0 : 0 < s := hs.1
  rcases lt_trichotomy s T with hsT | rfl | hTs
  · have hsd : s ∈ CDisc p.fn := by
      refine ⟨hs0, fun hev => hs.2 ?_⟩
      have h1 : ∀ᶠ u in 𝓝[<] s, u < T :=
        eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hsT)
      filter_upwards [hev, h1] with u hu hut
      rw [p.extend_fn_of_lt T v hut, p.extend_fn_of_lt T v hsT]
      exact hu
    rw [p.left_extend_of_lt T v hs0 hsT.le, p.extend_fn_of_lt T v hsT]
    exact hp s hsd
  · rw [p.left_extend_self hs0, p.extend_fn_self]
    unfold CPath.extVal
    split_ifs with hg
    · exact hg.2
    · exfalso
      apply hs.2
      filter_upwards [p.eventually_left hs0, eventually_nhdsWithin_of_forall
        (fun u (hu : u ∈ Iio s) => hu)] with u hu hus
      rw [p.extend_fn_of_lt s v hus, hu, p.extend_fn_self]
      simp [CPath.extVal, hg]
  · exfalso
    apply hs.2
    have h1 : ∀ᶠ u in 𝓝[<] s, T < u := eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hTs)
    filter_upwards [h1] with u hu
    rw [p.extend_fn_of_le T v hu.le, p.extend_fn_of_le T v hTs.le]

/-- The extension of a nearest-neighbour path (total, see the module docstring). -/
noncomputable def CycPath.extend (p : CycPath d) (T : ℝ≥0) (v : Fin d → ℤ) : CycPath d :=
  ⟨p.1.extend T v, p.2.extend T v⟩

@[simp] theorem CycPath.extend_len (p : CycPath d) (T : ℝ≥0) (v : Fin d → ℤ) :
    (p.extend T v).1.len = T := rfl

/-! ### Measurability -/

theorem measurable_cpath_left : Measurable fun q : CPath (Fin d → ℤ) × ℝ≥0 => q.1.left q.2 := by
  have h1 : Measurable fun q : CPath (Fin d → ℤ) × ℝ≥0 => leftVal q.1.fn q.2 :=
    measurable_leftVal_at (Q := fun q : CPath (Fin d → ℤ) × ℝ≥0 => q.1) measurable_fst
      measurable_snd
  have h2 : Measurable fun q : CPath (Fin d → ℤ) × ℝ≥0 => q.1.jv 0 :=
    (CPath.measurable_jv 0).comp measurable_fst
  have : (fun q : CPath (Fin d → ℤ) × ℝ≥0 => q.1.left q.2) = fun q =>
      if q.2 = 0 then q.1.jv 0 else leftVal q.1.fn q.2 := by
    funext q
    by_cases h : q.2 = 0
    · simp only [h, ite_true]
      have : q.1.left 0 = q.1.jv 0 := q.1.left_zero
      exact this
    · simp only [h, ite_false]
      exact q.1.left_eq_leftVal_of_pos (pos_iff_ne_zero.2 h)
  rw [this]
  exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) h2 h1

theorem measurable_extVal : Measurable fun q : CPath (Fin d → ℤ) × ℝ≥0 × (Fin d → ℤ) =>
    q.1.extVal q.2.1 q.2.2 := by
  classical
  have hl : Measurable fun q : CPath (Fin d → ℤ) × ℝ≥0 × (Fin d → ℤ) => q.1.left q.2.1 :=
    measurable_cpath_left.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hv : Measurable fun q : CPath (Fin d → ℤ) × ℝ≥0 × (Fin d → ℤ) => q.2.2 :=
    measurable_snd.comp measurable_snd
  have hset : MeasurableSet {q : CPath (Fin d → ℤ) × ℝ≥0 × (Fin d → ℤ) |
      0 < q.2.1 ∧ ∑ i, |q.2.2 i - q.1.left q.2.1 i| = 1} := by
    have h0 : MeasurableSet {q : CPath (Fin d → ℤ) × ℝ≥0 × (Fin d → ℤ) | 0 < q.2.1} :=
      measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)
    have hpair : Measurable fun q : CPath (Fin d → ℤ) × ℝ≥0 × (Fin d → ℤ) =>
        (q.2.2, q.1.left q.2.1) := hv.prodMk hl
    have hS : MeasurableSet {z : (Fin d → ℤ) × (Fin d → ℤ) | ∑ i, |z.1 i - z.2 i| = 1} :=
      (Set.to_countable _).measurableSet
    exact h0.inter (hpair hS)
  unfold CPath.extVal
  exact Measurable.ite hset hv hl

theorem measurable_cpath_extend : Measurable fun q : CPath (Fin d → ℤ) × ℝ≥0 × (Fin d → ℤ) =>
    q.1.extend q.2.1 q.2.2 := by
  classical
  rw [CPath.measurable_iff]
  refine ⟨measurable_coe_nnreal_ennreal.comp (measurable_fst.comp measurable_snd), fun t => ?_⟩
  have : (fun q : CPath (Fin d → ℤ) × ℝ≥0 × (Fin d → ℤ) => (q.1.extend q.2.1 q.2.2).fn t) =
      fun q => if q.2.1 ≤ t then q.1.extVal q.2.1 q.2.2 else q.1.fn t := rfl
  rw [this]
  exact Measurable.ite (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const)
    measurable_extVal (CPath.measurable_eval t |>.comp measurable_fst)

theorem measurable_cycPath_extend :
    Measurable fun q : CycPath d × ℝ≥0 × (Fin d → ℤ) => q.1.extend q.2.1 q.2.2 := by
  refine Measurable.subtype_mk ?_
  exact measurable_cpath_extend.comp ((measurable_subtype_coe.comp measurable_fst).prodMk
    measurable_snd)

end ElboimSly.Cyclic

end
