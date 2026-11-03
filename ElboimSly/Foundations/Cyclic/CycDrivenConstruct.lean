/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenExists
public import ElboimSly.Foundations.Cyclic.CycPathType
public import Mathlib

/-!
# Construction of the driven path from a locally finite event set

Basic properties of world-lines (c). For `E` satisfying `EvtSet` the driven path exists
(`exists_driven_of_evtSet`), with all jumps in `E`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The properties of the event set `E_k`: locally finite, and outside `E` nothing moves the path. -/
structure EvtSet (β : ℝ) [Fact (0 < β)] (Q : Set (I × RingSpace d β)) (δ : CycData I d)
    (X : CPath (Fin d → ℤ)) (a : ℝ≥0) (E : Set ℝ≥0) : Prop where
  pos : ∀ r ∈ E, 0 < r
  fin : ∀ T, (E ∩ Iic T).Finite
  noJump : ∀ r, 0 < r → r ∉ E → X.left (a + r) = X.fn (a + r)
  noRing : ∀ r, 0 < r → r ∉ E → ∀ e : Edge d, (δ.copy, (e, δ.clock β r)) ∉ Q
  shift : ∀ r' r, 0 < r' → r' < r → r' ∈ E → δ.clock β r' = δ.clock β r → r ∈ E

variable {R Q : Set (I × RingSpace d β)} {δ : CycData I d} {X : CPath (Fin d → ℤ)} {a : ℝ≥0}
  {E : Set ℝ≥0}

omit [MeasurableSpace I] in
/-- Outside `E`, a path with jumps in `E` that does not move satisfies the rules. -/
theorem EvtSet.rule_stay (hE : EvtSet β Q δ X a E) {p : CPath (Fin d → ℤ)}
    (hp : ∀ s ∈ CDisc p.fn, s ∈ E) {r : ℝ≥0} (hr : 0 < r) (hrE : r ∉ E)
    (hst : p.fn r = p.left r) : DrvRule β R Q δ X a p r := by
  unfold DrvRule
  rw [hst]
  refine RuleFn.of_stay ?_ ?_
  · rintro ⟨e, -, hmem⟩
    rcases hmem with hmem | ⟨r', h0, h1, hne, hx1, hx2, hx3⟩
    · exact hE.noRing r hr hrE e hmem
    · have hcd : r' ∈ CDisc p.fn := (p.mem_CDisc_iff h0).2 hne
      exact hrE (hE.shift r' r h0 h1 (hp r' hcd) hx2.symm)
  · exact not_not.mpr (hE.noJump r hr hrE)

theorem exists_gap_of_finite {E : Set ℝ≥0} {e : ℝ≥0} (hE : (E ∩ Iic e).Finite) (he : 0 < e) :
    ∃ t, t < e ∧ ∀ r ∈ E, t < r → r < e → False := by
  classical
  have hF : (E ∩ Iio e).Finite := hE.subset fun r hr => ⟨hr.1, hr.2.le⟩
  by_cases hne : (E ∩ Iio e).Nonempty
  · refine ⟨hF.toFinset.max' (by simpa using hne), ?_, fun r hr h1 h2 => ?_⟩
    · have := hF.toFinset.max'_mem (by simpa using hne)
      simp
    · have hrF : r ∈ hF.toFinset := by simpa using ⟨hr, h2⟩
      exact absurd (hF.toFinset.le_max' r hrF) (not_le.mpr h1)
  · exact ⟨0, he, fun r hr _ h2 => hne ⟨r, hr, h2⟩⟩

/-- Extend a path by a new value from time `e` on. -/
noncomputable def CPath.extendAt {V : Type*} (p : CPath V) (e : ℝ≥0) (v : V) : CPath V where
  len := ⊤
  fn r := open scoped Classical in if r < e then p.fn r else v
  rc s := by
    classical
    rcases lt_or_ge s e with h | h
    · have h1 : ∀ᶠ u in 𝓝[≥] s, u < e :=
        eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds h)
      filter_upwards [p.rc s, h1] with u hu hu'
      simp only [ite_eq_left hu', ite_eq_left h]; exact hu
    · filter_upwards [self_mem_nhdsWithin (a := s) (s := Ici s)] with u hu
      simp only [ite_eq_right (not_lt.mpr (h.trans hu)), ite_eq_right (not_lt.mpr h)]
  fin T := by
    classical
    refine ((p.fin T).insert e).subset fun s hs => ?_
    obtain ⟨⟨hs0, hs1⟩, hsT⟩ := hs
    by_cases hse : s = e
    · exact Or.inl hse
    · right
      refine ⟨⟨hs0, fun hev => hs1 ?_⟩, hsT⟩
      rcases lt_or_gt_of_ne hse with h | h
      · filter_upwards [hev, self_mem_nhdsWithin (a := s) (s := Iio s)] with u hu hus
        have hue : u < e := (Set.mem_Iio.mp hus).trans h
        simp only [ite_eq_left hue, ite_eq_left h]
        simpa [ite_eq_left hue, ite_eq_left h] using hu
      · have h1 : ∀ᶠ u in 𝓝[<] s, e < u :=
          eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds h)
        filter_upwards [h1] with u hu
        simp only [ite_eq_right (not_lt.mpr hu.le), ite_eq_right (not_lt.mpr h.le)]
  const s s' h _ := absurd h (by simp)

theorem CPath.extendAt_fn_lt {V : Type*} (p : CPath V) (e : ℝ≥0) (v : V) {r : ℝ≥0} (h : r < e) :
    (p.extendAt e v).fn r = p.fn r := by
  simp [CPath.extendAt, ite_eq_left h]

theorem CPath.extendAt_fn_ge {V : Type*} (p : CPath V) (e : ℝ≥0) (v : V) {r : ℝ≥0} (h : e ≤ r) :
    (p.extendAt e v).fn r = v := by
  simp [CPath.extendAt, ite_eq_right (not_lt.mpr h)]

theorem CPath.CDisc_extendAt {V : Type*} (p : CPath V) (e : ℝ≥0) (v : V) {s : ℝ≥0}
    (hs : s ∈ CDisc (p.extendAt e v).fn) : s = e ∨ (s < e ∧ s ∈ CDisc p.fn) := by
  classical
  by_cases hse : s = e
  · exact Or.inl hse
  · right
    obtain ⟨hs0, hs1⟩ := hs
    rcases lt_or_gt_of_ne hse with h | h
    · refine ⟨h, hs0, fun hev => hs1 ?_⟩
      filter_upwards [hev, self_mem_nhdsWithin (a := s) (s := Iio s)] with u hu hus
      have hue : u < e := (Set.mem_Iio.mp hus).trans h
      rw [CPath.extendAt_fn_lt p e v hue, CPath.extendAt_fn_lt p e v h]; exact hu
    · exfalso
      refine hs1 ?_
      have h1 : ∀ᶠ u in 𝓝[<] s, e < u :=
        eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds h)
      filter_upwards [h1] with u hu
      rw [CPath.extendAt_fn_ge p e v hu.le, CPath.extendAt_fn_ge p e v h.le]

end ElboimSly.Cyclic

end
