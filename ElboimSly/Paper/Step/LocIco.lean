/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Sets locally of type `[l, r)`

Structure of relaxed times; stopping times (a), second part.

`IsLocIco U` says that for every `M`, `U ∩ [0, M]` is a finite union of intervals `[l, r)`, `l < r`
(intersected with `[0, M]`). Finite intersections are of the same type, and if `U ∩ (c, ∞)` is
non-empty, `inf (U ∩ (c, ∞)) = min (U ∩ [c, ∞)) ∈ U`.
-/

@[expose] public section

open Set

namespace ElboimSly.Paper

/-- A set that is locally of type `[l, r)`. -/
def IsLocIco (U : Set ℝ) : Prop :=
  ∀ M : ℝ, ∃ L : Finset (ℝ × ℝ), (∀ p ∈ L, p.1 < p.2) ∧
    U ∩ Icc 0 M = (⋃ p ∈ L, Ico p.1 p.2) ∩ Icc 0 M

theorem IsLocIco.inter {U V : Set ℝ} (hU : IsLocIco U) (hV : IsLocIco V) : IsLocIco (U ∩ V) := by
  classical
  intro M
  obtain ⟨L, hL, hLe⟩ := hU M
  obtain ⟨L', hL', hLe'⟩ := hV M
  refine ⟨((L ×ˢ L').image fun q => (max q.1.1 q.2.1, min q.1.2 q.2.2)).filter
    (fun p => p.1 < p.2), fun p hp => (Finset.mem_filter.1 hp).2, ?_⟩
  ext t
  have h1 : t ∈ U ∩ Icc 0 M ↔ t ∈ (⋃ p ∈ L, Ico p.1 p.2) ∩ Icc 0 M := by rw [hLe]
  have h2 : t ∈ V ∩ Icc 0 M ↔ t ∈ (⋃ p ∈ L', Ico p.1 p.2) ∩ Icc 0 M := by rw [hLe']
  simp only [mem_inter_iff, mem_iUnion, exists_prop, Finset.mem_filter, Finset.mem_image,
    Finset.mem_product, mem_Ico] at h1 h2 ⊢
  constructor
  · rintro ⟨⟨hu, hv⟩, hc⟩
    obtain ⟨⟨p, hp, hpt⟩, -⟩ := h1.1 ⟨hu, hc⟩
    obtain ⟨⟨q, hq, hqt⟩, -⟩ := h2.1 ⟨hv, hc⟩
    refine ⟨⟨(max p.1 q.1, min p.2 q.2), ⟨⟨(p, q), ⟨hp, hq⟩, rfl⟩, ?_⟩, ?_⟩, hc⟩
    · exact lt_of_le_of_lt (max_le hpt.1 hqt.1) (lt_min hpt.2 hqt.2)
    · exact ⟨max_le hpt.1 hqt.1, lt_min hpt.2 hqt.2⟩
  · rintro ⟨⟨r, ⟨⟨⟨p, q⟩, ⟨hp, hq⟩, rfl⟩, hlt⟩, hrt⟩, hc⟩
    exact ⟨⟨(h1.2 ⟨⟨p, hp, ⟨le_trans (le_max_left _ _) hrt.1, lt_of_lt_of_le hrt.2 (min_le_left _ _)⟩⟩,
      hc⟩).1, (h2.2 ⟨⟨q, hq, ⟨le_trans (le_max_right _ _) hrt.1,
        lt_of_lt_of_le hrt.2 (min_le_right _ _)⟩⟩, hc⟩).1⟩, hc⟩

theorem IsLocIco.mem_iff {U : Set ℝ} (hU : IsLocIco U) (M : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (htM : t ≤ M) :
    t ∈ U ↔ ∃ L : Finset (ℝ × ℝ), (∀ p ∈ L, p.1 < p.2) ∧ ∃ p ∈ L, t ∈ Ico p.1 p.2 ∧
      U ∩ Icc 0 M = (⋃ p ∈ L, Ico p.1 p.2) ∩ Icc 0 M := by
  obtain ⟨L, hL, hLe⟩ := hU M
  constructor
  · intro ht
    have : t ∈ U ∩ Icc 0 M := ⟨ht, ht0, htM⟩
    rw [hLe] at this
    obtain ⟨hmem, -⟩ := this
    simp only [mem_iUnion, exists_prop] at hmem
    obtain ⟨p, hp, hpt⟩ := hmem
    exact ⟨L, hL, p, hp, hpt, hLe⟩
  · rintro ⟨L', -, p, hp, hpt, hLe'⟩
    have : t ∈ (⋃ p ∈ L', Ico p.1 p.2) ∩ Icc 0 M :=
      ⟨mem_iUnion₂.2 ⟨p, hp, hpt⟩, ht0, htM⟩
    rw [← hLe'] at this
    exact this.1

/-- Structure of relaxed times; stopping times (a), second part: for `U` locally of type `[l, r)`,
`c ≥ 0` and `U ∩ (c, ∞)` non-empty, `inf (U ∩ (c, ∞)) = min (U ∩ [c, ∞)) ∈ U`. -/
theorem IsLocIco.sInf_eq_min {U : Set ℝ} (hU : IsLocIco U) {c : ℝ} (hc : 0 ≤ c)
    (hne : (U ∩ Ioi c).Nonempty) :
    ∃ m ∈ U, c ≤ m ∧ (∀ u ∈ U, c ≤ u → m ≤ u) ∧ sInf (U ∩ Ioi c) = m := by
  classical
  obtain ⟨t₀, ht₀U, ht₀c⟩ := hne
  have ht00 : 0 ≤ t₀ := hc.trans ht₀c.le
  obtain ⟨L, hL, hLe⟩ := hU t₀
  have hinU : ∀ x, 0 ≤ x → x ≤ t₀ → (∃ p ∈ L, x ∈ Ico p.1 p.2) → x ∈ U := by
    rintro x hx0 hxM ⟨p, hp, hxp⟩
    have : x ∈ (⋃ p ∈ L, Ico p.1 p.2) ∩ Icc 0 t₀ := ⟨mem_iUnion₂.2 ⟨p, hp, hxp⟩, hx0, hxM⟩
    rw [← hLe] at this
    exact this.1
  have hcover : ∀ u ∈ U, u ≤ t₀ → 0 ≤ u → ∃ p ∈ L, u ∈ Ico p.1 p.2 := by
    intro u hu hu1 hu0
    have : u ∈ U ∩ Icc 0 t₀ := ⟨hu, hu0, hu1⟩
    rw [hLe] at this
    simpa only [mem_inter_iff, mem_iUnion, exists_prop] using this.1
  set C : Finset ℝ := (insert c (L.image Prod.fst)).filter (fun x => c ≤ x ∧ x ≤ t₀ ∧ x ∈ U)
    with hC
  -- a candidate below any `u ∈ U`, `c ≤ u ≤ t₀`
  have hcand : ∀ u ∈ U, c ≤ u → u ≤ t₀ → ∃ x ∈ C, x ≤ u := by
    intro u hu hcu hut
    obtain ⟨p, hp, hup⟩ := hcover u hu hut (hc.trans hcu)
    by_cases hpc : c ≤ p.1
    · refine ⟨p.1, ?_, hup.1⟩
      simp only [hC, Finset.mem_filter, Finset.mem_insert, Finset.mem_image]
      refine ⟨Or.inr ⟨p, hp, rfl⟩, hpc, hup.1.trans hut, hinU p.1 (hc.trans hpc)
        (hup.1.trans hut) ⟨p, hp, ⟨le_rfl, hL p hp⟩⟩⟩
    · push Not at hpc
      refine ⟨c, ?_, hcu⟩
      simp only [hC, Finset.mem_filter, Finset.mem_insert]
      exact ⟨Or.inl trivial, le_rfl, hcu.trans hut, hinU c hc (hcu.trans hut) ⟨p, hp, hpc.le, lt_of_le_of_lt hcu hup.2⟩⟩
  have hCne : C.Nonempty := by
    obtain ⟨x, hx, -⟩ := hcand t₀ ht₀U ht₀c.le le_rfl
    exact ⟨x, hx⟩
  set m := C.min' hCne with hm
  have hmC := Finset.min'_mem C hCne
  simp only [hC, Finset.mem_filter] at hmC
  have hlow : ∀ u ∈ U, c ≤ u → m ≤ u := by
    intro u hu hcu
    by_cases hut : u ≤ t₀
    · obtain ⟨x, hx, hxu⟩ := hcand u hu hcu hut
      exact (Finset.min'_le C x hx).trans hxu
    · push Not at hut
      exact hmC.2.2.1.trans hut.le
  refine ⟨m, hmC.2.2.2, hmC.2.1, hlow, ?_⟩
  have hne' : (U ∩ Ioi c).Nonempty := ⟨t₀, ht₀U, ht₀c⟩
  have hbdd : BddBelow (U ∩ Ioi c) := ⟨c, fun u hu => hu.2.le⟩
  refine le_antisymm ?_ (le_csInf hne' fun u hu => hlow u hu.1 hu.2.le)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set M := max t₀ (m + ε) with hM
  obtain ⟨L', hL', hLe'⟩ := hU M
  have hmM : m ≤ M := (by linarith : m ≤ m + ε).trans (le_max_right _ _)
  have hm0 : 0 ≤ m := hc.trans hmC.2.1
  have hmin : m ∈ U ∩ Icc 0 M := ⟨hmC.2.2.2, hm0, hmM⟩
  rw [hLe'] at hmin
  simp only [mem_inter_iff, mem_iUnion, exists_prop] at hmin
  obtain ⟨p, hp, hmp⟩ := hmin.1
  set u := (m + min p.2 (m + ε)) / 2 with hu
  have hmu : m < u := by
    have : m < min p.2 (m + ε) := lt_min hmp.2 (by linarith)
    linarith
  have huε : u < m + ε := by
    have := min_le_right p.2 (m + ε); linarith
  have hup : u ∈ Ico p.1 p.2 := ⟨hmp.1.trans hmu.le, by
    have := min_le_left p.2 (m + ε); linarith⟩
  have huU : u ∈ U := by
    have : u ∈ (⋃ p ∈ L', Ico p.1 p.2) ∩ Icc 0 M :=
      ⟨mem_iUnion₂.2 ⟨p, hp, hup⟩, hm0.trans hmu.le,
        huε.le.trans (le_max_right _ _)⟩
    rw [← hLe'] at this
    exact this.1
  calc sInf (U ∩ Ioi c) ≤ u := csInf_le hbdd ⟨huU, lt_of_le_of_lt hmC.2.1 hmu⟩
    _ < m + ε := huε

end ElboimSly.Paper
