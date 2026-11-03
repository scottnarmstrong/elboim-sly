/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.FastDisplacement

/-!
# The infima `τ_fast`, `τ_jump` are attained

Pathwise consequences of tfast and heavyJ (d) (supplement).

* `ofReal_lt_pathTfast_iff`: `T < τ_fast(w; L)` iff `‖w t - w s‖ < L` for all `t ∈ (0, T]`,
  `s ∈ [t-1, t]`.  Likewise `ofReal_lt_pathTjump_iff` for `τ_jump`.
* `ofReal_lt_pathTfast_congr`, `ofReal_lt_pathTjump_congr`: the events `{τ ≤ T}` depend only on
  `w|[0,T]`.
-/

@[expose] public section

open Filter Topology Set
open scoped ENNReal

namespace ElboimSly.Paper

variable {d : ℕ} {w : ℝ → Fin d → ℤ}

section generic

variable {S : Set ℝ}

theorem sInf_mem_of_stable (hpos : ∀ t ∈ S, 0 < t)
    (hst : ∀ t : ℝ, 0 ≤ t → t ∉ S → ∃ η > 0, ∀ t' ∈ Ico t (t + η), t' ∉ S) (hne : S.Nonempty) :
    sInf S ∈ S := by
  by_contra hn
  have hb : BddBelow S := ⟨0, fun t ht => (hpos t ht).le⟩
  have h0 : 0 ≤ sInf S := le_csInf hne (fun t ht => (hpos t ht).le)
  obtain ⟨η, hη, h⟩ := hst _ h0 hn
  obtain ⟨s, hs, hs2⟩ := exists_lt_of_csInf_lt hne (show sInf S < sInf S + η by linarith)
  exact h s ⟨csInf_le hb hs, hs2⟩ hs

theorem ofReal_lt_iInf_iff (hpos : ∀ t ∈ S, 0 < t)
    (hst : ∀ t : ℝ, 0 ≤ t → t ∉ S → ∃ η > 0, ∀ t' ∈ Ico t (t + η), t' ∉ S) {T : ℝ} :
    ENNReal.ofReal T < (⨅ t ∈ S, ENNReal.ofReal t) ↔ ∀ t ∈ S, T < t := by
  constructor
  · intro h t ht
    have := h.trans_le (iInf₂_le (f := fun t (_ : t ∈ S) => ENNReal.ofReal t) t ht)
    exact ((ENNReal.ofReal_lt_ofReal_iff' ).1 this).1
  · intro h
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    · have hm := sInf_mem_of_stable hpos hst hne
      have hb : BddBelow S := ⟨0, fun t ht => (hpos t ht).le⟩
      have heq : (⨅ t ∈ S, ENNReal.ofReal t) = ENNReal.ofReal (sInf S) :=
        le_antisymm (iInf₂_le _ hm)
          (le_iInf₂ fun t ht => ENNReal.ofReal_le_ofReal (csInf_le hb ht))
      rw [heq]
      exact (ENNReal.ofReal_lt_ofReal_iff (hpos _ hm)).2 (h _ hm)

end generic

/-- The set defining `τ_fast`. -/
def tfastSet (w : ℝ → Fin d → ℤ) (L : ℝ) : Set ℝ :=
  {t : ℝ | 0 < t ∧ ∃ s : ℝ, t - 1 ≤ s ∧ s ≤ t ∧ L ≤ ‖w t - w (max s 0)‖}

/-- The set defining `τ_jump`. -/
def tjumpSet (w : ℝ → Fin d → ℤ) (L : ℝ) : Set ℝ :=
  {t : ℝ | 0 < t ∧ L ≤ (cycJumpCount w (t - 1) t : ℝ)}

theorem pathTfast_eq (w : ℝ → Fin d → ℤ) (L : ℝ) :
    pathTfast w L = ⨅ t ∈ tfastSet w L, ENNReal.ofReal t := rfl

theorem pathTjump_eq (w : ℝ → Fin d → ℤ) (L : ℝ) :
    pathTjump w L = ⨅ t ∈ tjumpSet w L, ENNReal.ofReal t := rfl

theorem tfastSet_stable (hw : IsCyclicPath w) {L : ℝ} (hL : 0 < L) :
    ∀ t : ℝ, 0 ≤ t → t ∉ tfastSet w L → ∃ η > 0, ∀ t' ∈ Ico t (t + η), t' ∉ tfastSet w L := by
  intro t ht htS
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hw.rc t ht)
  refine ⟨u - t, by linarith [mem_Ioi.1 hu], fun t' ht' => ?_⟩
  have ht'u : t' ∈ Ico t u := ⟨ht'.1, by have := ht'.2; linarith⟩
  have hwt' : w t' = w t := hsub ht'u
  rintro ⟨ht'0, s, hs1, hs2, hge⟩
  rcases le_or_gt t s with hts | hts
  · have hs0 : max s 0 = s := max_eq_left (ht.trans hts)
    have : w s = w t := hsub ⟨hts, lt_of_le_of_lt hs2 ht'u.2⟩
    rw [hs0, this, hwt', sub_self, norm_zero] at hge
    linarith
  · rcases eq_or_lt_of_le ht with ht0 | ht0
    · have hs0 : max s 0 = 0 := max_eq_right (by linarith)
      rw [hs0, hwt', ← ht0, hw.zero, sub_self, norm_zero] at hge
      linarith
    · apply htS
      refine ⟨ht0, s, by linarith [ht'.1], hts.le, ?_⟩
      rwa [hwt'] at hge

theorem tjumpSet_stable (hw : IsCyclicPath w) {L : ℝ} (hL : 0 < L) :
    ∀ t : ℝ, 0 ≤ t → t ∉ tjumpSet w L → ∃ η > 0, ∀ t' ∈ Ico t (t + η), t' ∉ tjumpSet w L := by
  intro t ht htS
  have hJ : (cycJumpCount w (t - 1) t : ℝ) < L := by
    rcases eq_or_lt_of_le ht with ht0 | ht0
    · have : cycJumpSet w ∩ Ioc (t - 1) t = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
        intro hx hx1 hx2
        have := hx.1
        linarith
      unfold cycJumpCount
      rw [this]; simpa using hL
    · by_contra hc
      exact htS ⟨ht0, not_lt.1 hc⟩
  have hA : (cycJumpSet w ∩ Ioc t (t + 1)).Finite := (hw.fin (t + 1)).subset fun x hx => ⟨hx.1, hx.2.2⟩
  have e1 : ∀ᶠ u in 𝓝[>] t, ∀ x ∈ cycJumpSet w ∩ Ioc t (t + 1), u < x := by
    rw [Filter.eventually_all_finite hA]
    intro x hx
    exact Ioo_mem_nhdsGT hx.2.1 |> fun h => Filter.mem_of_superset h fun u hu => hu.2
  have e2 : ∀ᶠ u in 𝓝[>] t, u < t + 1 := Ioo_mem_nhdsGT (by linarith) |>
    fun h => Filter.mem_of_superset h fun u hu => hu.2
  obtain ⟨u, hu1, hu2, hu3⟩ := (e1.and (e2.and self_mem_nhdsWithin)).exists
  have htu : t < u := hu3
  refine ⟨u - t, by linarith, fun t' ht' => ?_⟩
  rintro ⟨_, hge⟩
  have ht'u : t' < u := by have := ht'.2; linarith
  have hsub : cycJumpSet w ∩ Ioc (t' - 1) t' ⊆ cycJumpSet w ∩ Ioc (t - 1) t := by
    intro x hx
    refine ⟨hx.1, ?_, ?_⟩
    · linarith [hx.2.1, ht'.1]
    · by_contra hxt
      push Not at hxt
      exact absurd (hu1 x ⟨hx.1, hxt, by linarith [hx.2.2]⟩) (by linarith [hx.2.2])
  have hle : cycJumpCount w (t' - 1) t' ≤ cycJumpCount w (t - 1) t :=
    Set.ncard_le_ncard hsub ((hw.fin t).subset fun x hx => ⟨hx.1, hx.2.2⟩)
  have : (cycJumpCount w (t' - 1) t' : ℝ) ≤ cycJumpCount w (t - 1) t := by exact_mod_cast hle
  linarith

theorem tfastSet_pos (w : ℝ → Fin d → ℤ) (L : ℝ) : ∀ t ∈ tfastSet w L, 0 < t := fun _ h => h.1

theorem tjumpSet_pos (w : ℝ → Fin d → ℤ) (L : ℝ) : ∀ t ∈ tjumpSet w L, 0 < t := fun _ h => h.1

/-- Pathwise consequences of tfast and heavyJ (d). `T < τ_fast(w; L)` iff the displacement over every
unit window ending in `(0, T]` is `< L`. -/
theorem ofReal_lt_pathTfast_iff (hw : IsCyclicPath w) {L : ℝ} (hL : 0 < L) (T : ℝ) :
    ENNReal.ofReal T < pathTfast w L ↔
      ∀ t : ℝ, 0 < t → t ≤ T → ∀ s : ℝ, t - 1 ≤ s → s ≤ t → ‖w t - w (max s 0)‖ < L := by
  rw [pathTfast_eq, ofReal_lt_iInf_iff (tfastSet_pos w L) (tfastSet_stable hw hL)]
  constructor
  · intro h t ht0 htT s hs1 hs2
    by_contra hc
    push Not at hc
    exact absurd (h t ⟨ht0, s, hs1, hs2, hc⟩) (not_lt.2 htT)
  · rintro h t ⟨ht0, s, hs1, hs2, hge⟩
    by_contra hc
    exact absurd (h t ht0 (not_lt.1 hc) s hs1 hs2) (not_lt.2 hge)

/-- Pathwise consequences of tfast and heavyJ (d). -/
theorem ofReal_lt_pathTjump_iff (hw : IsCyclicPath w) {L : ℝ} (hL : 0 < L) (T : ℝ) :
    ENNReal.ofReal T < pathTjump w L ↔
      ∀ t : ℝ, 0 < t → t ≤ T → (cycJumpCount w (t - 1) t : ℝ) < L := by
  rw [pathTjump_eq, ofReal_lt_iInf_iff (tjumpSet_pos w L) (tjumpSet_stable hw hL)]
  constructor
  · intro h t ht0 htT
    by_contra hc
    push Not at hc
    exact absurd (h t ⟨ht0, hc⟩) (not_lt.2 htT)
  · rintro h t ⟨ht0, hge⟩
    by_contra hc
    exact absurd (h t ht0 (not_lt.1 hc)) (not_lt.2 hge)

/-- Pathwise consequences of tfast and heavyJ (d): `{τ_fast ≤ T}` depends only on `w|[0,T]`. -/
theorem ofReal_lt_pathTfast_congr {w' : ℝ → Fin d → ℤ} (hw : IsCyclicPath w)
    (hw' : IsCyclicPath w') {L : ℝ} (hL : 0 < L) {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ x ∈ Icc 0 T, w x = w' x) :
    ENNReal.ofReal T < pathTfast w L ↔ ENNReal.ofReal T < pathTfast w' L := by
  rw [ofReal_lt_pathTfast_iff hw hL, ofReal_lt_pathTfast_iff hw' hL]
  have key : ∀ t, 0 < t → t ≤ T → ∀ s, s ≤ t → w t - w (max s 0) = w' t - w' (max s 0) := by
    intro t ht0 htT s hs
    rw [h t ⟨ht0.le, htT⟩, h (max s 0) ⟨le_max_right _ _, max_le (hs.trans htT) hT⟩]
  constructor
  · intro H t ht0 htT s hs1 hs2
    rw [← key t ht0 htT s hs2]; exact H t ht0 htT s hs1 hs2
  · intro H t ht0 htT s hs1 hs2
    rw [key t ht0 htT s hs2]; exact H t ht0 htT s hs1 hs2

/-- Pathwise consequences of tfast and heavyJ (d): `{τ_jump ≤ T}` depends only on the jump set of `w`
in `(0, T]`. -/
theorem ofReal_lt_pathTjump_congr {w' : ℝ → Fin d → ℤ} (hw : IsCyclicPath w)
    (hw' : IsCyclicPath w') {L : ℝ} (hL : 0 < L) {T : ℝ}
    (h : ∀ r ∈ Ioc 0 T, r ∈ cycJumpSet w ↔ r ∈ cycJumpSet w') :
    ENNReal.ofReal T < pathTjump w L ↔ ENNReal.ofReal T < pathTjump w' L := by
  rw [ofReal_lt_pathTjump_iff hw hL, ofReal_lt_pathTjump_iff hw' hL]
  have key : ∀ t : ℝ, 0 < t → t ≤ T → cycJumpCount w (t - 1) t = cycJumpCount w' (t - 1) t := by
    intro t ht0 htT
    unfold cycJumpCount
    congr 1
    ext r
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hr, hr2⟩
      exact ⟨(h r ⟨hr.1, hr2.2.trans htT⟩).1 hr, hr2⟩
    · rintro ⟨hr, hr2⟩
      exact ⟨(h r ⟨hr.1, hr2.2.trans htT⟩).2 hr, hr2⟩
  constructor
  · intro H t ht0 htT
    rw [← key t ht0 htT]; exact H t ht0 htT
  · intro H t ht0 htT
    rw [key t ht0 htT]; exact H t ht0 htT

end ElboimSly.Paper
