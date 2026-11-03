/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IsRelaxedTimeWrt
public import ElboimSly.Frozen.Defs.IndDelta
public import ElboimSly.Frozen.Defs.IsHeavy
public import Mathlib

/-!
# Structure of relaxed times: pointwise parts

Structure of relaxed times; stopping times (b), (c) (ES22 §7).

Setting: `w : ℝ → ℤ^d` right-continuous, `α : ℝ → ℝ` the last regeneration time at or before `t`
(left abstract), `𝒯` the set of `t ≥ 0` relaxed with respect to `w|_{[α t, t]}`, and `thit` the
hitting time of the written proof (`eq:cyc-thit`) for `w` and `α`.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The set `𝒯` of relaxed times of `w` with regeneration function `α`. -/
def stepRelaxedSet (β : ℝ) (w : ℝ → Fin d → ℤ) (α : ℝ → ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ IsRelaxedTimeWrt β w (α t) t}

/-- The hitting time `thit(t) = inf {s > t : ∃ s' ∈ s + βℤ, α(t) < s' < t, ‖w s - w s'‖ ≤ 1}`. -/
noncomputable def stepThit (β : ℝ) (w : ℝ → Fin d → ℤ) (α : ℝ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ⨅ s ∈ {s : ℝ | t < s ∧ ∃ s' : ℝ, (∃ k : ℤ, s' = s + k * β) ∧ α t < s' ∧ s' < t ∧
      ‖w s - w s'‖ ≤ 1}, ENNReal.ofReal s

theorem indDelta_pos' (hd : 1 ≤ d) : 0 < indDelta d := by
  unfold indDelta
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  positivity

theorem three_indDelta_lt_one (hd : 1 ≤ d) : 3 * indDelta d < 1 := by
  unfold indDelta
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ this
  have h3 : 0 < 3000 * (d : ℝ) ^ 2 := by positivity
  rw [← mul_div_assoc, div_lt_one h3]
  nlinarith

theorem rpow_three_indDelta_lt {β : ℝ} (hd : 1 ≤ d) (hβ : 1 < β) :
    β ^ (3 * indDelta d) < β := by
  have := Real.rpow_lt_rpow_of_exponent_lt hβ (three_indDelta_lt_one hd)
  simpa using this

theorem one_lt_rpow_indDelta {β : ℝ} (hd : 1 ≤ d) (hβ : 1 < β) : 1 < β ^ indDelta d :=
  Real.one_lt_rpow hβ (indDelta_pos' hd)

/-- Structure of relaxed times; stopping times (b). If `t` is relaxed then `thit(t) > t`. -/
theorem stepThit_gt_of_relaxed {β : ℝ} (hd : 1 ≤ d) (hβ : 1 < β) {w : ℝ → Fin d → ℤ} {α : ℝ → ℝ}
    (hrc : ∀ s, ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), w s' = w s) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : IsRelaxedTimeWrt β w (α t) t) : ENNReal.ofReal t < stepThit β w α t := by
  obtain ⟨ε, hε, hconst⟩ := hrc t
  have hgap : 0 < β - β ^ (3 * indDelta d) := sub_pos.2 (rpow_three_indDelta_lt hd hβ)
  have hm := lt_min hε hgap
  set η := min ε (β - β ^ (3 * indDelta d)) / 2 with hη
  have hη0 : 0 < η := by positivity
  have hηε : η < ε := by have := min_le_left ε (β - β ^ (3 * indDelta d)); simp only [hη]; linarith
  have hηg : η < β - β ^ (3 * indDelta d) := by
    have := min_le_right ε (β - β ^ (3 * indDelta d)); simp only [hη]; linarith
  have hlow : ENNReal.ofReal (t + η) ≤ stepThit β w α t := by
    refine le_iInf₂ fun s hs => ?_
    obtain ⟨hts, s', ⟨k, hk⟩, hαs', hs't, hnorm⟩ := hs
    refine ENNReal.ofReal_le_ofReal ?_
    by_contra hlt
    push Not at hlt
    have hws : w s = w t := hconst s ⟨hts.le, by linarith⟩
    have hβ0 : 0 < β := by linarith
    have hks : s' ≤ t - β ^ (3 * indDelta d) := by
      have hk0 : k < 0 := by
        by_contra hk0
        push Not at hk0
        have : (0 : ℝ) ≤ k := by exact_mod_cast hk0
        nlinarith
      have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      nlinarith
    have := ht.2 s' hαs'.le hks
    rw [hws] at hnorm
    have h1 := one_lt_rpow_indDelta hd hβ
    linarith
  exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)) hlow

/-- Structure of relaxed times; stopping times (c). If `α ≡ 0` and the path is `kβ`-periodic for some
`k ≥ 1` with `kβ ≤ t`, then `t` is not relaxed. -/
theorem not_relaxed_of_periodic {β : ℝ} (hd : 1 ≤ d) (hβ : 1 < β) {w : ℝ → Fin d → ℤ} {t : ℝ}
    {k : ℕ} (hk : 1 ≤ k) (hkt : (k : ℝ) * β ≤ t) (hper : ∀ r, 0 ≤ r → w (r + k * β) = w r) :
    ¬ IsRelaxedTimeWrt β w 0 t := by
  intro h
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h3 := rpow_three_indDelta_lt hd hβ
  have hs0 : 0 ≤ t - k * β := by linarith
  have := h.2 (t - k * β) hs0 (by nlinarith)
  have hw : w t = w (t - k * β) := by
    have := hper (t - k * β) hs0
    rwa [sub_add_cancel] at this
  rw [hw, sub_self, norm_zero] at this
  have := one_lt_rpow_indDelta hd hβ
  linarith

theorem rpow_three_indDelta_pos {β : ℝ} (hβ : 1 < β) (d : ℕ) : 0 < β ^ (3 * indDelta d) :=
  Real.rpow_pos_of_pos (by linarith) _

/-- On a piece `[e, e')` where `w` and `α` are constant, the visited set does not depend on the
endpoint `t ∈ [e, e')`. -/
theorem visitedSet_piece {w : ℝ → Fin d → ℤ} {a e e' t : ℝ} (hae : a ≤ e)
    (hw : ∀ s ∈ Ico e e', w s = w e) (ht : t ∈ Ico e e') : visitedSet w a t = visitedSet w a e := by
  unfold visitedSet
  ext y
  constructor
  · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
    by_cases hse : s ≤ e
    · exact ⟨s, ⟨hs1, hse⟩, rfl⟩
    · push Not at hse
      exact ⟨e, ⟨hae, le_rfl⟩, (hw s ⟨hse.le, lt_of_le_of_lt hs2 ht.2⟩).symm⟩
  · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
    exact ⟨s, ⟨hs1, hs2.trans ht.1⟩, rfl⟩

/-- Structure of relaxed times; stopping times (a), one piece. On a piece `[e, e')` where `w` and `α`
are constant, with the first approach time `s*` to `w e` attained, `𝒯 ∩ [e, e')` is of the form
`[e, min e' c)`. -/
theorem relaxedSet_piece {β : ℝ} (_hd : 1 ≤ d) (hβ : 1 < β) {w : ℝ → Fin d → ℤ} {α : ℝ → ℝ}
    {e e' : ℝ} (he0 : 0 ≤ e) (hw : ∀ s ∈ Ico e e', w s = w e) (hα : ∀ s ∈ Ico e e', α s = α e)
    (hae : α e ≤ e)
    (hmin : ∃ s₀ ∈ Icc (α e) e, ‖w e - w s₀‖ < β ^ indDelta d ∧
      ∀ s ∈ Icc (α e) e, ‖w e - w s‖ < β ^ indDelta d → s₀ ≤ s) :
    ∃ c : ℝ, stepRelaxedSet β w α ∩ Ico e e' = Ico e (min e' c) := by
  classical
  obtain ⟨s₀, hs₀, hs₀n, hs₀m⟩ := hmin
  have hb3 := rpow_three_indDelta_pos hβ d
  set P1 : Prop := ∀ r : ℝ, β ^ indDelta d ≤ r → ¬ IsHeavy w (α e) e (w e) r with hP1
  refine ⟨if P1 then s₀ + β ^ (3 * indDelta d) else e, ?_⟩
  ext t
  simp only [mem_inter_iff, stepRelaxedSet, mem_ofPred_eq, mem_Ico, lt_min_iff]
  constructor
  · rintro ⟨⟨-, hrel⟩, het, het'⟩
    rw [hα t ⟨het, het'⟩] at hrel
    have hP : P1 := by
      intro r hr hh
      refine hrel.1 r hr ?_
      unfold IsHeavy at hh ⊢
      rw [hw t ⟨het, het'⟩, visitedSet_piece hae hw ⟨het, het'⟩]
      exact hh
    refine ⟨het, het', ?_⟩
    rw [ite_eq_left hP]
    by_contra hge
    push Not at hge
    have := hrel.2 s₀ hs₀.1 (by linarith)
    rw [hw t ⟨het, het'⟩] at this
    linarith
  · rintro ⟨het, het', hc⟩
    refine ⟨⟨he0.trans het, ?_⟩, het, het'⟩
    rw [hα t ⟨het, het'⟩]
    split_ifs at hc with hP
    · refine ⟨fun r hr hh => hP r hr ?_, fun s hs1 hs2 => ?_⟩
      · unfold IsHeavy at hh ⊢
        rw [hw t ⟨het, het'⟩, visitedSet_piece hae hw ⟨het, het'⟩] at hh
        exact hh
      · rw [hw t ⟨het, het'⟩]
        by_cases hse : s ≤ e
        · by_contra hlt
          push Not at hlt
          have := hs₀m s ⟨hs1, hse⟩ hlt
          linarith
        · push Not at hse
          exfalso
          have := hs₀.2
          linarith
    · linarith

/-- The first approach time is attained, for a path that is constant on the pieces of a finite
partition `E`. -/
theorem exists_first_approach {w : ℝ → Fin d → ℤ} {a e b : ℝ} (hb : 0 < b) (E : Finset ℝ)
    (h0 : 0 ∈ E) (_hpos : ∀ x ∈ E, 0 ≤ x)
    (hpiece : ∀ e ∈ E, ∀ s, e ≤ s → (∀ x ∈ E, x ≤ e ∨ s < x) → w s = w e)
    (he : e ∈ E) (ha0 : 0 ≤ a) (hae : a ≤ e) :
    ∃ s₀ ∈ Icc a e, ‖w e - w s₀‖ < b ∧ ∀ s ∈ Icc a e, ‖w e - w s‖ < b → s₀ ≤ s := by
  classical
  set C : Finset ℝ := (insert a E).filter (fun x => a ≤ x ∧ x ≤ e ∧ ‖w e - w x‖ < b) with hC
  have hCne : C.Nonempty := ⟨e, by simp [hC, he, hae, hb]⟩
  have hs₀ := Finset.min'_mem C hCne
  simp only [hC, Finset.mem_filter] at hs₀
  refine ⟨C.min' hCne, ⟨hs₀.2.1, hs₀.2.2.1⟩, hs₀.2.2.2, fun s hs hn => ?_⟩
  -- the piece containing `s`
  have hEs : (E.filter (· ≤ s)).Nonempty := ⟨0, by simp [h0, ha0.trans hs.1]⟩
  set p := (E.filter (· ≤ s)).max' hEs with hp
  have hpmem := Finset.max'_mem (E.filter (· ≤ s)) hEs
  simp only [Finset.mem_filter] at hpmem
  have hmax : ∀ x ∈ E, x ≤ s → x ≤ p := fun x hx hxs =>
    Finset.le_max' (E.filter (· ≤ s)) x (by simp [hx, hxs])
  have hws : w s = w p := hpiece p hpmem.1 s hpmem.2 fun x hx => by
    by_cases hxs : x ≤ s
    · exact Or.inl (hmax x hx hxs)
    · exact Or.inr (not_le.1 hxs)
  by_cases hap : a ≤ p
  · refine le_trans (Finset.min'_le C p ?_) hpmem.2
    simp only [hC, Finset.mem_filter]
    exact ⟨Finset.mem_insert_of_mem hpmem.1, hap, hpmem.2.trans hs.2, by rw [← hws]; exact hn⟩
  · push Not at hap
    have hwa : w a = w p := hpiece p hpmem.1 a hap.le fun x hx => by
      by_cases hxs : x ≤ s
      · exact Or.inl (hmax x hx hxs)
      · exact Or.inr (lt_of_le_of_lt hs.1 (not_le.1 hxs))
    refine le_trans (Finset.min'_le C a ?_) hs.1
    simp only [hC, Finset.mem_filter]
    exact ⟨Finset.mem_insert_self _ _, le_rfl, hae, by rw [hwa, ← hws]; exact hn⟩

/-- Structure of relaxed times; stopping times (a). Suppose `w` and `α` are constant between the
points of a finite set `E ∋ 0` of non-negative event times, with some event after `M`, and
`0 ≤ α e ≤ e` at the events. Then `𝒯 ∩ [0, M]` is a finite union of intervals `[l, r)`, `l < r`
(intersected with `[0, M]`). -/
theorem relaxedSet_finite_union {β : ℝ} (hd : 1 ≤ d) (hβ : 1 < β) {w : ℝ → Fin d → ℤ}
    {α : ℝ → ℝ} {M : ℝ} (E : Finset ℝ) (h0 : 0 ∈ E) (hpos : ∀ x ∈ E, 0 ≤ x)
    (htop : ∃ x ∈ E, M < x)
    (hpiece : ∀ e ∈ E, ∀ s, e ≤ s → (∀ x ∈ E, x ≤ e ∨ s < x) → w s = w e ∧ α s = α e)
    (hα : ∀ e ∈ E, 0 ≤ α e ∧ α e ≤ e) :
    ∃ L : Finset (ℝ × ℝ), (∀ p ∈ L, p.1 < p.2) ∧
      stepRelaxedSet β w α ∩ Icc 0 M = (⋃ p ∈ L, Ico p.1 p.2) ∩ Icc 0 M := by
  classical
  have hb : 0 < β ^ indDelta d := Real.rpow_pos_of_pos (by linarith) _
  have hpc : ∀ e ∈ E, ∀ e', e < e' → (∀ x ∈ E, x ≤ e ∨ e' ≤ x) →
      ∃ c : ℝ, stepRelaxedSet β w α ∩ Ico e e' = Ico e (min e' c) := by
    intro e he e' hee' hnext
    refine relaxedSet_piece hd hβ (hpos e he) (fun s hs => ?_) (fun s hs => ?_) (hα e he).2
      (exists_first_approach hb E h0 hpos (fun e he s hes hno => (hpiece e he s hes hno).1) he
        (hα e he).1 (hα e he).2)
    · exact (hpiece e he s hs.1 fun x hx => (hnext x hx).imp_right fun h => lt_of_lt_of_le hs.2 h).1
    · exact (hpiece e he s hs.1 fun x hx => (hnext x hx).imp_right fun h => lt_of_lt_of_le hs.2 h).2
  have hpc' : ∀ e ∈ E, ∀ e', e < e' ∧ (∀ x ∈ E, x ≤ e ∨ e' ≤ x) →
      ∃ c : ℝ, stepRelaxedSet β w α ∩ Ico e e' = Ico e (min e' c) :=
    fun e he e' h => hpc e he e' h.1 h.2
  choose! c hc using hpc'
  refine ⟨(((E ×ˢ E).filter (fun q : ℝ × ℝ => q.1 < q.2 ∧ ∀ x ∈ E, x ≤ q.1 ∨ q.2 ≤ x)).image
    (fun q => (q.1, min q.2 (c q.1 q.2)))).filter (fun q => q.1 < q.2), ?_, ?_⟩
  · intro q hq
    exact (Finset.mem_filter.1 hq).2
  · ext t
    simp only [mem_inter_iff, mem_iUnion, Finset.mem_filter, Finset.mem_image, Finset.mem_product,
      exists_prop, mem_Ico, mem_Icc]
    constructor
    · rintro ⟨ht, ht0, htM⟩
      -- the piece containing t
      have hEt : (E.filter (· ≤ t)).Nonempty := ⟨0, by simp [h0, ht0]⟩
      set e := (E.filter (· ≤ t)).max' hEt with he
      have hemem := Finset.max'_mem (E.filter (· ≤ t)) hEt
      simp only [Finset.mem_filter] at hemem
      have hmax : ∀ x ∈ E, x ≤ t → x ≤ e := fun x hx hxt =>
        Finset.le_max' (E.filter (· ≤ t)) x (by simp [hx, hxt])
      obtain ⟨x₀, hx₀, hMx₀⟩ := htop
      have hGt : (E.filter (e < ·)).Nonempty :=
        ⟨x₀, by simp only [Finset.mem_filter]; exact ⟨hx₀, by
          have := hmax; by_contra hh; push Not at hh
          have := hemem.2; linarith⟩⟩
      set e' := (E.filter (e < ·)).min' hGt with he'
      have he'mem := Finset.min'_mem (E.filter (e < ·)) hGt
      simp only [Finset.mem_filter] at he'mem
      have hmin : ∀ x ∈ E, e < x → e' ≤ x := fun x hx hex =>
        Finset.min'_le (E.filter (e < ·)) x (by simp [hx, hex])
      have hnext : ∀ x ∈ E, x ≤ e ∨ e' ≤ x := fun x hx => by
        by_cases hxe : x ≤ e
        · exact Or.inl hxe
        · exact Or.inr (hmin x hx (not_le.1 hxe))
      have hte' : t < e' := by
        by_contra hh; push Not at hh
        have := hmax e' he'mem.1 hh
        linarith [he'mem.2]
      have hmem : t ∈ stepRelaxedSet β w α ∩ Ico e e' := ⟨ht, hemem.2, hte'⟩
      rw [hc e hemem.1 e' ⟨he'mem.2, hnext⟩] at hmem
      refine ⟨⟨(e, min e' (c e e')), ⟨⟨(e, e'), ⟨⟨hemem.1, he'mem.1⟩, he'mem.2, hnext⟩, rfl⟩,
        lt_of_le_of_lt hmem.1 hmem.2⟩, hmem.1, hmem.2⟩, ht0, htM⟩
    · rintro ⟨⟨q, ⟨⟨⟨e, e'⟩, ⟨⟨he, he'⟩, hee', hnext⟩, rfl⟩, hlt⟩, hq1, hq2⟩, ht0, htM⟩
      simp only at hq1 hq2 hlt
      have : t ∈ Ico e (min e' (c e e')) := ⟨hq1, hq2⟩
      rw [← hc e he e' ⟨hee', hnext⟩] at this
      exact ⟨this.1, ht0, htM⟩

end ElboimSly.Paper
