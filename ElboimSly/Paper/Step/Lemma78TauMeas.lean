/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.CoreHit
public import Mathlib

/-!
# Measurability of the event `{τ' < c}` for a right-continuous continuation

One excursion succeeds with probability at least frac12 ("History"). With `T` a random time and `w` a random path whose
history `(ω, s) ↦ w ω ((max s 0) ∧ T)` is jointly measurable, and `X` a measurable process with
right-continuous paths, the event `{hitTime β (w ω) 0 (T ω) (w ω (T ω) + X ω) < c}` is measurable:
by right-continuity the infimum in `hitTime` is a countable union over `k ∈ ℤ` and rational `r`.
This is what lets `P(G ∩ {τ' < 4ⁿ})` be read off from the lower bound for `P(G ∩ {τ' ≥ 4ⁿ})` of
`es4_1_core`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

theorem hitTime_lt_iff {β : ℝ} {w : ℝ → Fin d → ℤ} {T : ℝ} {Wp : ℝ → Fin d → ℤ} {c : ℝ} :
    hitTime β w 0 T Wp < ENNReal.ofReal c ↔
      ∃ r : ℝ, 0 < r ∧ r < c ∧ ∃ k : ℤ, 0 < T + r + k * β ∧ T + r + k * β < T ∧
        ‖Wp r - w (T + r + k * β)‖ ≤ 1 := by
  unfold hitTime
  rw [iInf_lt_iff]
  constructor
  · rintro ⟨r, hr⟩
    rw [iInf_lt_iff] at hr
    obtain ⟨⟨hr0, s', ⟨k, hk⟩, hs0, hsT, hn⟩, hlt⟩ := hr
    have hc : 0 < c := by
      by_contra h
      rw [not_lt] at h
      rw [ENNReal.ofReal_of_nonpos h] at hlt
      exact absurd hlt (by simp)
    refine ⟨r, hr0, (ENNReal.ofReal_lt_ofReal_iff hc).1 hlt, k, ?_, ?_, ?_⟩
    · rw [← hk]; exact hs0
    · rw [← hk]; exact hsT
    · rw [← hk]; exact hn
  · rintro ⟨r, hr0, hrc, k, h1, h2, h3⟩
    refine ⟨r, ?_⟩
    rw [iInf_lt_iff]
    refine ⟨⟨hr0, T + r + k * β, ⟨k, rfl⟩, h1, h2, h3⟩, ?_⟩
    exact (ENNReal.ofReal_lt_ofReal_iff (hr0.trans hrc)).2 hrc

theorem measurableSet_hitTime_lt {β : ℝ} {Ω : Type*} (H : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (hH : H ≤ mΩ) {T : Ω → ℝ} (hT : Measurable[H] T)
    {w : Ω → ℝ → Fin d → ℤ}
    (hhist : Measurable[H.prod inferInstance] fun p : Ω × ℝ => w p.1 (min (0 + max p.2 0) (T p.1)))
    (hT0 : ∀ ω, 0 ≤ T ω)
    (hwrc : ∀ ω s, ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), w ω s' = w ω s)
    {X : Ω → ℝ≥0 → Fin d → ℤ} (hX : Measurable X)
    (hXrc : ∀ ω t, ∀ᶠ s in nhdsWithin t (Ici t), X ω s = X ω t) (c : ℝ) :
    MeasurableSet {ω | hitTime β (w ω) 0 (T ω) (fun r => w ω (T ω) + X ω r.toNNReal) <
      ENNReal.ofReal c} := by
  classical
  have hTm : Measurable T := hT.mono hH le_rfl
  have hhm : Measurable fun p : Ω × ℝ => w p.1 (min (0 + max p.2 0) (T p.1)) :=
    hhist.mono (sup_le_sup (MeasurableSpace.comap_mono hH) le_rfl) le_rfl
  have hist_eq : ∀ ω (s : ℝ), 0 ≤ s → s ≤ T ω → w ω (min (0 + max s 0) (T ω)) = w ω s := by
    intro ω s h0 h1
    rw [zero_add, max_eq_left h0, min_eq_left h1]
  have hwT : Measurable fun ω => w ω (T ω) := by
    have := hhm.comp (measurable_id.prodMk hTm)
    have e : (fun ω => w ω (T ω)) = (fun p : Ω × ℝ => w p.1 (min (0 + max p.2 0) (T p.1))) ∘
        (fun ω => (ω, T ω)) := by
      funext ω
      simp only [Function.comp]
      rw [hist_eq ω (T ω) (hT0 ω) le_rfl]
    rw [e]
    exact this
  have hXq : ∀ q : ℝ≥0, Measurable fun ω => X ω q := fun q => (measurable_pi_apply q).comp hX
  have hgm : ∀ (k : ℤ) (q : ℚ), Measurable fun ω =>
      w ω (min (0 + max (T ω + q + k * β) 0) (T ω)) := fun k q =>
    hhm.comp (measurable_id.prodMk ((hTm.add_const _).add_const _))
  -- the countable pieces
  set S : ℤ → ℚ → Set Ω := fun k q => {ω | 0 < (q : ℝ) ∧ (q : ℝ) < c ∧ 0 < T ω + q + k * β ∧
    T ω + q + k * β < T ω ∧ ‖w ω (T ω) + X ω (q : ℝ).toNNReal -
      w ω (min (0 + max (T ω + q + k * β) 0) (T ω))‖ ≤ 1} with hS
  have hSm : ∀ k q, MeasurableSet (S k q) := by
    intro k q
    have hf : Measurable fun ω => w ω (T ω) + X ω (q : ℝ).toNNReal -
        w ω (min (0 + max (T ω + q + k * β) 0) (T ω)) :=
      (hwT.add (hXq _)).sub (hgm k q)
    have h1 : MeasurableSet {ω : Ω | 0 < (q : ℝ)} := MeasurableSet.const _
    have h1' : MeasurableSet {ω : Ω | (q : ℝ) < c} := MeasurableSet.const _
    have h2 : MeasurableSet {ω | 0 < T ω + q + k * β} :=
      measurableSet_lt measurable_const ((hTm.add_const _).add_const _)
    have h3 : MeasurableSet {ω | T ω + q + k * β < T ω} :=
      measurableSet_lt ((hTm.add_const _).add_const _) hTm
    have h4 : MeasurableSet {ω | ‖w ω (T ω) + X ω (q : ℝ).toNNReal -
        w ω (min (0 + max (T ω + q + k * β) 0) (T ω))‖ ≤ 1} :=
      hf ((Set.to_countable {v : Fin d → ℤ | ‖v‖ ≤ 1}).measurableSet)
    exact h1.inter (h1'.inter (h2.inter (h3.inter h4)))
  have hset : {ω | hitTime β (w ω) 0 (T ω) (fun r => w ω (T ω) + X ω r.toNNReal) <
      ENNReal.ofReal c} = ⋃ k : ℤ, ⋃ q : ℚ, S k q := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, hitTime_lt_iff, hS]
    constructor
    · rintro ⟨r, hr0, hrc, k, h1, h2, h3⟩
      refine ⟨k, ?_⟩
      -- choose the rational
      obtain ⟨ε1, hε1, hw1⟩ := hwrc ω (T ω + r + k * β)
      obtain ⟨u', hu', hX1⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hXrc ω r.toNNReal)
      have hu'r : r < (u' : ℝ) := (Real.toNNReal_lt_iff_lt_coe hr0.le).1 hu'
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min (lt_min (lt_add_of_pos_right r hε1)
        hu'r) (lt_min hrc (show r < r + (T ω - (T ω + r + k * β)) by linarith)))
      have hq3 : (q : ℝ) < r + ε1 := lt_of_lt_of_le hq2 ((min_le_left _ _).trans (min_le_left _ _))
      have hq4 : (q : ℝ) < u' := lt_of_lt_of_le hq2 ((min_le_left _ _).trans (min_le_right _ _))
      have hq5 : (q : ℝ) < c := lt_of_lt_of_le hq2 ((min_le_right _ _).trans (min_le_left _ _))
      have hq6 : (q : ℝ) < r + (T ω - (T ω + r + k * β)) :=
        lt_of_lt_of_le hq2 ((min_le_right _ _).trans (min_le_right _ _))
      have hqr : r < (q : ℝ) := hq1
      refine ⟨q, hr0.trans hqr, hq5, by linarith, by linarith, ?_⟩
      have e1 : w ω (T ω + q + k * β) = w ω (T ω + r + k * β) :=
        hw1 _ ⟨by linarith, by linarith⟩
      have hmem : (q : ℝ).toNNReal ∈ Ico r.toNNReal u' :=
        ⟨Real.toNNReal_mono hqr.le, (Real.toNNReal_lt_iff_lt_coe (hr0.trans hqr).le).2 hq4⟩
      have e2 : X ω (q : ℝ).toNNReal = X ω r.toNNReal := hX1 hmem
      have e3 : w ω (min (0 + max (T ω + q + k * β) 0) (T ω)) = w ω (T ω + q + k * β) :=
        hist_eq ω _ (by linarith) (by linarith)
      rw [e3, e1, e2]
      exact h3
    · rintro ⟨k, q, h0, hc, h1, h2, h3⟩
      refine ⟨q, h0, hc, k, h1, h2, ?_⟩
      have e3 : w ω (min (0 + max (T ω + q + k * β) 0) (T ω)) = w ω (T ω + q + k * β) :=
        hist_eq ω _ h1.le h2.le
      rw [e3] at h3
      simpa only [Real.toNNReal_coe] using h3
  rw [hset]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun q => hSm k q

end ElboimSly.Paper.Step

end
