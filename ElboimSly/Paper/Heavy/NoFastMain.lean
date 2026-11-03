/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.NoFast

/-!
# A good block cannot be approached fast: the two parts

A good block cannot be approached fast (a), (b).
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {β t₀ : ℝ} {w : ℝ → Fin d → ℤ} {ι : Fin d → ℤ}

/-- A good block cannot be approached fast (a). -/
theorem nofast_a {t_st : ℝ} (hgood : ¬ BadByTime d β t₀ n w ι t_st) {x y : ℝ}
    (hx : x ∈ cycIntTimes β) (hxy : x ≤ y) (hy : y ≤ min (x + heavyTkPrime d t₀ n) t_st)
    (hxB : latDist (w x) (heavyBlock (heavyLevel d n) ι) ≤ 2 ^ (heavyLevel d n + 2)) :
    ‖w y - w x‖ ≤ (2 : ℝ) ^ (heavyLevel d n - 1) := by
  by_contra hcon
  push Not at hcon
  apply hgood
  right; left
  refine ⟨x, hx, hxy.trans (hy.trans (min_le_right _ _)), hxB, y - x, ⟨by linarith, ?_⟩, ?_⟩
  · exact le_min (by linarith [min_le_left (x + heavyTkPrime d t₀ n) t_st])
      (by linarith [min_le_right (x + heavyTkPrime d t₀ n) t_st])
  · rwa [show x + (y - x) = y by ring]

/-- Time-Lipschitz bound before `τ_fast`: `‖w s' - w s‖ < n³` if `0 ≤ s ≤ s' ≤ s + 1`, `s' ≤ t`. -/
theorem norm_lt_of_close (hw : IsCyclicPath w) {t : ℝ} (hn : 1 ≤ n)
    (htf : ENNReal.ofReal t < pathTfastCube w n) {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s')
    (h1 : s' ≤ s + 1) (hst : s' ≤ t) : ‖w s' - w s‖ < (n : ℝ) ^ 3 := by
  have hL : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  rcases eq_or_lt_of_le hss with rfl | hlt
  · simpa using hL
  · have := norm_sub_lt_of_lt_pathTfast hw hL hs hlt
      (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) htf)
    have hc : ⌈s' - s⌉₊ ≤ 1 := Nat.ceil_le.2 (by push_cast; linarith)
    calc ‖w s' - w s‖ < (n : ℝ) ^ 3 * ⌈s' - s⌉₊ := this
      _ ≤ (n : ℝ) ^ 3 * 1 := by gcongr; exact_mod_cast hc
      _ = _ := mul_one _

/-- A good block cannot be approached fast (b). -/
theorem nofast_b (_hd : 5 ≤ d) (hβ : 0 < β) (hT : HeavyT d n₀ E n) (hw : IsCyclicPath w)
    {t_st : ℝ} (_ht0 : 0 ≤ t_st) (htf : ENNReal.ofReal t_st < pathTfastCube w n)
    (hgood : ¬ BadByTime d β t₀ n w ι t_st) {x y : ℝ}
    (hx : x ∈ cycIntTimes β) (hxy : x ≤ y) (hy : y ≤ min (x + heavyTkPrime d t₀ n) t_st)
    (hyB : latDist (w y) (heavyBlock (heavyLevel d n) ι) ≤
      2 ^ heavyLevel d n + (n : ℝ) ^ 41) :
    latDist (w x) (heavyBlock (heavyLevel d n) ι) ≤ 2 ^ (heavyLevel d n + 1) := by
  classical
  set k := heavyLevel d n with hk
  set tk := heavyTkPrime d t₀ n with htk
  set B := heavyBlock k ι with hB
  have hBne : B.Nonempty := heavyBlock_nonempty k ι
  have hn1 : 1 ≤ n := by have := hT.t4; omega
  obtain ⟨hT6a, -, -, -⟩ := hT.t6
  have hk1 : 1 ≤ k := by have := hT.t1.2; omega
  have h2k : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h2k1 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
  set f : ℝ → ℝ := fun s => latDist (w s) B with hf
  have hfL : ∀ s s', f s ≤ f s' + ‖w s - w s'‖ := fun s s' => latDist_le_add hBne _ _
  have hy0 : x ≤ t_st := hxy.trans (hy.trans (min_le_right _ _))
  have hx0 : 0 ≤ x := hx.1
  by_contra hcon
  push Not at hcon
  -- the set of cyclic integer times with `f > 2^(k+1)`
  set S : Set ℝ := {z | z ∈ cycIntTimes β ∧ x ≤ z ∧ z ≤ y ∧ (2 : ℝ) ^ (k + 1) < f z} with hS
  have hSx : x ∈ S := ⟨hx, le_rfl, hxy, hcon⟩
  have hSfin : S.Finite := (cycIntTimes_inter_Icc_finite hβ y).subset fun z hz =>
    ⟨hz.1, hx0.trans hz.2.1, hz.2.2.1⟩
  obtain ⟨x₁, hx₁S, hx₁max⟩ := Set.exists_max_image S id hSfin ⟨x, hSx⟩
  obtain ⟨hx₁CI, hxx₁, hx₁y, hfx₁⟩ := hx₁S
  have hytf : y ≤ t_st := hy.trans (min_le_right _ _)
  have hmax : ∀ z ∈ cycIntTimes β, x₁ < z → z ≤ y → f z ≤ 2 ^ (k + 1) := by
    intro z hz h1 h2
    by_contra hc
    push Not at hc
    exact absurd (hx₁max z ⟨hz, hxx₁.trans h1.le, h2, hc⟩) (not_le.2 h1)
  have hT6 : (n : ℝ) ^ 41 + 3 * (n : ℝ) ^ 3 < 2 ^ (k - 1) := hT6a
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hn41 : (0 : ℝ) ≤ (n : ℝ) ^ 41 := by positivity
  by_cases hexists : ∃ e ∈ cycIntTimes β, x₁ < e ∧ e ≤ y
  · -- Case B
    obtain ⟨e, heCI, he1, he2⟩ := hexists
    set m := min (x₁ + 1) y with hm
    have hm0 : 0 ≤ m := le_min (by linarith [hx₁CI.1]) (hx0.trans hxy)
    set z := cycFloor β m with hz
    have hzCI : z ∈ cycIntTimes β := cycFloor_mem hβ hm0
    have hzm : z ≤ m := cycFloor_le hβ
    have hzx₁ : x₁ < z := by
      rcases le_or_gt (x₁ + 1) y with h | h
      · have hmeq : m = x₁ + 1 := min_eq_left h
        have := lt_cycFloor_add_one (x := m) hβ
        rw [← hz, hmeq] at this
        linarith
      · have hmeq : m = y := min_eq_right h.le
        have := le_cycFloor_of_mem hβ hm0 heCI (by rw [hmeq]; exact he2)
        linarith
    have hzy : z ≤ y := hzm.trans (min_le_right _ _)
    have hzx₁1 : z ≤ x₁ + 1 := hzm.trans (min_le_left _ _)
    have hfz : f z ≤ 2 ^ (k + 1) := hmax z hzCI hzx₁ hzy
    have hlip1 := norm_lt_of_close (n := n) hw hn1 htf hx₁CI.1 hzx₁.le hzx₁1 (hzy.trans hytf)
    have hfz2 : 2 ^ (k + 1) - (n : ℝ) ^ 3 < f z := by
      have := hfL x₁ z
      rw [norm_sub_rev] at this
      linarith
    have hyz : y ≤ min (z + tk) t_st :=
      le_min (by linarith [min_le_left (x + tk) t_st, hy, hxx₁, hzx₁]) hytf
    have hzB : latDist (w z) B ≤ 2 ^ (k + 2) := by
      have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (k + 2) := by
        rw [pow_succ _ (k + 1)]; nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) (k + 1)]
      exact hfz.trans this
    have ha := nofast_a (n := n) hgood hzCI hzy hyz hzB
    have h3 := hfL z y
    rw [norm_sub_rev] at h3
    have h5 : f y ≤ 2 ^ k + (n : ℝ) ^ 41 := hyB
    linarith
  · -- Case A
    push Not at hexists
    have hxy' : x ≤ cycFloor β y := le_cycFloor_of_mem hβ (hx0.trans hxy) hx hxy
    have hcfCI : cycFloor β y ∈ cycIntTimes β := cycFloor_mem hβ (hx0.trans hxy)
    have hcf : cycFloor β y ≤ x₁ := by
      by_contra hc
      push Not at hc
      exact absurd (cycFloor_le hβ) (not_le.2 (hexists _ hcfCI hc))
    have hyx₁ : y ≤ x₁ + 1 := by
      have := lt_cycFloor_add_one (x := y) hβ
      linarith
    have hlip := norm_lt_of_close (n := n) hw hn1 htf hx₁CI.1 hx₁y hyx₁ hytf
    have := hfL x₁ y
    rw [norm_sub_rev] at this
    have h5 : f y ≤ 2 ^ k + (n : ℝ) ^ 41 := hyB
    linarith

end ElboimSly.Paper
