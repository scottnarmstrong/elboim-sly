/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Setting2
public import ElboimSly.Paper.Heavy.Es6FourMain
public import Mathlib

/-!
# The count `|N(V,1) ∩ [-r,r]^d| ≤ r^{8/3}` and the cover of `N(V,1.9ⁿ)`

One excursion succeeds with probability at least frac12, "Hitting `N(V,1)`" and "The far event". Both are deterministic
statements about `V = W₁([0,T])` on `ℋ_1`.

* `step78_count_V`: `|N(V,1) ∩ B(x,r)| ≤ 3^d |V ∩ B(x,r+1)| < 3^d (r+1)^{5/2} ≤ r^{8/3}` for
  `r ≥ L` (ES22 Lemma 6.4, `es6_four`: `V` has no heavy ball of radius `≥ t_n^δ`).
* `step78_cover_V`: on `Osc_1`, `N(V,1.9ⁿ) ⊆ ⋃_{j ≤ ⌊T/3.6ⁿ⌋} B(W₁(j 3.6ⁿ), 2·1.9ⁿ)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper

variable {d : ℕ}

/-- The ball `{e : ‖e‖ ≤ 1}` of `ℤ^d` has at most `3^d` points. -/
theorem ncard_unitBall_le : ({e : Fin d → ℤ | ‖e‖ ≤ 1}).ncard ≤ 3 ^ d := by
  have hsub : {e : Fin d → ℤ | ‖e‖ ≤ 1} ⊆
      ↑(Fintype.piFinset fun _ : Fin d => (Finset.Icc (-1 : ℤ) 1)) := by
    intro e he
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h1 : ‖e i‖ ≤ 1 := (norm_le_pi_norm e i).trans he
    rw [Int.norm_eq_abs] at h1
    have := abs_le.1 (by exact_mod_cast h1 : |e i| ≤ 1)
    exact this
  calc _ ≤ (↑(Fintype.piFinset fun _ : Fin d => (Finset.Icc (-1 : ℤ) 1)) :
        Set (Fin d → ℤ)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Fintype.piFinset fun _ : Fin d => (Finset.Icc (-1 : ℤ) 1)).card :=
        Set.ncard_coe_finset _
    _ = 3 ^ d := by simp [Fintype.card_piFinset]

theorem finite_ball_int (x : Fin d → ℤ) (r : ℝ) : {v : Fin d → ℤ | ‖v - x‖ ≤ r}.Finite := by
  have : {v : Fin d → ℤ | ‖v - x‖ ≤ r} ⊆ Set.pi univ (fun i => Icc (x i - ⌈r⌉) (x i + ⌈r⌉)) := by
    intro v hv i _
    have h1 : ‖v i - x i‖ ≤ r := (norm_le_pi_norm (v - x) i).trans hv
    rw [Int.norm_eq_abs] at h1
    have h2 : |((v i - x i : ℤ) : ℝ)| ≤ r := by exact_mod_cast h1
    have h3 := abs_le.1 h2
    have h4 : ((v i - x i : ℤ) : ℝ) ≤ ⌈r⌉ := h3.2.trans (Int.le_ceil r)
    have h5 : -(⌈r⌉ : ℝ) ≤ ((v i - x i : ℤ) : ℝ) := by
      have := Int.le_ceil r
      linarith [h3.1]
    have h4' : v i - x i ≤ ⌈r⌉ := by exact_mod_cast h4
    have h5' : -⌈r⌉ ≤ v i - x i := by exact_mod_cast h5
    constructor <;> omega
  exact (Set.Finite.pi (fun i => Set.finite_Icc _ _)).subset this

/-- The numerical step `3^d (r+1)^{5/2} ≤ r^{8/3}` for `r ≥ (6·3^d)^6`. -/
theorem step78_count_arith {r : ℝ} (hr : (6 * 3 ^ d : ℝ) ^ 6 ≤ r) :
    (3 : ℝ) ^ d * (r + 1) ^ (5 / 2 : ℝ) ≤ r ^ (8 / 3 : ℝ) := by
  have hK : (1 : ℝ) ≤ 6 * 3 ^ d := by
    have : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
    linarith
  have hr1 : 1 ≤ r := le_trans (one_le_pow₀ hK) hr
  have hr0 : 0 < r := by linarith
  have h1 : (r + 1) ^ (5 / 2 : ℝ) ≤ 6 * r ^ (5 / 2 : ℝ) := by
    have h2 : r + 1 ≤ 2 * r := by linarith
    calc (r + 1) ^ (5 / 2 : ℝ) ≤ (2 * r) ^ (5 / 2 : ℝ) :=
          Real.rpow_le_rpow (by linarith) h2 (by norm_num)
      _ = 2 ^ (5 / 2 : ℝ) * r ^ (5 / 2 : ℝ) := Real.mul_rpow (by norm_num) hr0.le
      _ ≤ 6 * r ^ (5 / 2 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have : (2 : ℝ) ^ (5 / 2 : ℝ) ≤ 6 := by
            have e : ((2 : ℝ) ^ (5 / 2 : ℝ)) ^ 2 = 32 := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
              norm_num
            nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (5 / 2 : ℝ)]
          exact this
  have h3 : 6 * (3 : ℝ) ^ d ≤ r ^ (1 / 6 : ℝ) := by
    have : (6 * 3 ^ d : ℝ) = ((6 * 3 ^ d : ℝ) ^ 6) ^ (1 / 6 : ℝ) := by
      have h := Real.pow_rpow_inv_natCast (x := 6 * 3 ^ d) (n := 6) (by positivity) (by norm_num)
      rw [show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num]
      exact h.symm
    rw [this]
    exact Real.rpow_le_rpow (by positivity) hr (by norm_num)
  have e : r ^ (8 / 3 : ℝ) = r ^ (5 / 2 : ℝ) * r ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_add hr0]; norm_num
  rw [e]
  calc (3 : ℝ) ^ d * (r + 1) ^ (5 / 2 : ℝ) ≤ 3 ^ d * (6 * r ^ (5 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (6 * 3 ^ d) * r ^ (5 / 2 : ℝ) := by ring
    _ ≤ r ^ (1 / 6 : ℝ) * r ^ (5 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = _ := by ring

variable {n₀ n : ℕ} {E : HeavyEscConsts} {t₀ : ℝ} {w : ℝ → Fin d → ℤ}

/-- **The count** `|N(V,1) ∩ [-r,r]^d| ≤ r^{8/3}`, `V = w([0,T])`, for `r ≥ L`. -/
theorem step78_count_V (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n)
    (hw : IsCyclicPath w) {T : ℝ} (hT0 : 0 ≤ T) (hj : ENNReal.ofReal T < pathTjumpCube w n)
    (hτ : ENNReal.ofReal T < heavyTauPrime d t₀ n w) (x : Fin d → ℤ) {L : ℝ}
    (hL1 : indScale t₀ n ^ indDelta d ≤ L) (hL2 : (6 * 3 ^ d : ℝ) ^ 6 ≤ L) {r : ℝ} (hr : L ≤ r) :
    (({u : Fin d → ℤ | ∃ v ∈ w '' Icc 0 T, ‖x + u - v‖ ≤ 1} ∩ {u | ‖u‖ ≤ r}).ncard : ℝ) ≤
      r ^ (8 / 3 : ℝ) := by
  have hr0 : 0 ≤ r := le_trans (le_trans (by positivity) hL2) hr
  have hnh := es6_four hd ht1 ht4 hT hw hT0 hj hτ x (r := r + 1) (by linarith)
  have hlt : (({v : Fin d → ℤ | ‖v - x‖ ≤ r + 1} ∩ visitedSet w 0 T).ncard : ℝ) <
      (r + 1) ^ (5 / 2 : ℝ) := by
    by_contra hge
    exact hnh ⟨by linarith, not_lt.1 hge⟩
  set Vr : Set (Fin d → ℤ) := {v | ‖v - x‖ ≤ r + 1} ∩ visitedSet w 0 T with hVr
  have hVrf : Vr.Finite := (finite_ball_int x (r + 1)).subset inter_subset_left
  have hsub : ({u : Fin d → ℤ | ∃ v ∈ w '' Icc 0 T, ‖x + u - v‖ ≤ 1} ∩ {u | ‖u‖ ≤ r}) ⊆
      (fun p : (Fin d → ℤ) × (Fin d → ℤ) => p.1 - x + p.2) '' (Vr ×ˢ {e : Fin d → ℤ | ‖e‖ ≤ 1}) := by
    rintro u ⟨⟨v, hv, hvn⟩, hu⟩
    refine ⟨(v, x + u - v), ⟨⟨?_, hv⟩, hvn⟩, by simp⟩
    show ‖v - x‖ ≤ r + 1
    have : v - x = u - (x + u - v) := by abel
    rw [this]
    calc ‖u - (x + u - v)‖ ≤ ‖u‖ + ‖x + u - v‖ := norm_sub_le _ _
      _ ≤ r + 1 := by simp only [mem_ofPred_eq] at hu; linarith
  have hfin : (Vr ×ˢ {e : Fin d → ℤ | ‖e‖ ≤ 1}).Finite :=
    hVrf.prod (by simpa using finite_ball_int (d := d) 0 1)
  calc (((({u : Fin d → ℤ | ∃ v ∈ w '' Icc 0 T, ‖x + u - v‖ ≤ 1} ∩ {u | ‖u‖ ≤ r})).ncard : ℕ) : ℝ)
      ≤ (((Vr ×ˢ {e : Fin d → ℤ | ‖e‖ ≤ 1}).ncard : ℕ) : ℝ) := by
        exact_mod_cast (Set.ncard_le_ncard hsub (hfin.image _)).trans (Set.ncard_image_le hfin)
    _ = (Vr.ncard : ℝ) * (({e : Fin d → ℤ | ‖e‖ ≤ 1}).ncard : ℝ) := by
        rw [Set.ncard_prod]; push_cast; ring
    _ ≤ (Vr.ncard : ℝ) * 3 ^ d := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact_mod_cast ncard_unitBall_le
    _ ≤ (r + 1) ^ (5 / 2 : ℝ) * 3 ^ d :=
        mul_le_mul_of_nonneg_right hlt.le (by positivity)
    _ = 3 ^ d * (r + 1) ^ (5 / 2 : ℝ) := by ring
    _ ≤ _ := step78_count_arith (hL2.trans hr)

/-- **The cover of `N(V, 1.9ⁿ)`**: on `Osc_1`, `V = W₁([0,T])` is covered by the balls of radius
`1.9ⁿ` around `W₁(j·3.6ⁿ)`, `0 ≤ j ≤ ⌊T/3.6ⁿ⌋`. -/
theorem step78_cover_V {W : ℝ → Fin d → ℤ} {T : ℝ} (hT : 0 ≤ T) (hosc : Step78Osc n T W) :
    ∃ Z : Finset (Fin d → ℤ), (∀ v ∈ W '' Icc 0 T, ∃ z ∈ Z, ‖v - z‖ ≤ (19 / 10 : ℝ) ^ n) ∧
      (Z.card : ℝ) ≤ T / (3.6 : ℝ) ^ n + 1 := by
  set h : ℝ := (3.6 : ℝ) ^ n with hh
  have hh0 : 0 < h := by positivity
  set J : ℕ := ⌊T / h⌋₊ with hJ
  refine ⟨(Finset.range (J + 1)).image fun j : ℕ => W ((j : ℝ) * h), ?_, ?_⟩
  · rintro v ⟨s, ⟨hs0, hsT⟩, rfl⟩
    set j : ℕ := ⌊s / h⌋₊ with hj
    have hjs : (j : ℝ) * h ≤ s := by
      have := Nat.floor_le (div_nonneg hs0 hh0.le)
      rw [← hj] at this
      rwa [le_div_iff₀ hh0] at this
    have hsj : s < ((j : ℝ) + 1) * h := by
      have := Nat.lt_floor_add_one (s / h)
      rw [← hj, div_lt_iff₀ hh0] at this
      exact this
    have hjJ : j ≤ J := Nat.floor_le_floor (div_le_div_of_nonneg_right hsT hh0.le)
    have hjT : (j : ℝ) * h ≤ T := hjs.trans hsT
    refine ⟨W ((j : ℝ) * h), Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩, ?_⟩
    have := hosc s ⟨hs0, hsT⟩ ((j : ℝ) * h) ⟨by positivity, hjT⟩
      (by rw [abs_of_nonneg (by linarith)]; linarith)
    have e : (1.9 : ℝ) = 19 / 10 := by norm_num
    rw [e] at this
    exact this
  · calc (((Finset.range (J + 1)).image fun j : ℕ => W ((j : ℝ) * h)).card : ℝ)
        ≤ ((Finset.range (J + 1)).card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ = (J : ℝ) + 1 := by simp
      _ ≤ T / h + 1 := by
          have := Nat.floor_le (div_nonneg hT hh0.le)
          linarith

end ElboimSly.Paper.Step

end
