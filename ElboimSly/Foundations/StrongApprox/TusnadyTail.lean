/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.TusnadyErr
public import ElboimSly.Foundations.StrongApprox.Perturb

/-!
# Upper and lower tail comparison for the binomial

Tusn'ady-type bound for Bin(m,frac12), Steps 3 and 4.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal Real ENNReal

namespace ElboimSly
namespace StrongApprox

theorem upper_alg {s x x' : ℝ} (hs : 4000 ≤ s) (hx0 : 0 ≤ x) (hxs : x ≤ s / 9600)
    (hx' : x' = x + (2500 * (1 + x ^ 2) - 1 / 2) / s) :
    x' ≤ 2 * x + 1 ∧ x + 1 / s ≤ x' - 17 * (24 / s) * (1 + x' ^ 2) := by
  have hs0 : 0 < s := by linarith
  have h1 : 2500 * (1 + x ^ 2) / s ≤ 1 + x := by
    rw [div_le_iff₀ hs0]
    linarith only [mul_nonneg hx0 (sub_nonneg.2 hxs), mul_nonneg hx0 hs0.le, hs]
  have hh : (2500 * (1 + x ^ 2) - 1 / 2) / s ≤ 1 + x := by
    refine le_trans ?_ h1
    gcongr; linarith
  have hx'1 : x' ≤ 2 * x + 1 := by rw [hx']; linarith
  have hx'0 : x ≤ x' := by
    rw [hx']
    have : 0 ≤ (2500 * (1 + x ^ 2) - 1 / 2) / s := by
      apply div_nonneg _ hs0.le; linarith only [sq_nonneg x]
    linarith
  refine ⟨hx'1, ?_⟩
  have h2 : 1 + x' ^ 2 ≤ 6 * (1 + x ^ 2) := by
    have hsq : x' ^ 2 ≤ (2 * x + 1) ^ 2 := pow_le_pow_left₀ (hx0.trans hx'0) hx'1 2
    linarith only [hsq, sq_nonneg (x - 1)]
  have h3 : 17 * (24 / s) * (1 + x' ^ 2) ≤ 17 * (24 / s) * (6 * (1 + x ^ 2)) := by gcongr
  have e : 17 * (24 / s) * (6 * (1 + x ^ 2)) = 2448 * (1 + x ^ 2) / s := by field_simp; ring
  have h4 : x + 1 / s ≤ x + (2500 * (1 + x ^ 2) - 1 / 2) / s - 2448 * (1 + x ^ 2) / s := by
    have : (2500 * (1 + x ^ 2) - 1 / 2) / s - 2448 * (1 + x ^ 2) / s =
        (52 * (1 + x ^ 2) - 1 / 2) / s := by field_simp; ring
    have h5 : 1 / s ≤ (52 * (1 + x ^ 2) - 1 / 2) / s := by
      gcongr; linarith only [sq_nonneg x]
    linarith
  rw [hx'] at h3 ⊢
  rw [e] at h3
  linarith

theorem lower_alg {s x v : ℝ} (hs : 4000 ≤ s) (hv0 : 0 ≤ v)
    (hvx : v ≤ x - (2500 * (1 + x ^ 2) - 1 / 2) / s) :
    v + 10 * (24 / s) * (1 + v ^ 2) ≤ x - 1 / s := by
  have hs0 : 0 < s := by linarith
  have hx : v ≤ x := by
    have : 0 ≤ (2500 * (1 + x ^ 2) - 1 / 2) / s := by
      apply div_nonneg _ hs0.le; linarith only [sq_nonneg x]
    linarith
  have h1 : v ^ 2 ≤ x ^ 2 := by gcongr
  have h2 : 10 * (24 / s) * (1 + v ^ 2) ≤ 240 * (1 + x ^ 2) / s := by
    have : 10 * (24 / s) * (1 + x ^ 2) = 240 * (1 + x ^ 2) / s := by field_simp; norm_num
    rw [← this]; gcongr
  have h3 : 1 / s ≤ (2260 * (1 + x ^ 2) - 1 / 2) / s := by
    gcongr; linarith only [sq_nonneg x]
  have e : (2500 * (1 + x ^ 2) - 1 / 2) / s - 240 * (1 + x ^ 2) / s =
      (2260 * (1 + x ^ 2) - 1 / 2) / s := by field_simp; ring
  linarith

theorem exp_neg_le_one_sub {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 2 / 3) : Real.exp (-u) ≤ 1 - u / 2 := by
  have := (abs_le.1 (abs_exp_sub_one_sub_le (u := -u) (by rw [abs_neg, abs_of_nonneg h0]; linarith))).2
  linarith only [this, mul_le_mul_of_nonneg_left h1 h0]

theorem g_mono {a V vj x' : ℝ} (ha0 : 0 < a) (haV : a * V ≤ 1 / 100) (_hx0 : 0 ≤ x')
    (hxv : x' ≤ vj) (hvV : vj ≤ V) :
    x' - 17 * a * (1 + x' ^ 2) ≤ vj - 17 * a * (1 + vj ^ 2) := by
  have h1 : a * vj ≤ a * V := by gcongr
  have h2 : a * x' ≤ a * V := by gcongr; linarith
  have h3 : 17 * a * (vj + x') ≤ 1 := by linarith only [h1, h2, haV]
  have h4 : 0 ≤ vj - x' := by linarith
  have h5 : vj - 17 * a * (1 + vj ^ 2) - (x' - 17 * a * (1 + x' ^ 2)) =
      (vj - x') * (1 - 17 * a * (vj + x')) := by ring
  linarith only [h5, mul_nonneg h4 (sub_nonneg.2 h3)]

theorem upper_combine {T I P1 Pb e s : ℝ} (hs : 0 < s) (h1 : T ≤ I + e) (h2 : I ≤ P1)
    (h3 : P1 ≤ Real.exp (-(1 / s) / 6) * Pb) (hu : Real.exp (-(1 / s) / 6) ≤ 1 - 1 / (12 * s))
    (he : e ≤ Pb / (12 * s)) (hPb : 0 ≤ Pb) : T ≤ Pb := by
  have h4 : Real.exp (-(1 / s) / 6) * Pb ≤ (1 - 1 / (12 * s)) * Pb := by gcongr
  have h5 : (1 - 1 / (12 * s)) * Pb + Pb / (12 * s) = Pb := by field_simp; ring
  linarith only [h1, h2, h3, h4, h5, he]

/-- Tusn'ady-type bound for Bin(m,frac12), Step 3 (upper tail comparison). -/
theorem tus_upper_tail {m : ℕ} (hm : 2000000000 ≤ m) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ tV m / 4)
    {n : ℕ} (hn : (m : ℝ) / 2 + sbS m * x + 2500 * (1 + x ^ 2) ≤ n) :
    sabT m n ≤ saPhib x := by
  have hm' : (2000000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : 1 ≤ m := by omega
  have hs := four_thousand_le_sbS hm
  have hs0 := sbS_pos m
  have hVs := tV_le_sbS (m := m)
  have hsV := sbS_mul_tV_le (m := m)
  have hsV2 := sbS_mul_tV_ge (m := m)
  have hV0 : 0 < tV m := tV_pos hm1
  obtain ⟨ld1, ld2, ld3⟩ := tus_ld hm hx0 hx
  set s := sbS m with hsd
  set V := tV m with hVd
  have hsx : 0 ≤ s * x := by positivity
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  by_cases hnm : m < n
  · rw [sabT_of_gt m (by exact_mod_cast hnm)]; exact saPhib_nonneg x
  rw [not_lt] at hnm
  set vj : ℝ := ((n : ℝ) - 1 / 2 - m / 2) / s with hvj
  by_cases hfar : V < vj
  · -- far tail
    have hfar' : s * V + 1 / 2 < (n : ℝ) - m / 2 := by
      rw [hvj, lt_div_iff₀ hs0] at hfar; linarith
    have hρ : 0 ≤ s * V := by positivity
    have h1 := sabT_le_exp (m := m) hm1 (n := n) hρ (fun i hi => by
      have : (n : ℝ) ≤ i := by exact_mod_cast hi
      linarith)
    refine le_trans h1 (le_trans (Real.exp_le_exp.2 ?_) ld2)
    have hs2 := sbS_sq_ge (m := m)
    rw [← hsd] at hs2
    have hmpos : (0 : ℝ) < m := by linarith
    rw [neg_le_neg_iff, le_div_iff₀ hmpos]
    have : (s * V) ^ 2 = s ^ 2 * V ^ 2 := by ring
    linarith only [this, mul_le_mul_of_nonneg_left hs2 (sq_nonneg V)]
  · rw [not_lt] at hfar
    have hj0 : (m : ℝ) / 2 + 1 / 2 ≤ n := by linarith only [hn, hsx, hx2]
    obtain ⟨hR0, hR1⟩ := tus_split hm hj0 hnm hfar
    have hR0' : 0 ≤ sabT m n - ∫ v in vj..V, tG m v := hR0
    have hR1' : sabT m n - ∫ v in vj..V, tG m v ≤ Real.exp (-(V ^ 2 / 4)) := hR1
    -- the perturbation
    have hvj0 : 0 ≤ vj := by rw [hvj]; apply div_nonneg _ hs0.le; linarith only [hj0]
    have ha0 : 0 < 24 / s := by positivity
    have ha1 : 24 / s ≤ 1 / 100 := by rw [div_le_iff₀ hs0]; linarith
    have haV : 24 / s * V ≤ 1 / 100 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hs0]; linarith
    have hI : ∫ v in vj..V, tG m v = ∫ v in vj..V, saphi v * Real.exp (tE m v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le hfar] at hv
      exact tG_eq hm (hvj0.trans hv.1) hv.2
    have hP := perturb_upper (a := 24 / s) (V := V) ha0 ha1 haV (measurable_tE m)
      (fun v hv => tE_abs_le hm hv.1 hv.2) (v0 := vj) ⟨hvj0, hfar⟩
    rw [← hI] at hP
    -- lower bound on vj and the inequality for g
    set x' : ℝ := x + (2500 * (1 + x ^ 2) - 1 / 2) / s with hx'
    have hxs : x ≤ s / 9600 := by linarith
    obtain ⟨hx'1, hg⟩ := upper_alg (s := s) hs hx0 hxs hx'
    have hx'vj : x' ≤ vj := by
      rw [hx', hvj]
      have : x + (2500 * (1 + x ^ 2) - 1 / 2) / s = (s * x + 2500 * (1 + x ^ 2) - 1 / 2) / s := by
        field_simp; ring
      rw [this]
      apply div_le_div_of_nonneg_right _ hs0.le
      linarith
    have hx'0 : 0 ≤ x' := by
      rw [hx']
      have : 0 ≤ (2500 * (1 + x ^ 2) - 1 / 2) / s := by
        apply div_nonneg _ hs0.le; linarith only [hx2]
      linarith
    have hmono := g_mono ha0 haV hx'0 hx'vj hfar
    have hΦ1 : saPhib (vj - 17 * (24 / s) * (1 + vj ^ 2)) ≤ saPhib (x + 1 / s) :=
      saPhib_antitone (by linarith only [hg, hmono])
    have hΦ2 := saPhib_add_le (t := x) (δ := 1 / s) hx0 (by positivity)
      (by rw [div_le_one hs0]; linarith)
    have hu : Real.exp (-(1 / s) / 6) ≤ 1 - 1 / (12 * s) := by
      have := exp_neg_le_one_sub (u := 1 / (6 * s)) (by positivity)
        (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
      have e1 : -(1 / s) / 6 = -(1 / (6 * s)) := by field_simp
      have e2 : 1 / (6 * s) / 2 = 1 / (12 * s) := by field_simp; ring
      rw [e1]; rw [e2] at this; exact this
    exact upper_combine hs0 (by linarith only [hR1']) (hP.trans hΦ1) hΦ2 hu ld1 (saPhib_nonneg x)

theorem saPhib_zero : saPhib 0 = 1 / 2 := by
  have := saPhi_neg 0
  rw [neg_zero] at this
  unfold saPhib at *
  linarith

theorem sabT_ge_half (m : ℕ) {j : ℤ} (hj : 2 * j ≤ m) : 1 / 2 ≤ sabT m j := by
  classical
  refine le_trans (sab_half_le_sum m) ?_
  unfold sabT
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases h : (m : ℝ) / 2 ≤ k
  · have : j ≤ (k : ℤ) := by
      have : (m : ℤ) ≤ 2 * k := by exact_mod_cast (by linarith : (m : ℝ) ≤ 2 * k)
      omega
    simp [h, this]
  · simp only [h, ite_false]
    split_ifs <;> first | exact sab_nonneg m k | exact le_rfl

theorem sabT_ge_half_add (m : ℕ) {n : ℕ} (hnm : n ≤ m) (hn : 2 * n < m) :
    1 / 2 + sab m n ≤ sabT m n := by
  classical
  have hS := sab_half_le_sum m
  have hsum : ∑ k ∈ Finset.range (m + 1), (if k = n then sab m k else 0) = sab m n := by
    rw [Finset.sum_ite_eq' (Finset.range (m + 1)) n (fun k => sab m k)]
    simp; omega
  have : (∑ k ∈ Finset.range (m + 1), if (m : ℝ) / 2 ≤ k then sab m k else 0) +
      ∑ k ∈ Finset.range (m + 1), (if k = n then sab m k else 0) ≤ sabT m n := by
    rw [← Finset.sum_add_distrib]
    unfold sabT
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases h1 : k = n
    · subst h1
      have : ¬ (m : ℝ) / 2 ≤ k := by
        have : (2 * k : ℝ) < m := by exact_mod_cast hn
        linarith
      simp [this]
    · by_cases h2 : (m : ℝ) / 2 ≤ k
      · have : (n : ℤ) ≤ k := by
          have : (m : ℝ) ≤ 2 * k := by linarith
          have : (m : ℤ) ≤ 2 * k := by exact_mod_cast this
          omega
        simp [h1, h2, this]
      · simp only [h1, h2, ite_false, add_zero]
        split_ifs <;> first | exact sab_nonneg m k | exact le_rfl
  linarith

theorem lower_combine {T I P1 PV Pb Ps c : ℝ} (hI : I ≤ T) (h1 : P1 - PV ≤ I) (h2 : Ps ≤ P1)
    (h3 : Real.exp c * Pb ≤ Ps) (_hc : 0 ≤ c) (hPb : 0 ≤ Pb) (hV : PV < c * Pb) : Pb < T := by
  have h4 : (1 + c) * Pb ≤ Real.exp c * Pb := by
    have := Real.add_one_le_exp c
    exact mul_le_mul_of_nonneg_right (by linarith only [this]) hPb
  linarith only [hI, h1, h2, h3, h4, hV]

/-- Tusn'ady-type bound for Bin(m,frac12), Step 4 (lower tail comparison). -/
theorem tus_lower_tail {m : ℕ} (hm : 2000000000 ≤ m) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ tV m / 4)
    {j : ℤ} (hj : (j : ℝ) ≤ m / 2 + sbS m * x - 2500 * (1 + x ^ 2) + 1) :
    saPhib x < sabT m j := by
  have hm' : (2000000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : 1 ≤ m := by omega
  have hs := four_thousand_le_sbS hm
  have hs0 := sbS_pos m
  have hVs := tV_le_sbS (m := m)
  have hsV := sbS_mul_tV_le (m := m)
  have hsV2 := sbS_mul_tV_ge (m := m)
  have hV0 : 0 < tV m := tV_pos hm1
  obtain ⟨ld1, ld2, ld3⟩ := tus_ld hm hx0 hx
  set s := sbS m with hsd
  set V := tV m with hVd
  have hsx : 0 ≤ s * x := by positivity
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  by_cases hlow : (j : ℝ) < m / 2 + 1 / 2
  · have hj2 : 2 * j ≤ m := by
      have : (2 * j : ℝ) < m + 1 := by linarith
      have : 2 * j < (m : ℤ) + 1 := by exact_mod_cast this
      omega
    have hT := sabT_ge_half m hj2
    rcases hx0.eq_or_lt with hx00 | hxp
    · -- x = 0
      subst hx00
      rw [saPhib_zero]
      by_cases hneg : j < 0
      · have : sabT m j = 1 := by
          have h := sabF_add_sabT m j
          rw [sabF_of_neg m (by omega)] at h
          linarith
        rw [this]; norm_num
      · rw [not_lt] at hneg
        obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hneg
        have hnm : n < m := by
          have : (n : ℝ) < m := by push_cast at hj; linarith only [hj, hm']
          exact_mod_cast this
        have h2n : 2 * n < m := by
          have : (2 * n : ℝ) < m := by push_cast at hj; linarith only [hj, hm']
          exact_mod_cast this
        have := sabT_ge_half_add m hnm.le h2n
        have hp : 0 < sab m n := sab_pos (by omega) (by omega)
        linarith
    · calc saPhib x < saPhib 0 := saPhib_strictAnti hxp
        _ = 1 / 2 := saPhib_zero
        _ ≤ sabT m j := hT
  · rw [not_lt] at hlow
    have hjpos : (0 : ℤ) ≤ j := by
      have : (0 : ℝ) ≤ j := by linarith
      exact_mod_cast this
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hjpos
    push_cast at hlow hj
    set vj : ℝ := ((n : ℝ) - 1 / 2 - m / 2) / s with hvj
    have hvj0 : 0 ≤ vj := by rw [hvj]; apply div_nonneg _ hs0.le; linarith
    have hvjx : vj ≤ x - (2500 * (1 + x ^ 2) - 1 / 2) / s := by
      rw [hvj]
      have : x - (2500 * (1 + x ^ 2) - 1 / 2) / s = (s * x - 2500 * (1 + x ^ 2) + 1 / 2) / s := by
        field_simp; ring
      rw [this]
      apply div_le_div_of_nonneg_right _ hs0.le
      linarith
    have hvjX : vj ≤ x := by
      have : 0 ≤ (2500 * (1 + x ^ 2) - 1 / 2) / s := by
        apply div_nonneg _ hs0.le; linarith only [hx2]
      linarith
    have hvjV : vj ≤ V := by linarith
    have hnm : n ≤ m := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 : (m : ℝ) + 1 ≤ n := by exact_mod_cast hcon
      have h2 : 2 * s ≤ vj := by
        rw [hvj, le_div_iff₀ hs0]
        have := sbS_sq m
        rw [← hsd] at this
        linarith only [this, h1]
      linarith
    obtain ⟨hR0, hR1⟩ := tus_split hm hlow hnm hvjV
    have hR0' : 0 ≤ sabT m n - ∫ v in vj..V, tG m v := hR0
    have ha0 : 0 < 24 / s := by positivity
    have ha1 : 24 / s ≤ 1 / 100 := by rw [div_le_iff₀ hs0]; linarith
    have haV : 24 / s * V ≤ 1 / 100 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hs0]; linarith
    have hI : ∫ v in vj..V, tG m v = ∫ v in vj..V, saphi v * Real.exp (tE m v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le hvjV] at hv
      exact tG_eq hm (hvj0.trans hv.1) hv.2
    have hP := perturb_lower (a := 24 / s) (V := V) ha0 ha1 haV (measurable_tE m)
      (fun v hv => tE_abs_le hm hv.1 hv.2) (v0 := vj) ⟨hvj0, hvjV⟩
    rw [← hI] at hP
    have hlow2 := lower_alg (s := s) (x := x) hs hvj0 hvjx
    have hΦ1 : saPhib (x - 1 / s) ≤ saPhib (vj + 10 * (24 / s) * (1 + vj ^ 2)) :=
      saPhib_antitone hlow2
    have hshift := exp_mul_saPhib_le (t := x) (c := 1 / (6 * s)) (by linarith) (by positivity)
      (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    have e : x - 6 * (1 / (6 * s)) = x - 1 / s := by field_simp
    rw [e] at hshift
    refine lower_combine (T := sabT m n) (I := ∫ v in vj..V, tG m v)
      (P1 := saPhib (vj + 10 * (24 / s) * (1 + vj ^ 2))) (PV := saPhib V) (Pb := saPhib x)
      (Ps := saPhib (x - 1 / s)) (c := 1 / (6 * s)) (by linarith only [hR0']) hP hΦ1 hshift
      (by positivity) (saPhib_nonneg x) ?_
    have : saPhib x / (6 * s) = 1 / (6 * s) * saPhib x := by ring
    rw [← this]; exact ld3

end StrongApprox
end ElboimSly
