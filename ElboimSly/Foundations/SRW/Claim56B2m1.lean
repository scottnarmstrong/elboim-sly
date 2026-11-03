/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Claim56Geom
public import Mathlib

/-!
# Claim 5.6, event `𝓑_{2m+1}`

ES22 Claim 5.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

theorem sideLen_cast (j : ℕ) (hj : 1 ≤ j) (i : Fin d) :
    ((sideLen d j i : ℕ) : ℝ) = if i.val = 0 then (2 : ℝ) ^ j / 2 else (2 : ℝ) ^ j := by
  unfold sideLen
  split_ifs
  · push_cast
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp [pow_succ]
  · push_cast; rfl

theorem mem_first_iff (w z : ℤ) (ℓ : ℕ) :
    z ∈ Icc (w - ℓ + 1) (w - ℓ + 1 + (ℓ : ℤ) - 1) ↔ (w : ℝ) - ℓ + 1 ≤ z ∧ (z : ℝ) ≤ w := by
  have e1 : ((w : ℝ) - ℓ + 1 ≤ z) ↔ (w - ℓ + 1 ≤ z) := by norm_cast
  have e2 : ((z : ℝ) ≤ w) ↔ z ≤ w := by norm_cast
  rw [e1, e2, mem_Icc]
  constructor <;> rintro ⟨a, b⟩ <;> constructor <;> omega

theorem mem_other_iff (w z : ℤ) (ℓ : ℕ) :
    z ∈ Icc (w - ℓ) (w - ℓ + ((2 * ℓ + 1 : ℕ) : ℤ) - 1) ↔
      (w : ℝ) - ℓ ≤ z ∧ (z : ℝ) ≤ w + ℓ := by
  have e1 : ((w : ℝ) - ℓ ≤ z) ↔ (w - ℓ ≤ z) := by norm_cast
  have e2 : ((z : ℝ) ≤ w + ℓ) ↔ z ≤ w + ℓ := by norm_cast
  rw [e1, e2, mem_Icc]
  constructor <;> rintro ⟨a, b⟩ <;> constructor <;> push_cast at * <;> omega

/-- First-coordinate estimate. -/
theorem coord_first {s P N μ x w q : ℝ} (hs : 288 ≤ s) (hP : 8 ≤ P) (hN1 : P * s ≤ N)
    (hN2 : N ≤ 2 * P * s) (hμ1 : 0.77 ≤ μ * P) (hμ2 : μ * P ≤ 1) (hμ0 : 0 ≤ μ)
    (hq : q = w - (N / 4 - 1)) (hx : |x - (μ * q + (1 - μ) * w)| ≤ s / 32) :
    w - s + 1 ≤ x ∧ x ≤ w := by
  have hP0 : 0 < P := by linarith
  have hN0 : 0 < N := by nlinarith
  have hlo : 0.77 * s ≤ μ * N := by
    calc 0.77 * s ≤ (μ * P) * s := by gcongr
      _ = μ * (P * s) := by ring
      _ ≤ μ * N := by gcongr
  have hhi : μ * N ≤ 2 * s := by
    calc μ * N ≤ μ * (2 * P * s) := by gcongr
      _ = 2 * (μ * P) * s := by ring
      _ ≤ 2 * 1 * s := by gcongr
      _ = 2 * s := by ring
  have hNbig : 2304 ≤ N := by nlinarith
  rw [abs_le] at hx
  have e : μ * q + (1 - μ) * w = w - μ * (N / 4 - 1) := by rw [hq]; ring
  rw [e] at hx
  have a1 : μ * (N / 4 - 1) ≥ μ * N / 8 := by
    have : N / 4 - 1 ≥ N / 8 := by linarith
    nlinarith
  have a2 : μ * (N / 4 - 1) ≤ μ * N / 4 := by nlinarith
  constructor <;> nlinarith [hx.1, hx.2]

/-- Other coordinates. -/
theorem coord_other {s P N μ x w q : ℝ} (hs : 288 ≤ s) (hP : 8 ≤ P) (hN2 : N ≤ 2 * P * s)
    (hμ2 : μ * P ≤ 1) (hμ0 : 0 ≤ μ) (_hN0 : 0 < N) (hq : |q - w| ≤ N / 4)
    (hx : |x - (μ * q + (1 - μ) * w)| ≤ s / 32) : |x - w| ≤ s / 32 + s / 2 := by
  have hP0 : 0 < P := by linarith
  have hhi : μ * N ≤ 2 * s := by
    calc μ * N ≤ μ * (2 * P * s) := by gcongr
      _ = 2 * (μ * P) * s := by ring
      _ ≤ 2 * 1 * s := by gcongr
      _ = 2 * s := by ring
  have e : x - w = (x - (μ * q + (1 - μ) * w)) + μ * (q - w) := by ring
  rw [e]
  calc |(x - (μ * q + (1 - μ) * w)) + μ * (q - w)|
      ≤ |x - (μ * q + (1 - μ) * w)| + |μ * (q - w)| := abs_add_le _ _
    _ ≤ s / 32 + μ * (N / 4) := by
        rw [abs_mul, abs_of_nonneg hμ0]
        gcongr
    _ ≤ s / 32 + s / 2 := by nlinarith

theorem sub_first (u w v : ℤ) (ℓ S : ℕ) (Nh : ℝ) (h : (w : ℝ) = u + Nh - 1) (hS : (S : ℝ) = Nh)
    (hℓ : (ℓ : ℝ) ≤ Nh) (h1 : (w : ℝ) - ℓ + 1 ≤ v) (h2 : (v : ℝ) ≤ w) :
    v ∈ Icc u (u + S - 1) := by
  rw [mem_Icc]
  constructor
  · have : (u : ℝ) ≤ v := by linarith
    exact_mod_cast this
  · have : (v : ℝ) ≤ u + S - 1 := by linarith
    exact_mod_cast this

theorem sub_other (u w v : ℤ) (ℓ S : ℕ) (N : ℝ) (hS : (S : ℝ) = N) (hw1 : (u : ℝ) + N / 4 ≤ w)
    (hw2 : (w : ℝ) ≤ u + 3 * N / 4) (hℓ : (ℓ : ℝ) + 1 ≤ N / 4) (h1 : (w : ℝ) - ℓ ≤ v)
    (h2 : (v : ℝ) ≤ w + ℓ) : v ∈ Icc u (u + S - 1) := by
  rw [mem_Icc]
  constructor
  · have : (u : ℝ) ≤ v := by linarith
    exact_mod_cast this
  · have : (v : ℝ) ≤ u + S - 1 := by linarith
    exact_mod_cast this

/-- ES22 Claim 5.6. -/
theorem claim56_B2m1 {j m : ℕ} {t : ℝ} (G : Claim56Geom d j t m) (u : Fin d → ℤ)
    (w : Fin d → ℤ)
    (hw0 : ∀ i : Fin d, i.val = 0 → (w i : ℝ) = u i + 2 ^ j / 2 - 1)
    (hw : ∀ i : Fin d, i.val ≠ 0 → (u i : ℝ) + 2 ^ j / 4 ≤ w i ∧
      (w i : ℝ) ≤ u i + 3 * 2 ^ j / 4)
    {T' : ℝ≥0} (hT1 : 0.3 * claimTau m t ≤ T') (hT2 : (T' : ℝ) ≤ 0.5 * claimTau m t)
    {x : Fin d → ℤ}
    (hx : ‖(fun i => (x i : ℝ)) - claimFw j u t w (t - T')‖ ≤ claimR0 m t) :
    cBox ^ d / (3 * √(claimTau m t)) ^ (d * CBox) ≤ kernel (claimBox u j) T' x w := by
  obtain ⟨s, P, N, hs, hP, hN, hs288, hP8, hts, hNlo, hNhi, hτ⟩ := G.facts
  have hj := G.j_pos
  have hr0 : claimR0 m t = s / 32 := by unfold claimR0; rw [← hs]
  rw [hr0] at hx
  have hs0 : 0 < s := by linarith
  have hP0 : 0 < P := by linarith
  have hN0 : 0 < N := by nlinarith
  have hNbig : 2304 ≤ N := by nlinarith
  have hT1' : 0.3 * s ^ 2 ≤ (T' : ℝ) := by rw [← hτ]; exact hT1
  have hT2' : (T' : ℝ) ≤ 0.5 * s ^ 2 := by rw [← hτ]; exact hT2
  have hts0 : 0 < t := by rw [hts]; positivity
  set μ : ℝ := √(2 * T' / t) with hμ
  have hq1 : 2 * (T' : ℝ) / t ≤ (1 / P) ^ 2 := by
    rw [div_le_iff₀ hts0, hts]; field_simp; nlinarith
  have hq2 : (0.77 / P) ^ 2 ≤ 2 * (T' : ℝ) / t := by
    rw [le_div_iff₀ hts0, hts]; field_simp; nlinarith
  have hμ1 : μ ≤ 1 / P := by
    rw [hμ, Real.sqrt_le_iff]; exact ⟨by positivity, hq1⟩
  have hμ2 : 0.77 / P ≤ μ := Real.le_sqrt_of_sq_le hq2
  have hμ0 : 0 ≤ μ := Real.sqrt_nonneg _
  have hμP : μ * P ≤ 1 := by
    calc μ * P ≤ 1 / P * P := by gcongr
      _ = 1 := by field_simp
  have hμP' : 0.77 ≤ μ * P := by
    calc 0.77 = 0.77 / P * P := by field_simp
      _ ≤ μ * P := by gcongr
  have hxi : ∀ i, |(x i : ℝ) - (μ * claimQ j u i + (1 - μ) * (w i : ℝ))| ≤ s / 32 := by
    intro i
    have := (pi_norm_le_iff_of_nonneg (by positivity)).1 hx i
    have e : claimFw j u t w (t - T') i = μ * claimQ j u i + (1 - μ) * (w i : ℝ) := by
      unfold claimFw; rw [sub_sub_cancel]
    simpa [Real.norm_eq_abs, e] using this
  set ℓ : ℕ := ⌈s⌉₊ with hℓ
  have hℓ1 : s ≤ ℓ := Nat.le_ceil s
  have hℓ2 : (ℓ : ℝ) < s + 1 := Nat.ceil_lt_add_one hs0.le
  have hℓpos : 1 ≤ ℓ := by
    have : (1 : ℝ) ≤ ℓ := by linarith
    exact_mod_cast this
  have hNs : 8 * s ≤ N := by nlinarith
  set m' : Fin d → ℤ := fun i => if i.val = 0 then w i - ℓ + 1 else w i - ℓ with hm'
  set L' : Fin d → ℕ := fun i => if i.val = 0 then ℓ else 2 * ℓ + 1 with hL'
  have hL1 : ∀ i, 1 ≤ L' i := by
    intro i; simp only [hL']; split_ifs <;> omega
  have hLc : ∀ i, ((L' i : ℕ) : ℝ) = if i.val = 0 then (ℓ : ℝ) else 2 * ℓ + 1 := by
    intro i; simp only [hL']; split_ifs <;> push_cast <;> ring
  have hLle : ∀ i, ((L' i : ℕ) : ℝ) ≤ 2 * s + 3 := by
    intro i; rw [hLc]; split_ifs <;> linarith
  have hLge : ∀ i, s ≤ ((L' i : ℕ) : ℝ) := by
    intro i; rw [hLc]; split_ifs <;> linarith
  have hmemI : ∀ (z : Fin d → ℤ) (i : Fin d), z i ∈ Icc (m' i) (m' i + L' i - 1) ↔
      (if i.val = 0 then (w i : ℝ) - ℓ + 1 ≤ z i ∧ (z i : ℝ) ≤ w i
        else (w i : ℝ) - ℓ ≤ z i ∧ (z i : ℝ) ≤ w i + ℓ) := by
    intro z i
    by_cases hi : i.val = 0
    · simp only [hi, ite_true, hm', hL']
      exact mem_first_iff (w i) (z i) ℓ
    · simp only [hi, ite_false, hm', hL']
      exact mem_other_iff (w i) (z i) ℓ
  have hwQ : w ∈ boxSet m' L' := by
    intro i
    rw [hmemI]
    split_ifs
    · constructor <;> linarith
    · constructor <;> linarith
  have hxQ : x ∈ boxSet m' L' := by
    intro i
    rw [hmemI]
    have h1 := hxi i
    unfold claimQ at h1
    by_cases hi : i.val = 0
    · have hw0' := hw0 i hi
      simp only [hi, ite_true] at h1 ⊢
      have hq0 : (u i : ℝ) + 2 ^ j / 4 * 1 = (w i : ℝ) - (N / 4 - 1) := by
        rw [hw0', hN]; ring
      rw [hq0] at h1
      have := coord_first hs288 hP8 hNlo hNhi hμP' hμP hμ0 rfl h1
      constructor <;> linarith [this.1, this.2]
    · have hwi := hw i hi
      simp only [hi, ite_false] at h1 ⊢
      rw [← hN] at hwi
      have hqw : |((u i : ℝ) + 2 ^ j / 4 * 2) - (w i : ℝ)| ≤ N / 4 := by
        rw [abs_le, hN.symm]
        constructor <;> linarith [hwi.1, hwi.2]
      have := coord_other hs288 hP8 hNhi hμP hμ0 hN0 hqw h1
      rw [abs_le] at this
      constructor <;> linarith [this.1, this.2]
  have hsub : boxSet m' L' ⊆ claimBox u j := by
    intro v hv i
    have hv' := (hmemI v i).1 (hv i)
    have hsl := sideLen_cast (d := d) j hj i
    rw [← hN] at hsl
    show v i ∈ Icc (u i) (u i + (sideLen d j i : ℕ) - 1)
    by_cases hi : i.val = 0
    · simp only [hi, ite_true] at hv' hsl
      have h0 := hw0 i hi
      rw [← hN] at h0
      exact sub_first (u i) (w i) (v i) ℓ (sideLen d j i) (N / 2) h0 hsl (by linarith) hv'.1 hv'.2
    · simp only [hi, ite_false] at hv' hsl
      obtain ⟨a, b⟩ := hw i hi
      rw [← hN] at a b
      exact sub_other (u i) (w i) (v i) ℓ (sideLen d j i) N hsl a b (by linarith) hv'.1 hv'.2
  have hLsq1 : ∀ i, ((L' i : ℕ) : ℝ) ^ 2 / 16 ≤ (T' : ℝ) := by
    intro i
    have := hLle i
    have := hLge i
    nlinarith
  have hLsq2 : ∀ i, (T' : ℝ) ≤ 16 * ((L' i : ℕ) : ℝ) ^ 2 := by
    intro i
    have := hLge i
    nlinarith
  have hbox := box_d m' L' hL1 hxQ hwQ (r := T') hLsq1 hLsq2
  refine le_trans ?_ ((hbox).trans (kernel_mono hsub T' x w))
  rw [← hs]
  calc cBox ^ d / (3 * s) ^ (d * CBox) = ∏ _i : Fin d, cBox / (3 * s) ^ CBox := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow, ← pow_mul]
        congr 2; rw [mul_comm]
    _ ≤ _ := by
        refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
        · exact div_nonneg cBox_pos.le (by positivity)
        · have h1 := hLge i
          have h2 := hLle i
          exact div_le_div_of_nonneg_left cBox_pos.le (pow_pos (by linarith) _)
            (pow_le_pow_left₀ (by linarith) (by linarith) _)

end SRW
end ElboimSly
