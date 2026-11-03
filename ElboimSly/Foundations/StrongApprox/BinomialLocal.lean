/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.Binomial
public import ElboimSly.Foundations.StrongApprox.Stirling

/-!
# Local expansion of $\mathrm{Bin}(m, \tfrac12)$

Local expansion of Bin(m,frac12) (Part I).
-/

@[expose] public section

open Filter Topology Finset
open scoped Real Nat

namespace ElboimSly
namespace StrongApprox

/-- The scale `s = √(m+1)/2` of local expansion of Bin(m,frac12). -/
noncomputable def sbS (m : ℕ) : ℝ := √((m : ℝ) + 1) / 2

theorem sbS_sq (m : ℕ) : sbS m ^ 2 = ((m : ℝ) + 1) / 4 := by
  unfold sbS; rw [div_pow, Real.sq_sqrt (by positivity)]; norm_num

theorem sbS_pos (m : ℕ) : 0 < sbS m := by unfold sbS; positivity

/-- `D(j) = log sab m j + (j-μ)²/(2s²)`. -/
noncomputable def sbD (m j : ℕ) : ℝ :=
  Real.log (sab m j) + ((j : ℝ) - m / 2) ^ 2 / (2 * sbS m ^ 2)

/-- The increment ratio `a_j = (2j - m + 1)/(m+1)`. -/
noncomputable def sbA (m j : ℕ) : ℝ := (2 * (j : ℝ) - m + 1) / (m + 1)

theorem sab_succ_ratio {m j : ℕ} (hj : j < m) :
    sab m (j + 1 : ℕ) = sab m j * (((m : ℝ) - j) / (j + 1)) := by
  rw [sab_natCast, sab_natCast]
  have h := Nat.choose_succ_right_eq m j
  have h2 : ((m.choose (j + 1) : ℕ) : ℝ) * ((j : ℝ) + 1) = (m.choose j : ℝ) * ((m : ℝ) - j) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this
    rw [Nat.cast_sub hj.le] at this
    exact this
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  field_simp
  linarith

theorem sbD_succ_sub {m j : ℕ} (hj : j < m) :
    sbD m (j + 1) - sbD m j = Real.log ((1 - sbA m j) / (1 + sbA m j)) + 2 * sbA m j := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
  have hsj : 0 < sab m j := sab_pos (by omega) (by omega)
  have hsj1 : 0 < sab m (j + 1 : ℕ) := sab_pos (by omega) (by omega)
  have hr : (m : ℝ) - j > 0 := by linarith
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hratio : (1 - sbA m j) / (1 + sbA m j) = ((m : ℝ) - j) / (j + 1) := by
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have h1 : 1 - sbA m j = 2 * ((m : ℝ) - j) / (m + 1) := by unfold sbA; field_simp; ring
    have h2 : 1 + sbA m j = 2 * ((j : ℝ) + 1) / (m + 1) := by unfold sbA; field_simp; ring
    rw [h1, h2]; field_simp
  have hlog : Real.log (sab m (j + 1 : ℕ)) - Real.log (sab m j) = Real.log (((m : ℝ) - j) / (j + 1)) := by
    rw [sab_succ_ratio hj, Real.log_mul hsj.ne' (by positivity), add_sub_cancel_left]
  unfold sbD
  rw [hratio, ← hlog, sbS_sq]
  unfold sbA
  have : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  push_cast
  field_simp
  ring

theorem sbD_step_bound {m j : ℕ} (hm : 32 ≤ m) (hj : j < m) {K : ℝ} (hKm : K ≤ m / 16 + 2)
    (hjK : |2 * (j : ℝ) - m + 1| ≤ 2 * K) :
    |sbD m (j + 1) - sbD m j| ≤ 32 * K ^ 3 / ((m : ℝ) + 1) ^ 3 := by
  have hm' : (32 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hK0 : 0 ≤ K := by linarith [abs_nonneg (2 * (j : ℝ) - m + 1)]
  have ha : |sbA m j| ≤ 2 * K / ((m : ℝ) + 1) := by
    unfold sbA
    rw [abs_div, abs_of_pos hm1]
    exact div_le_div_of_nonneg_right hjK hm1.le
  have ha2 : |sbA m j| ≤ 1 / 2 := by
    refine ha.trans ?_
    rw [div_le_iff₀ hm1]; linarith only [hKm, hm']
  rw [sbD_succ_sub hj]
  refine (abs_log_sub_add_le ha2).trans ?_
  calc 4 * |sbA m j| ^ 3 ≤ 4 * (2 * K / ((m : ℝ) + 1)) ^ 3 := by gcongr
    _ = _ := by rw [div_pow, mul_pow]; ring

theorem sbD_chain {m : ℕ} (hm : 32 ≤ m) {K : ℝ} (hKm : K ≤ m / 16 + 2) {lo : ℕ} :
    ∀ n : ℕ, (∀ i : ℕ, lo ≤ i → i < lo + n → |2 * (i : ℝ) - m + 1| ≤ 2 * K) → lo + n ≤ m →
      |sbD m (lo + n) - sbD m lo| ≤ n * (32 * K ^ 3 / ((m : ℝ) + 1) ^ 3) := by
  intro n
  induction n with
  | zero => intro _ _; simp
  | succ n ih =>
    intro h hle
    have h1 := ih (fun i hi1 hi2 => h i hi1 (by omega)) (by omega)
    have h2 := sbD_step_bound (m := m) (j := lo + n) hm (by omega) hKm (h (lo + n) (by omega) (by omega))
    have e : lo + (n + 1) = lo + n + 1 := by ring
    rw [e]
    push_cast
    calc |sbD m (lo + n + 1) - sbD m lo|
        = |(sbD m (lo + n + 1) - sbD m (lo + n)) + (sbD m (lo + n) - sbD m lo)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by linarith)

theorem log_sqrt2pi_sbS (m : ℕ) :
    Real.log (√(2 * π) * sbS m) = Real.log (π * ((m : ℝ) + 1) / 2) / 2 := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h : √(2 * π) * sbS m = √(π * ((m : ℝ) + 1) / 2) := by
    have h0 : 0 ≤ √(2 * π) * sbS m := (mul_pos (Real.sqrt_pos.2 (by positivity)) (sbS_pos m)).le
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) h0]
    have h1 : √(2 * π) * √(2 * π) = 2 * π := Real.mul_self_sqrt (by positivity)
    have h2 : sbS m * sbS m = ((m : ℝ) + 1) / 4 := by rw [← sq]; exact sbS_sq m
    have h3 : √(2 * π) * sbS m * (√(2 * π) * sbS m) =
        (√(2 * π) * √(2 * π)) * (sbS m * sbS m) := by ring
    rw [h3, h1, h2]; ring
  rw [h, Real.log_sqrt (by positivity)]

theorem log_one_add_le {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.log (1 + x) ∧ Real.log (1 + x) ≤ x := by
  refine ⟨Real.log_nonneg (by linarith), ?_⟩
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith)
  linarith

theorem central_even {k : ℕ} (hk : 1 ≤ k) :
    |sbD (2 * k) k + Real.log (√(2 * π) * sbS (2 * k))| ≤ 1 / (3 * k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set c : ℝ := ((2 * k).choose k : ℝ) / 4 ^ k with hc
  have hcpos : 0 < c := by
    have : 0 < (2 * k).choose k := Nat.choose_pos (by omega)
    rw [hc]; positivity
  have hsab : sab (2 * k) k = c := by
    rw [sab_natCast, hc]
    congr 1
    rw [pow_mul]; norm_num
  have hlo := exp_neg_le_central_binom hk
  have hhi := central_binom_le_exp hk
  have hLeq : √(π * k) * c = √(π * k) * ((2 * k).choose k : ℝ) / 4 ^ k := by rw [hc]; ring
  rw [← hLeq] at hlo hhi
  have hq : 0 < √(π * k) * c := by positivity
  have hL1 : -(1 / (6 * (k : ℝ))) ≤ Real.log (√(π * k) * c) := by
    rw [Real.le_log_iff_exp_le hq]; exact hlo
  have hL2 : Real.log (√(π * k) * c) ≤ 1 / (24 * (k : ℝ)) := by
    rw [Real.log_le_iff_le_exp hq]; exact hhi
  have hLsplit : Real.log (√(π * k) * c) = Real.log (π * k) / 2 + Real.log c := by
    rw [Real.log_mul (Real.sqrt_pos.2 (by positivity)).ne' hcpos.ne',
      Real.log_sqrt (by positivity)]
  have hA := log_sqrt2pi_sbS (2 * k)
  have hArg : π * (((2 * k : ℕ) : ℝ) + 1) / 2 = (π * k) * (1 + 1 / (2 * k)) := by
    push_cast; field_simp
  have hlog1 := log_one_add_le (x := 1 / (2 * (k : ℝ))) (by positivity)
  have hAeq : Real.log (π * (((2 * k : ℕ) : ℝ) + 1) / 2) = Real.log (π * k) + Real.log (1 + 1 / (2 * (k : ℝ))) := by
    rw [hArg, Real.log_mul (by positivity) (by positivity)]
  have hD : sbD (2 * k) k = Real.log c := by
    unfold sbD
    rw [hsab]; push_cast; ring_nf
  rw [hD, hA, hAeq]
  have hkk : 1 / (24 * (k : ℝ)) + 1 / (2 * (2 * k)) ≤ 1 / (3 * k) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    linarith only [sq_nonneg (k : ℝ)]
  have hkk2 : 1 / (6 * (k : ℝ)) ≤ 1 / (3 * k) := by gcongr; norm_num
  have h2 : 1 / (2 * (k : ℝ)) / 2 = 1 / (2 * (2 * k)) := by field_simp
  rw [abs_le]
  constructor
  · linarith only [hL1, hLsplit, hlog1.1, hkk2]
  · linarith only [hL2, hLsplit, hlog1.2, h2, hkk]

theorem central_odd {k : ℕ} (hk : 1 ≤ k) :
    |sbD (2 * k + 1) k + Real.log (√(2 * π) * sbS (2 * k + 1))| ≤ 1 / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set c : ℝ := ((2 * k).choose k : ℝ) / 4 ^ k with hc
  have hcpos : 0 < c := by
    have : 0 < (2 * k).choose k := Nat.choose_pos (by omega)
    rw [hc]; positivity
  have hsab : sab (2 * k + 1) k = c * ((2 * (k : ℝ) + 1) / (2 * k + 2)) := by
    rw [sab_natCast, hc]
    have h1 := Nat.add_one_mul_choose_eq (2 * k) k
    rw [Nat.choose_symm_half] at h1
    have h2 : ((2 * k + 1 : ℕ) : ℝ) * ((2 * k).choose k : ℝ) =
        ((2 * k + 1).choose k : ℝ) * ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    rw [pow_succ, pow_mul]
    norm_num
    field_simp
    linarith only [h2]
  have hlo := exp_neg_le_central_binom hk
  have hhi := central_binom_le_exp hk
  have hLeq : √(π * k) * c = √(π * k) * ((2 * k).choose k : ℝ) / 4 ^ k := by rw [hc]; ring
  rw [← hLeq] at hlo hhi
  have hq : 0 < √(π * k) * c := by positivity
  have hL1 : -(1 / (6 * (k : ℝ))) ≤ Real.log (√(π * k) * c) := by
    rw [Real.le_log_iff_exp_le hq]; exact hlo
  have hL2 : Real.log (√(π * k) * c) ≤ 1 / (24 * (k : ℝ)) := by
    rw [Real.log_le_iff_le_exp hq]; exact hhi
  have hLsplit : Real.log (√(π * k) * c) = Real.log (π * k) / 2 + Real.log c := by
    rw [Real.log_mul (Real.sqrt_pos.2 (by positivity)).ne' hcpos.ne',
      Real.log_sqrt (by positivity)]
  have hA := log_sqrt2pi_sbS (2 * k + 1)
  have hArg : π * (((2 * k + 1 : ℕ) : ℝ) + 1) / 2 = (π * k) * (1 + 1 / (k : ℝ)) := by
    push_cast; field_simp; ring
  have hlog1 := log_one_add_le (x := 1 / (k : ℝ)) (by positivity)
  have hlog2 := log_one_add_le (x := 1 / (2 * (k : ℝ) + 1)) (by positivity)
  have hAeq : Real.log (π * (((2 * k + 1 : ℕ) : ℝ) + 1) / 2) =
      Real.log (π * k) + Real.log (1 + 1 / (k : ℝ)) := by
    rw [hArg, Real.log_mul (by positivity) (by positivity)]
  have hratio : Real.log ((2 * (k : ℝ) + 1) / (2 * k + 2)) = -Real.log (1 + 1 / (2 * (k : ℝ) + 1)) := by
    rw [← Real.log_inv]; congr 1; field_simp; ring
  have hD : sbD (2 * k + 1) k = Real.log c + Real.log ((2 * (k : ℝ) + 1) / (2 * k + 2)) +
      1 / (4 * ((k : ℝ) + 1)) := by
    unfold sbD
    rw [hsab, Real.log_mul hcpos.ne' (by positivity), sbS_sq]
    push_cast
    congr 1
    field_simp
    ring
  rw [hD, hA, hAeq, hratio]
  set u : ℝ := 1 / (k : ℝ) with hu
  have hu0 : 0 < u := by positivity
  have e1 : 1 / (4 * ((k : ℝ) + 1)) ≤ 1 / 4 * u := by
    rw [hu, show (1 : ℝ) / 4 * (1 / k) = 1 / (4 * k) by field_simp]; gcongr; linarith
  have e2 : 1 / (2 * (k : ℝ) + 1) ≤ 1 / 2 * u := by
    rw [hu, show (1 : ℝ) / 2 * (1 / k) = 1 / (2 * k) by field_simp]; gcongr; linarith
  have e3 : 1 / (6 * (k : ℝ)) = 1 / 6 * u := by rw [hu]; field_simp
  have e4 : 1 / (24 * (k : ℝ)) = 1 / 24 * u := by rw [hu]; field_simp
  have e5 : 1 / (4 * ((k : ℝ) + 1)) ≥ 0 := by positivity
  rw [abs_le]
  constructor
  · linarith only [hL1, hLsplit, e3, hlog1.1, hlog2.2, e2, e5, hu0]
  · linarith only [hL2, hLsplit, e4, hlog2.1, e1, hlog1.2, hu0]

theorem sbS_le_two_mul {k : ℕ} (hk : 1 ≤ k) (m : ℕ) (hm : m ≤ 2 * k + 1) : sbS m ≤ 2 * k := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm' : (m : ℝ) ≤ 2 * k + 1 := by exact_mod_cast hm
  have h1 := sbS_sq m
  have h2 := sbS_pos m
  by_contra h
  rw [not_le] at h
  have h3 : (2 * (k : ℝ)) ^ 2 < sbS m ^ 2 := pow_lt_pow_left₀ h (by positivity) two_ne_zero
  linarith only [h3, h1, hm', hk', mul_le_mul_of_nonneg_left hk' (by linarith : (0 : ℝ) ≤ k)]

theorem central_bound {m : ℕ} (hm : 32 ≤ m) :
    |sbD m (m / 2) + Real.log (√(2 * π) * sbS m)| ≤ 2 / sbS m := by
  obtain ⟨k, hk⟩ : ∃ k, m / 2 = k := ⟨_, rfl⟩
  have hk16 : 16 ≤ k := by omega
  have hs := sbS_pos m
  rcases Nat.even_or_odd' m with ⟨q, hq | hq⟩
  · have hkq : k = q := by omega
    subst hkq
    have hmm : m = 2 * k := hq
    subst hmm
    rw [hk]
    refine (central_even (by omega)).trans ?_
    have h1 := sbS_le_two_mul (k := k) (by omega) (2 * k) (by omega)
    have hk' : (16 : ℝ) ≤ k := by exact_mod_cast hk16
    rw [div_le_div_iff₀ (by positivity) hs]
    linarith only [h1, hk']
  · have hkq : k = q := by omega
    subst hkq
    have hmm : m = 2 * k + 1 := hq
    subst hmm
    rw [hk]
    refine (central_odd (by omega)).trans ?_
    have h1 := sbS_le_two_mul (k := k) (by omega) (2 * k + 1) le_rfl
    have hk' : (16 : ℝ) ≤ k := by exact_mod_cast hk16
    rw [div_le_div_iff₀ (by positivity) hs]
    linarith only [h1]

/-- Local expansion of Bin(m,frac12), the natural-number form. -/
theorem binom_local_nat {m : ℕ} (hm : 32 ≤ m) {J : ℕ} (hJ : |(J : ℝ) - m / 2| ≤ m / 16 + 1) :
    |sbD m J + Real.log (√(2 * π) * sbS m)| ≤
      2 / sbS m + 32 * (|(J : ℝ) - m / 2| + 1) ^ 4 / ((m : ℝ) + 1) ^ 3 := by
  have hm' : (32 : ℝ) ≤ m := by exact_mod_cast hm
  set K : ℝ := |(J : ℝ) - m / 2| + 1 with hK
  have hK1 : 1 ≤ K := by have := abs_nonneg ((J : ℝ) - m / 2); linarith
  have hKm : K ≤ m / 16 + 2 := by linarith
  have hJm : J < m := by
    have := (abs_le.1 hJ).2
    have : (J : ℝ) < m := by linarith
    exact_mod_cast this
  have hc1 : 2 * ((m / 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.mul_div_le m 2
  have hc2 : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
    have : m ≤ 2 * (m / 2) + 1 := by omega
    exact_mod_cast this
  have hcen := central_bound hm
  have hB : 0 ≤ 32 * K ^ 3 / ((m : ℝ) + 1) ^ 3 := by positivity
  have habs := abs_cases ((J : ℝ) - m / 2)
  have key : |sbD m J - sbD m (m / 2)| ≤ K * (32 * K ^ 3 / ((m : ℝ) + 1) ^ 3) := by
    rcases le_or_gt (m / 2) J with hcJ | hcJ
    · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hcJ
      have hch := sbD_chain (m := m) hm hKm (lo := m / 2) n
        (fun i hi1 hi2 => by
          have hi1' : (m / 2 : ℕ) ≤ i := hi1
          have hi2' : (i : ℝ) + 1 ≤ ((m / 2 : ℕ) : ℝ) + n := by
            have : i + 1 ≤ m / 2 + n := hi2
            exact_mod_cast this
          have hi1'' : ((m / 2 : ℕ) : ℝ) ≤ i := by exact_mod_cast hi1'
          have hnJ : (J : ℝ) = ((m / 2 : ℕ) : ℝ) + n := by
            rw [hn]; push_cast; ring
          rw [abs_le]; constructor <;> rcases habs with ⟨h, h'⟩ | ⟨h, h'⟩ <;>
            linarith only [hc1, hc2, hi1'', hi2', hnJ, hK, hK1, h, h']) (by omega)
      rw [← hn] at hch
      refine hch.trans ?_
      gcongr
      have hnJ : (J : ℝ) = ((m / 2 : ℕ) : ℝ) + n := by rw [hn]; push_cast; ring
      rcases habs with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hcJ.le
      have hch := sbD_chain (m := m) hm hKm (lo := J) n
        (fun i hi1 hi2 => by
          have hi1' : (J : ℝ) ≤ i := by exact_mod_cast hi1
          have hi2' : (i : ℝ) + 1 ≤ J + n := by
            have : i + 1 ≤ J + n := hi2
            exact_mod_cast this
          have hnJ : ((m / 2 : ℕ) : ℝ) = J + n := by rw [hn]; push_cast; ring
          rw [abs_le]; constructor <;> rcases habs with ⟨h, h'⟩ | ⟨h, h'⟩ <;>
            linarith only [hc1, hc2, hi1', hi2', hnJ, hK, hK1, h, h']) (by omega)
      rw [← hn, abs_sub_comm] at hch
      refine hch.trans ?_
      gcongr
      have hnJ : ((m / 2 : ℕ) : ℝ) = J + n := by rw [hn]; push_cast; ring
      rcases habs with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  calc |sbD m J + Real.log (√(2 * π) * sbS m)|
      = |(sbD m J - sbD m (m / 2)) + (sbD m (m / 2) + Real.log (√(2 * π) * sbS m))| := by ring_nf
    _ ≤ |sbD m J - sbD m (m / 2)| + |sbD m (m / 2) + Real.log (√(2 * π) * sbS m)| := abs_add_le _ _
    _ ≤ _ := by
        have : K * (32 * K ^ 3 / ((m : ℝ) + 1) ^ 3) = 32 * K ^ 4 / ((m : ℝ) + 1) ^ 3 := by ring
        rw [this] at key
        linarith

/-- Local expansion of Bin(m,frac12). For `m ≥ 32` and every integer `j` with
`|j - m/2| ≤ m/16 + 1`,
`log sab m j = -log(√(2π) s) - (j - m/2)²/(2s²) + E₁(j)` with `s = √(m+1)/2` and
`|E₁(j)| ≤ 2/s + 32(|j - m/2| + 1)⁴/(m+1)³`. Here `E₁(j)` is the displayed difference. -/
theorem binom_local {m : ℕ} (hm : 32 ≤ m) {j : ℤ} (hj : |(j : ℝ) - m / 2| ≤ m / 16 + 1) :
    |Real.log (sab m j) -
        (-Real.log (√(2 * π) * sbS m) - ((j : ℝ) - m / 2) ^ 2 / (2 * sbS m ^ 2))| ≤
      2 / sbS m + 32 * (|(j : ℝ) - m / 2| + 1) ^ 4 / ((m : ℝ) + 1) ^ 3 := by
  have hm' : (32 : ℝ) ≤ m := by exact_mod_cast hm
  have hj0 : 0 ≤ j := by
    have := (abs_le.1 hj).1
    have : (0 : ℝ) < j := by linarith
    exact_mod_cast this.le
  obtain ⟨J, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
  have h := binom_local_nat hm (J := J) (by simpa using hj)
  have e : Real.log (sab m (J : ℤ)) - (-Real.log (√(2 * π) * sbS m) -
      (((J : ℤ) : ℝ) - m / 2) ^ 2 / (2 * sbS m ^ 2)) =
      sbD m J + Real.log (√(2 * π) * sbS m) := by
    unfold sbD; push_cast; ring
  rw [e]
  simpa using h

end StrongApprox
end ElboimSly
