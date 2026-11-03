/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Cor610Aux
public import ElboimSly.Paper.Heavy.WindowAvg
public import ElboimSly.Paper.Heavy.TauHat

/-!
# Corollary 6.10

ES22 Corollary 6.10 (§6; deviations F12, F59).

Let `h = t_n^{ε/2} ≤ t < τ̌(w)`.  Then `|𝒯(w) ∩ [t - h, t]| ≥ (0.9 + 3/n) h`.

* `heavyH_ge`, `tkPrime_le_rpow`, `tn_pow_le`: the numerical comparisons feeding (T10).
* `volume_badUnion_le_rpow`: the occupation bound for `Λ_t`.
* `es6_ten`: the corollary.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {β t₀ : ℝ} {w : ℝ → Fin d → ℤ}

theorem indDelta_mul_d (hd : 1 ≤ d) : indDelta d * d = heavyEps d / 10 := by
  have : (d : ℝ) ≠ 0 := by positivity
  unfold indDelta heavyEps
  field_simp
  ring

theorem heavyEps_pos (hd : 1 ≤ d) : 0 < heavyEps d := by
  unfold heavyEps
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

/-- `h = t_n^{ε/2} ≥ 4^{εn/2}`. -/
theorem heavyH_ge (hd : 1 ≤ d) (ht1 : 1 < t₀) :
    (4 : ℝ) ^ (heavyEps d * n / 2) ≤ heavyH d t₀ n := by
  have hε := heavyEps_pos hd
  unfold heavyH
  have h1 := indScale_gt_four_pow ht1 n
  calc (4 : ℝ) ^ (heavyEps d * n / 2) = ((4 : ℝ) ^ (n : ℝ)) ^ (heavyEps d / 2) := by
        rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
    _ = ((4 : ℝ) ^ n) ^ (heavyEps d / 2) := by rw [Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) h1.le (by positivity)

/-- `t_n^{3ε/10} ≤ 4^{3ε(n+1)/10}`. -/
theorem tn_pow_le (hd : 1 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) :
    indScale t₀ n ^ (3 * heavyEps d / 10) ≤ (4 : ℝ) ^ (3 * heavyEps d * (n + 1) / 10) := by
  have hε := heavyEps_pos hd
  have h1 := indScale_le_four_pow ht4 n
  have h0 : 0 ≤ indScale t₀ n := ((by positivity : (0:ℝ) ≤ 4 ^ n).trans (indScale_gt_four_pow ht1 n).le)
  calc indScale t₀ n ^ (3 * heavyEps d / 10) ≤ ((4 : ℝ) ^ (n + 1)) ^ (3 * heavyEps d / 10) :=
        Real.rpow_le_rpow h0 h1 (by positivity)
    _ = (4 : ℝ) ^ (3 * heavyEps d * (n + 1) / 10) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1; push_cast; ring

/-- `t'_k ≤ 4^{4δn+1}`. -/
theorem tkPrime_le_rpow (hd : 1 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hk : 16 ≤ heavyLevel d n) :
    heavyTkPrime d t₀ n ≤ (4 : ℝ) ^ (4 * indDelta d * n + 1) := by
  obtain ⟨_, _, h3, _⟩ := scales_facts_c (d := d) (n := n) ht1 ht4 hk
  have hk4 : (1 : ℝ) ≤ (heavyLevel d n : ℝ) ^ 4 :=
    one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ heavyLevel d n))
  have h4 : (4 : ℝ) ^ (heavyLevel d n + 1) / (heavyLevel d n : ℝ) ^ 4 ≤ (4 : ℝ) ^ (heavyLevel d n + 1) :=
    div_le_self (by positivity) hk4
  have hle := heavyLevel_le (d := d) hd n
  calc heavyTkPrime d t₀ n ≤ _ := h3.trans h4
    _ = (4 : ℝ) ^ ((heavyLevel d n : ℝ) + 1) := by
        rw [← Real.rpow_natCast]; push_cast; rfl
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end ElboimSly.Paper.Heavy
