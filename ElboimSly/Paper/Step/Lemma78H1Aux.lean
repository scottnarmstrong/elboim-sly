/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.TauHat
public import ElboimSly.Paper.Heavy.Twelve
public import Mathlib

/-!
# Auxiliary facts for the event cH_1

* `exists_h1_cutoff`: a cutoff `c ∈ (T, T']` below the first multiple of `β` above `T`;
* `ofReal_lt_cycClosingTime`: no closing by `c` gives `T(w) > c`;
* `step78_tauHat_of_gamma`: `W ∈ Γ_n`, `T(W) > T` and `T < t_n` give `τ̂(W) > T`;
* `step78_sigma_bounds`: `0 < σ ≤ 2` from `|σ - √2| ≤ 3β^{-1/16}` and `β ≥ 6^16`.
-/

@[expose] public section

open Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Heavy

theorem exists_h1_cutoff {β : ℝ} (hβ : 0 < β) {T T' : ℝ≥0} (hT : T < T') :
    ∃ c : ℝ≥0, T < c ∧ c ≤ T' ∧ ∀ k : ℕ, 1 ≤ k → (k : ℝ) * β ≤ c → (k : ℝ) * β ≤ T := by
  set k0 : ℕ := ⌊(T : ℝ) / β⌋₊ + 1 with hk0
  have hk0T : (T : ℝ) < k0 * β := by
    have := Nat.lt_floor_add_one ((T : ℝ) / β)
    rw [div_lt_iff₀ hβ] at this
    exact_mod_cast this
  set m : ℝ := min (k0 * β) T' with hm
  have hTm : (T : ℝ) < m := lt_min hk0T (by exact_mod_cast hT)
  have hmT' : m ≤ T' := min_le_right _ _
  have hmk : m ≤ k0 * β := min_le_left _ _
  have hc0 : (0 : ℝ) ≤ ((T : ℝ) + m) / 2 := by
    have := T.2; linarith
  refine ⟨(((T : ℝ) + m) / 2).toNNReal, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hc0]; linarith
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hc0]; linarith
  · intro k _ hk
    rw [Real.coe_toNNReal _ hc0] at hk
    have h1 : (k : ℝ) * β < k0 * β := by linarith
    have h2 : (k : ℝ) < k0 := lt_of_mul_lt_mul_right h1 hβ.le
    have h3 : k < ⌊(T : ℝ) / β⌋₊ + 1 := by exact_mod_cast h2
    have h4 : k ≤ ⌊(T : ℝ) / β⌋₊ := by omega
    have h5 : (k : ℝ) ≤ (T : ℝ) / β := (Nat.le_floor_iff (div_nonneg T.2 hβ.le)).1 h4
    rw [le_div_iff₀ hβ] at h5
    exact h5

variable {d : ℕ}

theorem ofReal_lt_cycClosingTime {β c : ℝ} (hβ : 0 < β) (hc : 0 ≤ c) {w : ℝ → Fin d → ℤ}
    (hcl : ¬ ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) * β ≤ c ∧ w ((k : ℝ) * β) = 0) :
    ENNReal.ofReal c < cycClosingTime β w := by
  set k1 : ℕ := ⌊c / β⌋₊ + 1 with hk1
  have hk1c : c < k1 * β := by
    have := Nat.lt_floor_add_one (c / β)
    rw [div_lt_iff₀ hβ] at this
    exact_mod_cast this
  have hk10 : (0 : ℝ) ≤ k1 * β := by positivity
  calc ENNReal.ofReal c < ENNReal.ofReal (k1 * β) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hk1c
    _ ≤ cycClosingTime β w := by
        unfold cycClosingTime
        refine le_iInf₂ fun k hk => ENNReal.ofReal_le_ofReal ?_
        obtain ⟨hk1', hk0⟩ := hk
        have hkc : c < k * β := by
          by_contra hle
          exact hcl ⟨k, hk1', not_lt.1 hle, hk0⟩
        have : (k1 : ℝ) ≤ k := by
          by_contra hlt
          push Not at hlt
          have hk' : k < ⌊c / β⌋₊ + 1 := by exact_mod_cast hlt
          have : k ≤ ⌊c / β⌋₊ := by omega
          have h3 : (k : ℝ) ≤ c / β := (Nat.le_floor_iff (div_nonneg hc hβ.le)).1 this
          rw [le_div_iff₀ hβ] at h3
          linarith
        nlinarith

theorem step78_tauHat_of_gamma {β t₀ T : ℝ} {n : ℕ} {w : ℝ → Fin d → ℤ} (hT0 : 0 ≤ T)
    (hΓ : heavyGamma d β t₀ n w) (hcl : ENNReal.ofReal T < cycClosingTime β w)
    (hTn : T < indScale t₀ n) : ENNReal.ofReal T < heavyTauHat d β t₀ n w := by
  obtain ⟨-, hlt⟩ := hΓ
  have hm : ENNReal.ofReal T <
      min (cycClosingTime β w) (ENNReal.ofReal (indScale t₀ n)) :=
    lt_min hcl ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hTn)
  have h2 := hm.trans hlt
  unfold heavyTauHat heavyTauCheck
  simp only [lt_min_iff] at hm h2 ⊢
  exact ⟨hm.2, hm.1, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩

theorem step78_sigma_bounds {σ β τ : ℝ} (hβ : (6 : ℝ) ^ 16 ≤ β) (hτ : 0 < τ)
    (h : |σ - Real.sqrt 2| ≤ max (3 * β ^ (-(1 : ℝ) / 16) - τ ^ (-(1 : ℝ) / 16)) 0) :
    0 < σ ∧ σ ≤ 2 := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have h6 : (6 : ℝ) ≤ β ^ ((1 : ℝ) / 16) := by
    have : ((6 : ℝ) ^ 16) ^ ((1 : ℝ) / 16) = 6 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← this]
    exact Real.rpow_le_rpow (by positivity) hβ (by norm_num)
  have e : β ^ (-(1 : ℝ) / 16) = (β ^ ((1 : ℝ) / 16))⁻¹ := by
    rw [← Real.rpow_neg hβ0.le]; ring_nf
  have h1 : β ^ (-(1 : ℝ) / 16) ≤ 1 / 6 := by
    rw [e]
    exact (inv_anti₀ (by norm_num) h6).trans_eq (by norm_num)
  have h2 : 0 < τ ^ (-(1 : ℝ) / 16) := Real.rpow_pos_of_pos hτ _
  have h3 : max (3 * β ^ (-(1 : ℝ) / 16) - τ ^ (-(1 : ℝ) / 16)) 0 ≤ 1 / 2 :=
    max_le (by linarith) (by norm_num)
  have h4 := (abs_le.1 (h.trans h3))
  have s1 : (7 / 5 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> linarith [h4.1, h4.2]

end ElboimSly.Paper.Step

end
