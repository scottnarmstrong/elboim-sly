/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Asymp2
public import ElboimSly.Paper.Escape.C56Small
public import Mathlib

/-!
# Claim 5.6: a controlled path inside `B^-`

ES22 Claim 5.6 (ES22 Claim 5.6, with the deviations F63, F66, F31, F32, D11, F03).

`es5_6`: there is `β_{56} = β_{56}(d, n₀)` such that under `Es4Setting` with `β ≥ β_{56}` and
`γ ≥ max (γ₁, γ₅₆)`, for every `u`, `v ∈ ∂B ∩ B^-`, `w ∈ F_B` and real `t ∈ [4^{j-1}, 4^j]`
(`j = escJ n`), the walk `W_v = v + W` satisfies `P(E_{56}) ≥ n^{-γ+1}`.  Here `E_{56}` is
`Esc56Event`: `W_v(t) = w`, `W_v(s) ∈ B^-` for `s ≤ t`, `W_v(s) ≠ v` on `[β, t]`,
`W_v(s) ≠ w` on `[0, t - β]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.SRW ElboimSly.Brownian

variable {k : ℕ}

theorem ev_pow_le_four_pow : ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → 4 * (n : ℝ) ^ 40 ≤ 4 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 40 (by norm_num : (1 : ℝ) < 4)
  obtain ⟨N0, hN0⟩ :=
    eventually_atTop.1 (h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  refine ⟨N0, fun n hn => ?_⟩
  have := hN0 n hn
  have hp : (0 : ℝ) < 4 ^ n := by positivity
  rw [div_lt_iff₀ hp] at this
  linarith

/-- **Claim 5.6** (ES22 Claim 5.6). -/
theorem es5_6 (hd : 5 ≤ k + 2) (n₀ : ℕ) :
    ∃ β56 : ℝ, ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), β56 ≤ β →
      ∀ {Ω : Type} (𝒢₀ : MeasurableSpace Ω) [_mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
        {N N' : Ω → Measure (CycS ℕ (k + 2) β)} (_S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N')
        {γ : ℝ}, max (gamma1 (k + 2)) (escGamma56 (k + 2)) ≤ γ →
        ∀ (u v z : Fin (k + 2) → ℤ) (t : ℝ), v ∈ escBoundary (escJ n) u →
          v ∈ escBlockMinus (escJ n) u → z ∈ escFace (escJ n) u →
          (4 : ℝ) ^ (escJ n - 1) ≤ t → t ≤ 4 ^ escJ n →
          ENNReal.ofReal ((n : ℝ) ^ (-γ + 1)) ≤
            Pr {ω | Esc56Event β (escJ n) u v z t (escYv N v ω)} := by
  obtain ⟨C, hC, H⟩ := es5_6_core hd
  obtain ⟨β41, Hc⟩ := H n₀
  obtain ⟨B, hB⟩ := asymp_conditions (d := k + 2) (by omega) n₀ C
  obtain ⟨N0, hN0⟩ := ev_pow_le_four_pow
  refine ⟨max (max β41 B) (4 ^ (N0 + 1)), fun β _ n t₀ hβ56 Ω 𝒢₀ mΩ Pr N N' S γ hγ u v z t hv hvm
    hz ht1 ht2 => ?_⟩
  have hβ41 : β41 ≤ β := (le_max_left _ _).trans ((le_max_left _ _).trans hβ56)
  have hβB : B ≤ β := (le_max_right _ _).trans ((le_max_left _ _).trans hβ56)
  have hβN : (4 : ℝ) ^ (N0 + 1) ≤ β := (le_max_right _ _).trans hβ56
  obtain ⟨hβ1, hβ40, hn0, hθ', hL0, hconst, hP0, hP1⟩ := hB β hβB
  have hp := S.params
  have hn2 : 2 ≤ n := by have := hp.eight_le; have := hp.lt; omega
  have hnN : N0 ≤ n := by
    by_contra hlt
    push Not at hlt
    have h1 : β < indScale t₀ n := hp.beta_lt
    have h2 : indScale t₀ n ≤ 4 ^ (n + 1) := by
      unfold indScale; rw [pow_succ]
      nlinarith [hp.le_four, pow_pos (by norm_num : (0 : ℝ) < 4) n]
    have h3 : (4 : ℝ) ^ (n + 1) ≤ 4 ^ (N0 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have h4n := hN0 n hnN
  have hj1 : n ^ 20 ≤ 2 ^ escJ n := le_two_pow_escJ n
  have hj2 : 2 ^ escJ n < 2 * n ^ 20 := two_pow_escJ_lt hn2
  have hj6 : 6 ≤ escJ n := by
    by_contra hlt
    push Not at hlt
    have h1 : 2 ^ escJ n ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 40 ≤ n := by have := hp.eight_le; have := hp.lt; omega
    have h3 : 40 ^ 20 ≤ n ^ 20 := Nat.pow_le_pow_left h2 20
    have : 2 ^ 5 < 40 ^ 20 := by norm_num
    omega
  have hgeom : EscGeom (escJ n) u v z := ⟨hj6, hv, hvm, hz⟩
  have hjn : (4 : ℝ) ^ escJ n ≤ 4 ^ n := by
    have h2 : (2 : ℝ) ^ escJ n < 2 * (n : ℝ) ^ 20 := by exact_mod_cast hj2
    have h1 : (4 : ℝ) ^ escJ n = (2 ^ escJ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h3 : (0 : ℝ) < 2 ^ escJ n := by positivity
    calc (4 : ℝ) ^ escJ n = (2 ^ escJ n) ^ 2 := h1
      _ ≤ (2 * (n : ℝ) ^ 20) ^ 2 := by gcongr
      _ = 4 * (n : ℝ) ^ 40 := by ring
      _ ≤ 4 ^ n := h4n
  by_cases hbig : β < 4 ^ escJ n
  · exact Hc β n t₀ hβ41 𝒢₀ S hgeom hβ40 ht1 ht2 hjn hn0 hθ' _
      (fun T hT hT' => eta_bound hL0 hT) hconst hP0 hP1 hbig (max_le_iff.1 hγ).2 hn2 hj1 hj2
  · push Not at hbig
    have hsmall := small_case (N := N) S.space.ppp hgeom hbig ht1 ht2
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hsmall
    exact claim56_small_gamma (d := k + 2) hn2 hj1 hj2 (max_le_iff.1 hγ).1

end ElboimSly.Paper.Escape

end
