/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Final
public import ElboimSly.Paper.Escape.C56Phase
public import ElboimSly.Paper.Escape.C56Incl
public import ElboimSly.Paper.Escape.C56Zero
public import ElboimSly.Paper.Escape.C56LastProb
public import Mathlib

/-!
# ES22 Claim 5.6: assembly

ES22 Claim 5.6, "Conclusion".  The probability part of the proof, under explicit numerical
hypotheses on `β` (which hold for `β ≥ β_{56}`; see `C56Asymp`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.SRW ElboimSly.Brownian

variable {k : ℕ}

theorem rho_ge_of_one_le {t : ℝ} (ht : 0 < t) {m i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ 2 * m) :
    Real.sqrt t / 2 ^ m / 16 ≤ es56Rho t m i := by
  have hs := Real.sqrt_pos.2 ht
  have e : Real.sqrt t / 2 ^ m / 16 = Real.sqrt t / 2 ^ (m + 4) := by
    rw [pow_add, div_div]; norm_num
  rw [e]
  unfold es56Rho
  split_ifs with h
  · exact div_le_div_of_nonneg_left hs.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega))
  · exact div_le_div_of_nonneg_left hs.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega))

theorem tau_bounds {β t : ℝ} (hβ0 : 0 < β) (hsb : Real.sqrt β ≤ t) :
    Real.sqrt β ≤ claimTau (escPhaseM β t) t ∧ claimTau (escPhaseM β t) t < 4 * Real.sqrt β := by
  have hpm : (0 : ℝ) < 4 ^ escPhaseM β t := by positivity
  have h1 := four_pow_m_le hβ0 hsb
  have h2 := lt_four_pow_m_succ hβ0 hsb
  rw [pow_succ] at h2
  unfold claimTau
  constructor
  · rw [le_div_iff₀ hpm]; linarith
  · rw [div_lt_iff₀ hpm]; linarith

/-- **ES22 Claim 5.6, probability part.** -/
theorem es5_6_core (hd : 5 ≤ k + 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n₀ : ℕ, ∃ β41 : ℝ, ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ),
      β41 ≤ β → ∀ {Ω : Type} (𝒢₀ : MeasurableSpace Ω) [_mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
        {N N' : Ω → Measure (CycS ℕ (k + 2) β)} (_S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N')
        {j : ℕ} {u v z : Fin (k + 2) → ℤ} (_hgeom : EscGeom j u v z) {t : ℝ}
        (_hβ : (2 : ℝ) ^ 40 ≤ β) (_ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (_ht2 : t ≤ 4 ^ j)
        (_hjn : (4 : ℝ) ^ j ≤ 4 ^ n) (_hn0 : (4 : ℝ) ^ n₀ < 0.6 * Real.sqrt β)
        (_hθ' : ∀ ρ : ℝ, Real.sqrt (Real.sqrt β) / 16 ≤ ρ →
          (4864 / 10 * ρ ^ 2) ^ indThetaH ≤ ρ / 240)
        (η : ℝ) (_hη : ∀ T : ℝ, 0.6 * Real.sqrt β ≤ T → T ≤ (4 : ℝ) ^ n →
          Real.exp (-((avoidLevel T : ℕ) : ℝ) ^ 2) ≤ η)
        (_hconst : escCstar (k + 2) + 2 * η + C * β ^ (-indDelta (k + 2) / 30) ≤
          ctube (k + 2) escKstar)
        (_hP0 : ∀ τ : ℝ, Real.sqrt β ≤ τ → τ ≤ 4 * Real.sqrt β →
          4 * ((k + 2 : ℕ) : ℝ) * Real.exp (-min ((β ^ (0.3 : ℝ)) ^ 2 /
            (8 * (((0.6 * τ).toNNReal : ℝ≥0) : ℝ))) (β ^ (0.3 : ℝ) / 2)) + η ≤
            cBox ^ (201 * (k + 2)) / (2 * Real.sqrt τ) ^ (201 * (k + 2) * CBox) / 2)
        (_hP1 : ∀ τ : ℝ, Real.sqrt β ≤ τ → τ ≤ 4 * Real.sqrt β → ∀ T' : ℝ≥0,
          0.3 * τ ≤ T' → (T' : ℝ) ≤ 0.5 * τ →
          4 * ((k + 2 : ℕ) : ℝ) * Real.exp (-min ((β ^ (0.3 : ℝ)) ^ 2 / (8 * (T' : ℝ)))
            (β ^ (0.3 : ℝ) / 2)) ≤
            cBox ^ (k + 2) / (3 * Real.sqrt τ) ^ ((k + 2) * CBox) / 2)
        (_hβj : β < 4 ^ j) {γ : ℝ} (_hγ : escGamma56 (k + 2) ≤ γ) (_hn2 : 2 ≤ n)
        (_hj1 : n ^ 20 ≤ 2 ^ j) (_hj2 : 2 ^ j < 2 * n ^ 20),
        ENNReal.ofReal ((n : ℝ) ^ (-γ + 1)) ≤
          Pr {ω | Esc56Event β j u v z t (escYv N v ω)} := by
  obtain ⟨C, hC, H0⟩ := phase_prob hd
  refine ⟨C, hC, fun n₀ => ?_⟩
  obtain ⟨β41, H1⟩ := H0 n₀
  refine ⟨β41, fun β _ n t₀ hβ41 Ω 𝒢₀ mΩ Pr N N' S j u v z hgeom t hβ ht1 ht2 hjn hn0 hθ' η hη
    hconst hP0 hP1 hβj γ hγ hn2 hj1 hj2 => ?_⟩
  have := S.space.ppp.isProbabilityMeasure
  have hβ0 : 0 < β := Fact.out
  obtain ⟨hS, hsβ, hSj⟩ := sqrt_facts (by have := hgeom.hj; omega) hβ hβj ht1
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have hβ16 : (2 : ℝ) ^ 16 ≤ β := le_trans (by norm_num) hβ
  have hm3 := three_le_m hβ16 hβj (by have := hgeom.hj; omega) ht1
  set m := escPhaseM β t with hm
  set τ := claimTau m t with hτ
  obtain ⟨hτ1, hτ2⟩ := tau_bounds hβ0 hsβ
  have hn0' : (4 : ℝ) ^ n₀ < 9 / 10 * Real.sqrt β := by
    have := Real.sqrt_pos.2 hβ0; linarith
  have hn0'' : (4 : ℝ) ^ n₀ < 0.6 * τ := by
    have := Real.sqrt_pos.2 hβ0; linarith
  -- the radii bound
  have hθ : ∀ i : ℕ, 1 ≤ i → i ≤ 2 * m →
      (4864 / 10 * es56Rho t m i ^ 2) ^ indThetaH ≤ escR t m i / 30 := by
    intro i hi1 him
    have hρ := rho_ge_of_one_le ht0 hi1 him
    have hsq : Real.sqrt t / 2 ^ m = Real.sqrt τ := by
      have h22 : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have hpm : (0 : ℝ) < 2 ^ m := by positivity
      rw [div_eq_iff hpm.ne']
      simp only [hτ, claimTau]
      rw [show (2 : ℝ) ^ m = Real.sqrt (4 ^ m) by
        rw [← h22, Real.sqrt_sq hpm.le], ← Real.sqrt_mul (by positivity)]
      congr 1; field_simp
    rw [hsq] at hρ
    have hq : Real.sqrt (Real.sqrt β) ≤ Real.sqrt τ := Real.sqrt_le_sqrt hτ1
    have := hθ' (es56Rho t m i) (by linarith)
    refine this.trans ?_
    have := rho_le_eight_escR ht0 m i
    linarith
  -- the steps
  have hstep : ∀ i : ℕ, i < 2 * m →
      ENNReal.ofReal (escCstar (k + 2)) * Pr {ω | EscG β j u v z t (escYv N v ω) i} ≤
        Pr ({ω | EscG β j u v z t (escYv N v ω) i} ∩
          {ω | EscBi β j u v z t (escYv N v ω) (i + 1)}) := by
    intro i hi
    have := H1 β n t₀ hβ41 𝒢₀ S hgeom hβ hβj ht1 ht2 hjn hsβ hn0' hm3 hθ η
      (fun T hT hT' => hη T (by linarith [Real.sqrt_pos.2 hβ0]) hT') hconst
      (i := i + 1) (by omega) (by omega)
    simpa using this
  have hchain := chain_bound (Pr := Pr) (c := ENNReal.ofReal (escCstar (k + 2)))
    (fun i => {ω | EscG β j u v z t (escYv N v ω) i})
    (fun i => {ω | EscBi β j u v z t (escYv N v ω) i})
    (fun i => by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff]
      exact EscG_succ_iff β j u v z t _ i) (I := 2 * m) (fun i hi => hstep i hi)
  -- phase 0
  have hη0 : Real.exp (-((avoidLevel (0.6 * claimTau m t) : ℕ) : ℝ) ^ 2) ≤ η := by
    refine hη _ (by linarith) ?_
    have : (0.6 : ℝ) * τ ≤ t := by
      have : τ ≤ t := by
        simp only [hτ, claimTau]
        have : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
        rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    linarith [ht2.trans hjn]
  have hP00 := phase0_prob 𝒢₀ S hgeom hβ hβj ht1 ht2 hjn hsβ hm3 hn0'' η _ hη0 le_rfl
    (hP0 τ hτ1 hτ2.le)
  -- the last phase
  have hlast := last_prob S hgeom hβ hβj ht1 ht2 hm3 (cBox ^ (k + 2) /
      (3 * Real.sqrt τ) ^ ((k + 2) * CBox) / 2)
    (fun T' h1 h2 => hP1 τ hτ1 hτ2.le T' h1 h2) le_rfl
  have hincl : {ω | EscG β j u v z t (escYv N v ω) (2 * m)} ∩
      {ω | EscBlast β j u z t (escYv N v ω)} ⊆ {ω | Esc56Event β j u v z t (escYv N v ω)} :=
    fun ω hω => Esc56_of_G hgeom hβ hβj ht1 ht2 hm3 _ hω.1 hω.2
  -- the real inequality
  have hc0 : 0 ≤ cBox ^ (201 * (k + 2)) / (2 * Real.sqrt τ) ^ (201 * (k + 2) * CBox) / 2 := by
    have := cBox_pos; have := Real.sqrt_nonneg τ; positivity
  have hc1 : 0 ≤ cBox ^ (k + 2) / (3 * Real.sqrt τ) ^ ((k + 2) * CBox) / 2 := by
    have := cBox_pos; have := Real.sqrt_nonneg τ; positivity
  have hcs := escCstar_pos (k + 2)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hβn : β < 4 * (n : ℝ) ^ 40 := by
    have h1 : (4 : ℝ) ^ j = (2 ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h2 : (2 : ℝ) ^ j < 2 * (n : ℝ) ^ 20 := by exact_mod_cast hj2
    have h3 : (0 : ℝ) < 2 ^ j := by positivity
    calc β < 4 ^ j := hβj
      _ = (2 ^ j) ^ 2 := h1
      _ < (2 * (n : ℝ) ^ 20) ^ 2 := by gcongr
      _ = 4 * (n : ℝ) ^ 40 := by ring
  have hmj : m ≤ j := by
    have h4 := four_pow_m_le hβ0 hsβ
    have hS1 : (1 : ℝ) ≤ Real.sqrt β := by
      have : (1 : ℝ) ≤ 2 ^ 20 := by norm_num
      linarith
    have : (4 : ℝ) ^ m ≤ 4 ^ j := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) m]
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).1 this
  have hjlog : (j : ℝ) ≤ 20 * Real.logb 2 n + 1 := by
    have h2 : (2 : ℝ) ^ j < 2 * (n : ℝ) ^ 20 := by exact_mod_cast hj2
    have hn0' : (0 : ℝ) < n := by linarith
    have hlt : Real.logb 2 ((2 : ℝ) ^ j) < Real.logb 2 (2 * (n : ℝ) ^ 20) :=
      Real.logb_lt_logb (by norm_num) (by positivity) h2
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), Real.logb_mul (by norm_num)
      (by positivity), Real.logb_self_eq_one (by norm_num), Real.logb_pow] at hlt
    push_cast at hlt
    linarith
  have hm20 : (m : ℝ) ≤ 20 * Real.logb 2 n + 1 := by
    have : (m : ℝ) ≤ j := by exact_mod_cast hmj
    linarith
  have hgam := escGamma_lower_bound (k + 2) hnR (by linarith [(by norm_num : (1 : ℝ) ≤ 2 ^ 40)])
    hβn hm20 hγ
  have hprod := product_lower (k + 2) (by linarith [(by norm_num : (1 : ℝ) ≤ 2 ^ 40)]) hτ1 hτ2.le
  have hreal : (n : ℝ) ^ (-γ + 1) ≤ cBox ^ (k + 2) / (3 * Real.sqrt τ) ^ ((k + 2) * CBox) / 2 *
      (escCstar (k + 2) ^ (2 * m) *
        (cBox ^ (201 * (k + 2)) / (2 * Real.sqrt τ) ^ (201 * (k + 2) * CBox) / 2)) := by
    refine hgam.trans ?_
    have hcp : 0 ≤ escCstar (k + 2) ^ (2 * m) := by positivity
    calc escK0 (k + 2) * β ^ (-escD (k + 2)) * escCstar (k + 2) ^ (2 * m)
        ≤ (cBox ^ (201 * (k + 2)) / (2 * Real.sqrt τ) ^ (201 * (k + 2) * CBox) / 2 *
          (cBox ^ (k + 2) / (3 * Real.sqrt τ) ^ ((k + 2) * CBox) / 2)) *
            escCstar (k + 2) ^ (2 * m) := by gcongr
      _ = _ := by ring
  have hcl : (ENNReal.ofReal (escCstar (k + 2))) ^ (2 * m) = ENNReal.ofReal (escCstar (k + 2) ^ (2 * m)) :=
    (ENNReal.ofReal_pow hcs.le _).symm
  calc ENNReal.ofReal ((n : ℝ) ^ (-γ + 1))
      ≤ ENNReal.ofReal (cBox ^ (k + 2) / (3 * Real.sqrt τ) ^ ((k + 2) * CBox) / 2) *
          ((ENNReal.ofReal (escCstar (k + 2))) ^ (2 * m) *
            ENNReal.ofReal (cBox ^ (201 * (k + 2)) / (2 * Real.sqrt τ) ^ (201 * (k + 2) * CBox) / 2)) := by
        rw [hcl, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc1]
        exact ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal (cBox ^ (k + 2) / (3 * Real.sqrt τ) ^ ((k + 2) * CBox) / 2) *
          ((ENNReal.ofReal (escCstar (k + 2))) ^ (2 * m) *
            Pr {ω | EscG β j u v z t (escYv N v ω) 0}) := by gcongr
    _ ≤ ENNReal.ofReal (cBox ^ (k + 2) / (3 * Real.sqrt τ) ^ ((k + 2) * CBox) / 2) *
          Pr {ω | EscG β j u v z t (escYv N v ω) (2 * m)} := by gcongr
    _ ≤ _ := hlast.trans (measure_mono hincl)

end ElboimSly.Paper.Escape


end
