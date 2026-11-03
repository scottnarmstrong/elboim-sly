/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.Lemma82Union
public import Mathlib

/-!
# Lemma 8.2 (ES22 §8): pair proximity at the base

ES22 Lemma 8.2 (ES22 §8, Lemma 8.2, ES22 §8).

`es8_lemma82`: for all starting data `(u₁, u₂, q₁, q₂)`, the event
`Ω(u₁,u₂,q₁,q₂;t'_n) ∩ {|𝔓_n| ≥ 3.9ⁿ}` has probability at most `e^{-n³}`.  The proof writes
`q₂ = q₁ + q + kβ` with `q ∈ [0, β)` and distinguishes Case A (`q ≤ t'`), Case C (`q ≥ β - t'`) and
Case B (`t' < q < β - t'`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper.Base

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem lemPairSet_periodic {ν : Measure (RingSpace d β)} (hν : Good ν) (u₁ u₂ : Fin d → ℤ)
    (q₁ q t' ρ : ℝ) (k : ℤ) :
    lemPairSet ν u₁ u₂ q₁ (q₁ + q + k * β) t' ρ = lemPairSet ν u₁ u₂ q₁ (q₁ + q) t' ρ := by
  ext s₂
  simp only [lemPairSet, mem_ofPred_eq]
  constructor
  · rintro ⟨hs, s₁, hs₁, h⟩
    refine ⟨hs, s₁, hs₁, ?_⟩
    rwa [cycWalk_add_zsmul hν u₂ (q₁ + q) k hs.1] at h
  · rintro ⟨hs, s₁, hs₁, h⟩
    refine ⟨hs, s₁, hs₁, ?_⟩
    rwa [cycWalk_add_zsmul hν u₂ (q₁ + q) k hs.1]

theorem eps_le_exp {d n : ℕ} (hnK : es8nK d ≤ n) :
    es8Eps d n ≤ Real.exp (-(n : ℝ) ^ 3) := by
  have h := es8nK_spec d n hnK
  have hCA : 0 ≤ es8CA d * Real.exp (-(4 : ℝ) ^ n / 12) := by
    unfold es8CA
    have := latConst_nonneg (c := 1 / 6) (by norm_num) d
    positivity
  have hone : (1 : ℝ) ≤ (2 * 4 ^ n : ℝ) ^ d := one_le_pow₀ (by
    have : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    linarith)
  have heps : 0 ≤ es8Eps d n := by
    have := es8Eps_ge d n
    have h1 : 0 < Real.exp (-(n : ℝ) ^ 4) := Real.exp_pos _
    have h2 : 0 < ((2 : ℝ) ^ (n ^ 4))⁻¹ := by positivity
    linarith
  nlinarith

/-- **ES22 Lemma 8.2** (ES22 Lemma 8.2, for all starting data): the probability that the walks do not
merge by time `t'_n` and the contact set `𝔓_n` has measure `≥ 3.9ⁿ` is at most `e^{-n³}`. -/
theorem es8_lemma82 {Ω : Type} [MeasurableSpace Ω] {Pe : Measure Ω}
    {ν : Ω → Measure (RingSpace d β)}
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe) (hd : 5 ≤ d) {n : ℕ} (hn4 : 4 ≤ n)
    (hnC : lem82nC d ≤ n) (hn2 : lem82n2 d ≤ n) (hn39 : 14980 ≤ n) (hnK : es8nK d ≤ n)
    {t₀ : ℝ} (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (htβ : indScale t₀ n ≤ β)
    (u₁ u₂ : Fin d → ℤ) (q₁ q₂ : ℝ) :
    Pe {ω | cycOmega (ν ω) u₁ u₂ q₁ q₂ (indScaleReduced t₀ n) ∧
        ENNReal.ofReal ((39 / 10 : ℝ) ^ n) ≤
          volume {s₂ : ℝ | s₂ ∈ Icc 0 (indScaleReduced t₀ n) ∧
            ∃ s₁ ∈ Icc 0 (indScaleReduced t₀ n),
              ‖ElboimSly.cycWalk (ν ω) u₁ q₁ s₁ - ElboimSly.cycWalk (ν ω) u₂ q₂ s₂‖ ≤
                (19 / 10 : ℝ) ^ n}} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 3)) := by
  classical
  have : NeZero d := ⟨by omega⟩
  have hβ : 0 < β := Fact.out
  set t' : ℝ := indScaleReduced t₀ n with ht'
  have ht'pos : 0 < t' := indScaleReduced_pos (by omega) ht1
  have hT2 : lem82T n t₀ = 2 * t' := lem82T_eq_two_mul n t₀
  have hTβ : 2 * t' < β := by rw [← hT2]; exact lem82T_lt_beta hn4 hβ htβ
  obtain ⟨q, k, hq0, hqβ, hq₂⟩ := exists_mod (β := β) q₁ q₂
  have hgood : ∀ᵐ ω ∂Pe, Good (ν ω) := ae_good hν
  have hm : (0 : ℝ) < (39 / 10 : ℝ) ^ n := by positivity
  have hspec := es8nK_spec d n hnK
  set ρ : ℝ := (19 / 10 : ℝ) ^ n with hρ
  set m : ℝ := (39 / 10 : ℝ) ^ n with hmdef
  have hCA : 0 ≤ es8CA d * Real.exp (-(4 : ℝ) ^ n / 12) := by
    unfold es8CA
    have := latConst_nonneg (c := 1 / 6) (by norm_num) d
    positivity
  have heps : 0 ≤ es8Eps d n := by
    have := es8Eps_ge d n
    have h1 : 0 < Real.exp (-(n : ℝ) ^ 4) := Real.exp_pos _
    have h2 : 0 < ((2 : ℝ) ^ (n ^ 4))⁻¹ := by positivity
    linarith
  have farB : ∀ (c : Fin d → ℤ) (r : ℝ), Pe {ω | ¬ farGood (ν ω) c r n (2 * t').toNNReal} ≤
      ENNReal.ofReal (es8CA d * Real.exp (-(4 : ℝ) ^ n / 12)) := fun c r => by
    have := far_prob hν hn4 ht1 ht4 (le_of_lt (lem82T_lt_beta hn4 hβ htβ)) c r
    rw [hT2] at this
    rwa [neg_div]
  have pairB : ∀ (a b : Fin d → ℤ) (r : ℝ), a ≠ b →
      Pe {ω | ENNReal.ofReal m ≤ volume (cycContactSet (ν ω) a b r (2 * t') ρ)} ≤
        ENNReal.ofReal (es8Eps d n) := fun a b r hab => by
    have := (es8_pair hν hd hn4 hnC hn2 hn39 ht1 ht4 htβ a b hab r).2
    rwa [hT2] at this
  have finalU : ∀ c : Fin d → ℤ,
      es8CA d * Real.exp (-(4 : ℝ) ^ n / 12) + (((farBox c n).erase c).card : ℕ) * es8Eps d n ≤
        Real.exp (-(n : ℝ) ^ 3) := fun c => by
    have h1 : ((((farBox c n).erase c).card : ℕ) : ℝ) ≤ (2 * 4 ^ n : ℝ) ^ d :=
      (Nat.cast_le.2 (Finset.card_erase_le)).trans (card_farBox c n)
    nlinarith
  set E : Set Ω := {ω | cycOmega (ν ω) u₁ u₂ q₁ q₂ t' ∧ ENNReal.ofReal m ≤
      volume {s₂ : ℝ | s₂ ∈ Icc 0 t' ∧ ∃ s₁ ∈ Icc 0 t',
        ‖ElboimSly.cycWalk (ν ω) u₁ q₁ s₁ - ElboimSly.cycWalk (ν ω) u₂ q₂ s₂‖ ≤ ρ}} with hE
  by_cases hA : q ≤ t'
  · -- Case A
    have hU := union_bound (Pe := Pe) ((farBox u₁ n).erase u₁) (S := E)
      (bad := {ω | ¬ farGood (ν ω) u₁ q₁ n (2 * t').toNNReal})
      (E := fun b => {ω | ENNReal.ofReal m ≤ volume (cycContactSet (ν ω) u₁ b q₁ (2 * t') ρ)})
      hCA heps ?_ (farB u₁ q₁)
      (fun b hb => pairB u₁ b q₁ (Ne.symm (Finset.ne_of_mem_erase hb)))
    · exact hU.trans (ENNReal.ofReal_le_ofReal (finalU u₁))
    · filter_upwards [hgood] with ω hω hEω
      by_cases hf : farGood (ν ω) u₁ q₁ n (2 * t').toNNReal
      · right
        obtain ⟨b, hb1, hb2, hb3⟩ := caseA_exists hω hm hq0 hA hq₂ hEω.1.1 hf hEω.2
        exact mem_biUnion (Finset.mem_erase.2 ⟨hb1, mem_farBox hb2⟩) hb3
      · left; exact hf
  by_cases hC : β - t' ≤ q
  · -- Case C
    have hU := union_bound (Pe := Pe) ((farBox u₂ n).erase u₂) (S := E)
      (bad := {ω | ¬ farGood (ν ω) u₂ (q₁ + q) n (2 * t').toNNReal})
      (E := fun a => {ω | ENNReal.ofReal m ≤
        volume (cycContactSet (ν ω) a u₂ (q₁ + q) (2 * t') ρ)})
      hCA heps ?_ (farB u₂ (q₁ + q))
      (fun a ha => pairB a u₂ (q₁ + q) (Finset.ne_of_mem_erase ha))
    · exact hU.trans (ENNReal.ofReal_le_ofReal (finalU u₂))
    · filter_upwards [hgood] with ω hω hEω
      by_cases hf : farGood (ν ω) u₂ (q₁ + q) n (2 * t').toNNReal
      · right
        obtain ⟨a, ha1, ha2, ha3⟩ := caseC_exists hω hm hC hqβ hq₂ hEω.1.1 hf hEω.2
        exact mem_biUnion (Finset.mem_erase.2 ⟨ha1, mem_farBox ha2⟩) ha3
      · left; exact hf
  · -- Case B
    push Not at hA hC
    have hb := caseB_prob hν hd hn4 hnC hn2 hn39 ht1 ht4 u₁ u₂ (ra := q₁) (rb := q₁ + q)
      (by linarith) (by linarith)
    refine le_trans (measure_mono_ae ?_) (hb.trans ?_)
    · filter_upwards [hgood] with ω hω hEω
      have h2 := hEω.2
      show ENNReal.ofReal m ≤ volume (lemPairSet (ν ω) u₁ u₂ q₁ (q₁ + q) t' ρ)
      rw [← lemPairSet_periodic hω u₁ u₂ q₁ q t' ρ k, ← hq₂]
      exact h2
    · rw [← ENNReal.ofReal_add (Real.exp_pos _).le (by positivity)]
      refine ENNReal.ofReal_le_ofReal ((le_trans ?_ (es8Eps_ge d n)).trans (eps_le_exp hnK))
      rw [one_div, inv_pow]

end ElboimSly.Paper

end
