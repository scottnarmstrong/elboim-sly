/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.TauBad
public import ElboimSly.Paper.Heavy.MeasStop4

/-!
# Corollary 6.3: `τ'` is rarely small

Corollary after Lemma 6.2 (ES22 §6, eq. (tau')).

* `blockIdx_abs_le`, `ncard_blocksNear_le`: the blocks of `ℬ_m` within distance `R` of the origin
  have indices in `[-R, R]^d`; there are at most `(2R+1)^d` of them.
* `tauPrime_det`: before `τ_fast`, `τ' ≤ t_n ∧ t_reg` forces some `τ'(B) ≤ t_n ∧ t_reg` with
  `m₀ ≤ m ≤ n` and `d(0, B) < 5^n`.
* `es6_three_of_two`: the probability bound, from `P(τ_fast ≤ t_n ∧ t_reg) ≤ ϖ` and the bound of
  ES22 Lemma 6.2 for each block (distinctly named hypothesis `h2`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {β t₀ : ℝ}

theorem blockIdx_abs_le {m R : ℕ} {ι : Fin d → ℤ}
    (hι : latDist (0 : Fin d → ℤ) (heavyBlock m ι) ≤ (R : ℝ)) (c : Fin d) :
    |ι c| ≤ (R : ℤ) := by
  obtain ⟨a, haB, ha⟩ := exists_le_of_latDist_le (heavyBlock_nonempty m ι) hι
  have h1 : ((|a c| : ℤ) : ℝ) ≤ (R : ℝ) := by
    have h2 : ‖(0 - a) c‖ ≤ ‖0 - a‖ := norm_le_pi_norm (0 - a) c
    rw [Int.cast_abs]
    simpa [Int.norm_eq_abs] using h2.trans ha
  have h4 : |a c| ≤ (R : ℤ) := by exact_mod_cast h1
  have hbl : a c / 2 ^ m = ι c := haB c
  have h5 : |ι c| ≤ |a c| := by rw [← hbl]; exact Int.abs_ediv_le_abs _ _
  exact h5.trans h4

/-- The finset of candidate indices. -/
def blocksBox (d R : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(R : ℤ)) (R : ℤ)

theorem card_blocksBox (d R : ℕ) : (blocksBox d R).card = (2 * R + 1) ^ d := by
  unfold blocksBox
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- Corollary after Lemma 6.2, pathwise. -/
theorem tauPrime_det {w : ℝ → Fin d → ℤ} (hT : HeavyT d n₀ E n) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    (hw : IsCyclicPath w) {mm : ℝ≥0∞} (hmm : mm ≤ ENNReal.ofReal (indScale t₀ n))
    (hfast : mm < pathTfastCube w n) (hτ : heavyTauPrime d t₀ n w ≤ mm) :
    ∃ m ι, heavyM0 d t₀ n ≤ m ∧ m ≤ n ∧
      latDist (0 : Fin d → ℤ) (heavyBlock m ι) ≤ ((5 ^ n : ℕ) : ℝ) ∧
        heavyTauPrimeBlock d n w m ι ≤ mm := by
  have hn : 1 ≤ n := by have := hT.t4; omega
  have htop : heavyTauPrime d t₀ n w < ⊤ :=
    lt_of_le_of_lt (hτ.trans hmm) ENNReal.ofReal_lt_top
  obtain ⟨m, hm0, ι, hmι⟩ := heavyTauPrime_attained hw hn htop
  have hblock : heavyTauPrimeBlock d n w m ι ≤ mm := hmι ▸ hτ
  refine ⟨m, ι, hm0, ?_, ?_, hblock⟩
  · -- m ≤ n
    have hK : 1 ≤ heavyTrials d n := heavyTrials_pos hn
    have h1 : heavyEntSeq w (heavyScaleJ n) m (heavyD n m : ℝ≥0∞) ι 0 + (heavyD n m : ℝ≥0∞) ≤
        heavyEntSeq w (heavyScaleJ n) m (heavyD n m : ℝ≥0∞) ι 1 := heavyEntSeq_succ_ge 0
    have h2 : heavyEntSeq w (heavyScaleJ n) m (heavyD n m : ℝ≥0∞) ι 1 ≤
        heavyTauPrimeBlock d n w m ι := heavyEntSeq_mono hK
    have h3 : (heavyD n m : ℝ≥0∞) ≤ ENNReal.ofReal (indScale t₀ n) :=
      le_add_self.trans (h1.trans (h2.trans (hblock.trans hmm)))
    have h4 : ((heavyD n m : ℕ) : ℝ) ≤ indScale t₀ n := by
      rw [← ENNReal.ofReal_natCast] at h3
      exact (ENNReal.ofReal_le_ofReal_iff (by
        have := indScale_gt_four_pow ht1 n
        exact (by positivity : (0 : ℝ) ≤ 4 ^ n).trans this.le)).1 h3
    have h5 := h4.trans (indScale_le_four_pow ht4 n)
    by_contra hmn
    push Not at hmn
    have h6 : (4 : ℝ) ^ n ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hmn.le
    have h7 : (16 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (4 : ℝ) ≤ n := by exact_mod_cast hT.t4
      nlinarith
    have h8 : ((heavyD n m : ℕ) : ℝ) = (n : ℝ) ^ 2 * 4 ^ m := by
      unfold heavyD; push_cast; ring
    rw [h8] at h5
    have h9 : (4 : ℝ) ^ (n + 1) = 4 * 4 ^ n := by ring
    have : (0 : ℝ) < 4 ^ n := by positivity
    nlinarith
  · -- the block is within distance 5^n of the origin
    set B := heavyBlock m ι with hB
    have hent : entranceTime w B ≤ mm := by
      refine le_trans ?_ hblock
      exact (heavyEntSeq_mono (Nat.zero_le _) : heavyEntSeq w (heavyScaleJ n) m
        (heavyD n m : ℝ≥0∞) ι 0 ≤ _)
    have hentlt : entranceTime w B < ⊤ := lt_of_le_of_lt (hent.trans hmm) ENNReal.ofReal_lt_top
    have hex : ∃ s : ℝ, 0 ≤ s ∧ w s ∈ B := by
      by_contra hno
      push Not at hno
      have : entranceTime w B = ⊤ := by
        unfold entranceTime
        refine iInf_eq_top.2 fun t => iInf_eq_top.2 fun ht => absurd ht.2 (hno t ht.1)
      exact absurd this hentlt.ne
    obtain ⟨s0, hs0⟩ := hex
    obtain ⟨s'', hs''0, -, hs''B, hs''eq⟩ := exists_entrance_real hw hs0.1 hs0.2
    have hs''le : ENNReal.ofReal s'' ≤ mm := hs''eq ▸ hent
    have htn : s'' ≤ indScale t₀ n := by
      have := hs''le.trans hmm
      exact (ENNReal.ofReal_le_ofReal_iff (by
        have := indScale_gt_four_pow ht1 n
        exact (by positivity : (0 : ℝ) ≤ 4 ^ n).trans this.le)).1 this
    have hnorm : ‖w s''‖ < 5 ^ n := norm_lt_five_pow_of_lt_pathTfastCube hw hT.t3
      (by omega) hs''0 (htn.trans (indScale_le_four_pow ht4 n)) (lt_of_le_of_lt hs''le hfast)
    refine (latDist_le_norm_of_mem hs''B 0).trans ?_
    have : ‖(0 : Fin d → ℤ) - w s''‖ = ‖w s''‖ := by simp
    push_cast
    linarith

/-- Corollary after Lemma 6.2, conditional on the per-block bound `h2` of ES22 Lemma 6.2 and on
`P(τ_fast ≤ t_n ∧ t_reg) ≤ ϖ`. -/
theorem es6_three_of_two {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω}
    {env : Ω → Measure (RingSpace d β)} (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    (hT : HeavyT d n₀ E n) (hgood : ∀ᵐ ω ∂Pe, Good (env ω)) {ϖ q : ℝ}
    (hfast : Pe {ω | pathTfastCube (fun s : ℝ => cycWalk (env ω) 0 0 s) n ≤
      min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))} ≤ ENNReal.ofReal ϖ)
    (h2 : ∀ m (ι : Fin d → ℤ), heavyM0 d t₀ n ≤ m →
      Pe {ω | heavyTauPrimeBlock d n (fun s : ℝ => cycWalk (env ω) 0 0 s) m ι ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))} ≤ ENNReal.ofReal q) :
    Pe {ω | heavyTauPrime d t₀ n (fun s : ℝ => cycWalk (env ω) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))} ≤
      ENNReal.ofReal ϖ + (((n + 1) * 5 ^ (d * (n + 1)) : ℕ) : ℝ≥0∞) * ENNReal.ofReal q := by
  classical
  set F : Finset (ℕ × (Fin d → ℤ)) :=
    ((Finset.range (n + 1)).filter fun m => heavyM0 d t₀ n ≤ m) ×ˢ blocksBox d (5 ^ n) with hF
  have hsub : {ω | heavyTauPrime d t₀ n (fun s : ℝ => cycWalk (env ω) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))} ≤ᵐ[Pe]
      {ω | pathTfastCube (fun s : ℝ => cycWalk (env ω) 0 0 s) n ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))} ∪
      ⋃ p ∈ F, {ω | heavyTauPrimeBlock d n (fun s : ℝ => cycWalk (env ω) 0 0 s) p.1 p.2 ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))} := by
    filter_upwards [hgood] with ω hω hmem
    by_cases hf : pathTfastCube (fun s : ℝ => cycWalk (env ω) 0 0 s) n ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))
    · exact Or.inl hf
    · refine Or.inr ?_
      obtain ⟨m, ι, hm0, hmn, hdist, hblk⟩ := tauPrime_det hT ht1 ht4
        (isCyclicPath_cycWalk hω) (min_le_left _ _) (not_le.1 hf) hmem
      simp only [mem_iUnion, mem_ofPred_eq, exists_prop]
      refine ⟨(m, ι), ?_, hblk⟩
      simp only [hF, Finset.mem_product, Finset.mem_filter, Finset.mem_range, blocksBox,
        Fintype.mem_piFinset, Finset.mem_Icc]
      refine ⟨⟨by omega, hm0⟩, fun c => ?_⟩
      have := abs_le.1 (blockIdx_abs_le hdist c)
      exact ⟨this.1, this.2⟩
  refine (measure_mono_ae hsub).trans ((measure_union_le _ _).trans ?_)
  refine add_le_add hfast ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ p ∈ F, Pe {ω | heavyTauPrimeBlock d n (fun s : ℝ => cycWalk (env ω) 0 0 s) p.1 p.2 ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (env ω))}
      ≤ ∑ _p ∈ F, ENNReal.ofReal q := Finset.sum_le_sum fun p hp =>
        h2 p.1 p.2 (by simp only [hF, Finset.mem_product, Finset.mem_filter] at hp; exact hp.1.2)
    _ = (F.card : ℝ≥0∞) * ENNReal.ofReal q := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        gcongr
        have hcard : F.card ≤ (n + 1) * (2 * 5 ^ n + 1) ^ d := by
          rw [hF, Finset.card_product, card_blocksBox]
          gcongr
          exact (Finset.card_filter_le _ _).trans (by simp)
        have h5 : 2 * 5 ^ n + 1 ≤ 5 ^ (n + 1) := by
          have : 1 ≤ 5 ^ n := Nat.one_le_pow _ _ (by norm_num)
          rw [pow_succ]; omega
        calc F.card ≤ (n + 1) * (2 * 5 ^ n + 1) ^ d := hcard
          _ ≤ (n + 1) * (5 ^ (n + 1)) ^ d := by gcongr
          _ = _ := by rw [← pow_mul, mul_comm (n + 1) d]

end ElboimSly.Paper.Heavy
