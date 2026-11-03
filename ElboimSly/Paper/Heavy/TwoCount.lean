/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.TwoCond
public import ElboimSly.Paper.Heavy.MeasStop4
public import ElboimSly.Foundations.Concentration.BinomialTail

/-!
# Lemma 6.2, Step 3: counting

ES22 Lemma 6.2, Step 3 (F62).

For a stopping time `T` (the closing time) and the stopping time `τ_V` built from the canonical
versions `P(ℰ(ξ_{B'}) | ℱ_{ξ_{B'}})`,
`P(τ'(B) ≤ t_n ∧ T) ≤ e^{-n³/17} + P(τ_V < t_n ∧ T)`.
The proof applies counting long gaps to the trials `i = 1, …, K - 1` and
Binomial tails (c).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {f : Filtration ℝ≥0 m0}
  {W : Ω → ℝ → Fin d → ℤ} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- ES22 Lemma 6.2, Step 3. -/
theorem heavy_two_count (hAd : AdaptedCyclic f W) {n m : ℕ} (hn : 3 ≤ n)
    (hjm : heavyScaleJ n ≤ m) (ι : Fin d → ℤ) {tn : ℝ} (htn0 : 0 ≤ tn)
    (htn : tn ≤ (4 : ℝ) ^ (n + 1))
    (hE : ∀ ι', MeasurableSet
      (heavyEscSet W n (heavyScaleJ n) (heavyXi W (heavyScaleJ n) ι')))
    {Tcl : Ω → ℝ≥0∞} (hTcl : IsStoppingTime f Tcl) :
    μ {ω | heavyTauPrimeBlock d n (W ω) m ι ≤ min (ENNReal.ofReal tn) (Tcl ω)} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 3 / 17))) +
        μ {ω | heavyTauV (W ω) (heavyScaleJ n) (fun ι' => heavyEscVersion hAd μ n ι' ω)
          ((n : ℝ) ^ (-escGamma d)) < min (ENNReal.ofReal tn) (Tcl ω)} := by
  classical
  have hn1 : 1 ≤ n := by omega
  set j := heavyScaleJ n with hj
  set c : ℝ := (n : ℝ) ^ (-escGamma d) with hc
  set τV : Ω → ℝ≥0∞ := fun ω => heavyTauV (W ω) j (fun ι' => heavyEscVersion hAd μ n ι' ω) c
    with hτVdef
  have hτV : IsStoppingTime f τV :=
    hAd.isStoppingTime_heavyTauV j (fun ι' ω => heavyEscVersion hAd μ n ι' ω) c
      (fun ι' => (stronglyMeasurable_condExp).measurable)
  have hconst : IsStoppingTime f (fun _ : Ω => ENNReal.ofReal tn) :=
    isStoppingTime_const f tn.toNNReal
  set Tbar : Ω → ℝ≥0∞ := fun ω => min (min (ENNReal.ofReal tn) (Tcl ω)) (τV ω) with hTbar
  have hTb : IsStoppingTime f Tbar := (hconst.min hTcl).min hτV
  have hTfin : ∀ ω, Tbar ω ≠ ⊤ := fun ω =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((min_le_left _ _).trans (min_le_left _ _))
  have hs : ∀ i, IsStoppingTime f (fun ω => heavySi (W ω) n m ι i) :=
    fun i => hAd.isStoppingTime_heavySi (n := n) m ι i
  -- the number of trials
  set K := heavyTrials d n with hK
  have hKpos : 0 < K := heavyTrials_pos hn1
  obtain ⟨K', hK'⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  -- shifted families
  set s' : ℕ → Ω → ℝ≥0∞ := fun k ω => heavySi (W ω) n m ι (k + 1) with hs'
  set r' : ℕ → Ω → ℝ≥0∞ := fun k ω => heavySi (W ω) n m ι (k + 2) with hr'
  set G : ℕ → Set Ω := fun k => {ω | heavySi (W ω) n m ι (k + 1) < Tbar ω} with hG
  set 𝒢 : ℕ → MeasurableSpace Ω := fun k => (hs (k + 1)).measurableSpace with h𝒢
  set p : ℝ := (n : ℝ) ^ (-escGamma d) with hp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hp0 : 0 ≤ p := (Real.rpow_pos_of_pos hnpos _).le
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1)
    (by have := escGamma_gt_two d; linarith)
  have h𝒢le : ∀ i ≤ K', 𝒢 i ≤ m0 := fun i _ => (hs (i + 1)).measurableSpace_le
  have h𝒢mono : ∀ i < K', 𝒢 i ≤ 𝒢 (i + 1) := fun i _ =>
    (hs (i + 1)).measurableSpace_mono (hs (i + 1 + 1)) (fun ω => heavyEntSeq_mono (Nat.le_succ _))
  have hGm : ∀ i < K', MeasurableSet[𝒢 i] (G i) := by
    intro i _
    have := measurableSet_inter_lt_stopping (hs (i + 1)) (hs (i + 1)) hTb (fun ω => le_rfl)
      (H := Set.univ) MeasurableSet.univ
    rwa [Set.univ_inter] at this
  have hAm : ∀ i < K', MeasurableSet[𝒢 (i + 1)] (concGapEvent s' r' ((4 : ℝ) ^ n) i) := by
    intro i _
    exact measurableSet_heavyGapSet hAd n m ι (i + 1)
  have hB : ∀ i < K', ∀ F, MeasurableSet[𝒢 i] F →
      p * μ.real (G i ∩ F) ≤ μ.real (concGapEvent s' r' ((4 : ℝ) ^ n) i ∩ G i ∩ F) := by
    intro i hi
    have hae := heavy_cond_gap hAd hn1 hjm ι (i := i + 1) (by omega) hE hTb hTfin (c := c)
      (fun ω => min_le_right _ _)
    exact (concBernoulli_hyp_iff_condExp (h𝒢le i hi.le) (hGm i hi)
      (measurableSet_heavyGapSet' hAd n m ι (i + 1)) p).2 hae
  have hsr : ∀ i < K', ∀ ω, s' i ω ≤ r' i ω := fun i _ ω =>
    heavyEntSeq_mono (Nat.le_succ _)
  have hrs : ∀ i < K', ∀ ω, r' i ω ≤ s' (i + 1) ω := fun i _ ω => le_rfl
  have hL : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hcount := concGapCount_le (μ := μ) (K := K') (s := s') (r := r') hsr hrs hL htn0
    (G := G) (𝒢 := 𝒢) h𝒢le h𝒢mono hGm hAm hp0 hp1 (fun i hi F hF => hB i hi F hF)
  -- the binomial bound
  have hfloor : ⌊tn / (4 : ℝ) ^ n⌋ ≤ 5 := by
    have : tn / (4 : ℝ) ^ n < 6 := by
      rw [div_lt_iff₀ hL]
      have : (4 : ℝ) ^ (n + 1) = 4 * 4 ^ n := by ring
      nlinarith
    have := Int.floor_lt.2 (show tn / (4 : ℝ) ^ n < ((6 : ℤ) : ℝ) by exact_mod_cast this)
    omega
  have hKp : ((n : ℝ) ^ 3 - 1) / 2 ≤ K' * p := by
    have hKge : (n : ℝ) ^ (escGamma d + 3) ≤ K := Nat.le_ceil _
    have e : (n : ℝ) ^ (escGamma d + 3) * p = (n : ℝ) ^ 3 := by
      rw [hp, ← Real.rpow_add hnpos]
      have : escGamma d + 3 + -escGamma d = ((3 : ℕ) : ℝ) := by push_cast; ring
      rw [this, Real.rpow_natCast]
    have h1 : (n : ℝ) ^ 3 ≤ K * p := by
      have := mul_le_mul_of_nonneg_right hKge hp0
      linarith
    have hK'r : (K' : ℝ) = K - 1 := by rw [hK']; push_cast; ring
    have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn1)
    rw [hK'r]
    nlinarith
  have hbin := concBinomLE_le_exp_cube (K := K') hn hp0 hp1 hKp (m := ⌊tn / (4 : ℝ) ^ n⌋) hfloor
  -- the set inclusion
  have hsub : {ω | heavyTauPrimeBlock d n (W ω) m ι ≤ min (ENNReal.ofReal tn) (Tcl ω)} ⊆
      ({ω | s' K' ω ≤ ENNReal.ofReal tn} ∩ concGamma G K') ∪ {ω | τV ω < min (ENNReal.ofReal tn) (Tcl ω)} := by
    intro ω hω
    have hωK : heavySi (W ω) n m ι (K' + 1) ≤ min (ENNReal.ofReal tn) (Tcl ω) := by
      have : heavyTauPrimeBlock d n (W ω) m ι = heavySi (W ω) n m ι (K' + 1) := by
        unfold heavyTauPrimeBlock; rw [← hK, hK']
      rw [← this]; exact hω
    have hfinK : heavySi (W ω) n m ι (K' + 1) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hωK.trans (min_le_left _ _))
    have hfinK' : heavySi (W ω) n m ι K' ≠ ⊤ :=
      ne_top_of_le_ne_top hfinK (heavyEntSeq_mono (Nat.le_succ _))
    have hstrict : heavySi (W ω) n m ι K' < heavySi (W ω) n m ι (K' + 1) := by
      have h1 := heavyEntSeq_succ_ge (w := W ω) (j := heavyScaleJ n) (m := m)
        (D := (heavyD n m : ℝ≥0∞)) (ι := ι) K'
      refine lt_of_lt_of_le ?_ h1
      refine ENNReal.lt_add_right hfinK' ?_
      have : 0 < heavyD n m := heavyD_pos hn1 m
      exact_mod_cast this.ne'
    by_cases hv : τV ω ≤ heavySi (W ω) n m ι K'
    · right
      exact lt_of_le_of_lt hv (lt_of_lt_of_le hstrict hωK)
    · left
      push Not at hv
      refine ⟨hωK.trans (min_le_left _ _), ?_⟩
      intro k hk
      have hmono : heavySi (W ω) n m ι (k + 1) ≤ heavySi (W ω) n m ι K' :=
        heavyEntSeq_mono (by omega)
      have h1 : heavySi (W ω) n m ι (k + 1) < τV ω := lt_of_le_of_lt hmono hv
      have h2 : heavySi (W ω) n m ι (k + 1) < min (ENNReal.ofReal tn) (Tcl ω) :=
        lt_of_le_of_lt hmono (lt_of_lt_of_le hstrict hωK)
      exact lt_min h2 h1
  have hP1 : μ (({ω | s' K' ω ≤ ENNReal.ofReal tn} ∩ concGamma G K')) ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 3 / 17))) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hcount.trans hbin)
  calc μ {ω | heavyTauPrimeBlock d n (W ω) m ι ≤ min (ENNReal.ofReal tn) (Tcl ω)}
      ≤ μ (({ω | s' K' ω ≤ ENNReal.ofReal tn} ∩ concGamma G K') ∪
          {ω | τV ω < min (ENNReal.ofReal tn) (Tcl ω)}) := measure_mono hsub
    _ ≤ μ ({ω | s' K' ω ≤ ENNReal.ofReal tn} ∩ concGamma G K') +
        μ {ω | τV ω < min (ENNReal.ofReal tn) (Tcl ω)} := measure_union_le _ _
    _ ≤ _ := add_le_add hP1 le_rfl

end ElboimSly.Paper.Heavy
