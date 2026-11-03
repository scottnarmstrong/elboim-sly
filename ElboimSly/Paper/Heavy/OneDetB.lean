/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.OneDetA

/-!
# Theorem 6.1, pathwise part: summing over clean windows

Written proof: proof of ES22 Theorem 6.1 (ES22 §6).

* `unclean_card_le`: at most `R` of the windows `(t + (ℓ-1)h, t + ℓh]`, `1 ≤ ℓ ≤ M`, contain one of
  the regeneration times `σ_1,..., σ_R`.
* `es6_one_det`: on the event `𝒢`, for every `t ∈ [0, t_n - t_n^ε]`,
  `|𝒯 ∩ [t, t + t_n^ε]| ≥ (0.9 + 2/n) t_n^ε`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {β t₀ : ℝ} [Fact (0 < β)]
  {ν : ℕ → Measure (RingSpace d β)}

open scoped Classical in
/-- The windows containing a regeneration time `σ_i`, `1 ≤ i ≤ R`, number at most `R`. -/
theorem unclean_card_le (σ : ℕ → ℝ) (R M : ℕ) {t h : ℝ} (hh : 0 < h)
    (hσ : ∀ ℓ ∈ Finset.Icc 1 M, (∃ i, t + ((ℓ : ℝ) - 1) * h < σ i ∧ σ i ≤ t + ℓ * h) →
      ∃ i ∈ Finset.Icc 1 R, t + ((ℓ : ℝ) - 1) * h < σ i ∧ σ i ≤ t + ℓ * h) :
    ((Finset.Icc 1 M).filter fun ℓ : ℕ =>
      ∃ i, t + ((ℓ : ℝ) - 1) * h < σ i ∧ σ i ≤ t + ℓ * h).card ≤ R := by
  classical
  refine le_trans (Finset.card_le_card (t := (Finset.Icc 1 R).image fun i => ⌈(σ i - t) / h⌉₊) ?_)
    (Finset.card_image_le.trans (by simp))
  intro ℓ hℓ
  simp only [Finset.mem_filter] at hℓ
  obtain ⟨i, hi, h1, h2⟩ := hσ ℓ hℓ.1 hℓ.2
  refine Finset.mem_image.2 ⟨i, hi, ?_⟩
  have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.1 hℓ.1).1
  rw [Nat.ceil_eq_iff (by omega)]
  constructor
  · rw [lt_div_iff₀ hh]
    have : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by rw [Nat.cast_sub hℓ1]; simp
    rw [this]; linarith
  · rw [div_le_iff₀ hh]; linarith

/-- Written proof: proof of ES22 Theorem 6.1, pathwise: on `𝒢`, every window of length `t_n^ε` in
`[0, t_n]` contains relaxed times of measure at least `(0.9 + 2/n) t_n^ε`. -/
theorem es6_one_det {n₀ : ℕ} (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    (hβt : β < indScale t₀ n) (hT : HeavyT d n₀ E n) (hν : ∀ k, Good (ν k))
    (hG : heavyGood d β t₀ n ν) {t : ℝ} (ht0 : 0 ≤ t)
    (htle : t + indScale t₀ n ^ heavyEps d ≤ indScale t₀ n) :
    ENNReal.ofReal ((9 / 10 + 2 / (n : ℝ)) * indScale t₀ n ^ heavyEps d) ≤
      volume ({s : ℝ | 0 ≤ s ∧ IsRelaxedTime ν s} ∩ Icc t (t + indScale t₀ n ^ heavyEps d)) := by
  classical
  have hε : 0 < heavyEps d := heavyEps_pos (by omega)
  have hn4 : 4 ≤ n := hT.t4
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn4r : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have htn0 : 0 < indScale t₀ n := by
    have h1 := indScale_gt_four_pow ht1 n
    exact (by positivity : (0 : ℝ) < 4 ^ n).trans h1
  set T : Set ℝ := {s : ℝ | 0 ≤ s ∧ IsRelaxedTime ν s} with hTdef
  have hTm : MeasurableSet T := measurableSet_relaxedTimes_regen hν
  set h := heavyH d t₀ n with hhdef
  have hh0 : 0 < h := Real.rpow_pos_of_pos htn0 _
  have hh2 : indScale t₀ n ^ heavyEps d = h * h := by
    rw [hhdef]; unfold heavyH; rw [← Real.rpow_add htn0]; congr 1; ring
  rw [hh2] at htle ⊢
  set M : ℕ := ⌊h⌋₊ with hM
  have hMh : (M : ℝ) ≤ h := Nat.floor_le hh0.le
  have hMh1 : h < M + 1 := Nat.lt_floor_add_one h
  set R : ℕ := regenCount ν (indScale t₀ n) with hR
  have hRn : R ≤ n ^ 3 := hG.1
  set a : ℕ → ℝ := fun ℓ => t + ((ℓ : ℝ) - 1) * h with ha
  set P : ℕ → Prop := fun ℓ => ∀ i, ¬ (ENNReal.ofReal (a ℓ) < regenSigma ν i ∧
    regenSigma ν i ≤ ENNReal.ofReal (a ℓ + h)) with hP
  set C : Finset ℕ := (Finset.Icc 1 M).filter P with hC
  set Uc : Finset ℕ := (Finset.Icc 1 M).filter fun ℓ => ¬ P ℓ with hUc
  have hh_le : ∀ ℓ ∈ Finset.Icc 1 M, a ℓ + h ≤ t + h * h := by
    intro ℓ hℓ
    have hℓM : (ℓ : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.1 hℓ).2
    simp only [ha]
    nlinarith
  have hat : ∀ ℓ ∈ Finset.Icc 1 M, t ≤ a ℓ := by
    intro ℓ hℓ
    have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (Finset.mem_Icc.1 hℓ).1
    simp only [ha]
    nlinarith
  -- unclean windows
  have hUcard : Uc.card ≤ R := by
    have key := unclean_card_le (fun i => (regenSigma ν i).toReal) R M (t := t) hh0 (by
      intro ℓ hℓ ⟨i, hi1, hi2⟩
      have hat' := hat ℓ hℓ
      have hle := hh_le ℓ hℓ
      have hfin : regenSigma ν i ≠ ⊤ := by
        intro htop
        simp [htop] at hi1
        linarith
      have hσ : regenSigma ν i = ENNReal.ofReal ((regenSigma ν i).toReal) :=
        (ENNReal.ofReal_toReal hfin).symm
      have hi2' : (regenSigma ν i).toReal ≤ a ℓ + h := by
        simp only [ha]; nlinarith
      have hiR : i ≤ R := by
        rw [hR, le_regenCount_iff ν htn0.le, hσ]
        exact ENNReal.ofReal_le_ofReal (by nlinarith)
      have hi1' : 0 < i := by
        rcases Nat.eq_zero_or_pos i with rfl | hp
        · simp [regenSigma] at hi1; linarith
        · exact hp
      exact ⟨i, Finset.mem_Icc.2 ⟨hi1', hiR⟩, hi1, hi2⟩)
    refine le_trans (Finset.card_le_card ?_) key
    intro ℓ hℓ
    simp only [hUc, Finset.mem_filter, hP, not_forall, not_not] at hℓ
    obtain ⟨hℓM, i, hi⟩ := hℓ
    simp only [Finset.mem_filter]
    refine ⟨hℓM, i, ?_, ?_⟩
    · have hat' := hat ℓ hℓM
      have hfin : regenSigma ν i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi.2
      have := (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) hfin).1 hi.1
      simpa [ha] using this
    · have hfin : regenSigma ν i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi.2
      have hle := hh_le ℓ hℓM
      have := (ENNReal.le_ofReal_iff_toReal_le hfin (by
        have := hat ℓ hℓM; simp only [ha] at this ⊢; nlinarith [hh0])).1 hi.2
      simp only [ha] at this ⊢
      nlinarith
  have hCcard : (M : ℝ) - R ≤ C.card := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 M) P
    have h2 : C.card + Uc.card = M := by
      rw [hC, hUc, this]; simp
    have : (C.card : ℝ) + Uc.card = M := by exact_mod_cast h2
    have : (Uc.card : ℝ) ≤ R := by exact_mod_cast hUcard
    linarith
  -- each clean window
  set c3 : ℝ := (9 / 10 + 3 / (n : ℝ)) * h with hc3
  have hwin : ∀ ℓ ∈ C, ENNReal.ofReal c3 ≤ volume (T ∩ Ioc (a ℓ) (a ℓ + h)) := by
    intro ℓ hℓ
    simp only [hC, Finset.mem_filter] at hℓ
    have hat' := hat ℓ hℓ.1
    have hle := hh_le ℓ hℓ.1
    have hb := clean_window_bound hd hn0 ht1 ht4 hβt hT hν hG (a := a ℓ) (by linarith)
      (by linarith) hℓ.2
    have hsub : T ∩ Icc (a ℓ) (a ℓ + h) ⊆ (T ∩ Ioc (a ℓ) (a ℓ + h)) ∪ {a ℓ} := by
      intro s hs
      rcases hs.2.1.eq_or_lt with heq | hlt
      · exact Or.inr heq.symm
      · exact Or.inl ⟨hs.1, hlt, hs.2.2⟩
    calc ENNReal.ofReal c3 ≤ volume (T ∩ Icc (a ℓ) (a ℓ + h)) := hb
      _ ≤ volume ((T ∩ Ioc (a ℓ) (a ℓ + h)) ∪ {a ℓ}) := measure_mono hsub
      _ ≤ volume (T ∩ Ioc (a ℓ) (a ℓ + h)) + volume ({a ℓ} : Set ℝ) := measure_union_le _ _
      _ = _ := by simp
  -- sum over the clean windows
  have hdisj : (↑C : Set ℕ).PairwiseDisjoint fun ℓ => T ∩ Ioc (a ℓ) (a ℓ + h) := by
    intro ℓ hℓ ℓ' hℓ' hne
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro s hs hs'
    have hlt : ℓ < ℓ' ∨ ℓ' < ℓ := lt_or_gt_of_ne hne
    rcases hlt with hlt | hlt
    · have : (ℓ : ℝ) + 1 ≤ ℓ' := by exact_mod_cast hlt
      have h1 := hs.2.2
      have h2 := hs'.2.1
      simp only [ha] at h1 h2
      nlinarith
    · have : (ℓ' : ℝ) + 1 ≤ ℓ := by exact_mod_cast hlt
      have h1 := hs'.2.2
      have h2 := hs.2.1
      simp only [ha] at h1 h2
      nlinarith
  have hsum : (C.card : ℝ≥0∞) * ENNReal.ofReal c3 ≤ volume (T ∩ Icc t (t + h * h)) := by
    calc (C.card : ℝ≥0∞) * ENNReal.ofReal c3 = ∑ _ℓ ∈ C, ENNReal.ofReal c3 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ℓ ∈ C, volume (T ∩ Ioc (a ℓ) (a ℓ + h)) := Finset.sum_le_sum hwin
      _ = volume (⋃ ℓ ∈ C, T ∩ Ioc (a ℓ) (a ℓ + h)) :=
          (measure_biUnion_finset hdisj fun ℓ _ => hTm.inter measurableSet_Ioc).symm
      _ ≤ _ := by
          apply measure_mono
          intro s hs
          simp only [mem_iUnion] at hs
          obtain ⟨ℓ, hℓ, hs⟩ := hs
          have hℓ' := (Finset.mem_filter.1 hℓ).1
          exact ⟨hs.1, (hat ℓ hℓ').trans hs.2.1.le, hs.2.2.trans (hh_le ℓ hℓ')⟩
  refine le_trans ?_ hsum
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  -- the arithmetic, using (T10)
  have hT10 : 2 * (n : ℝ) * ((n : ℝ) ^ 3 + 2) ≤ h := (hT.t10.2).trans (heavyH_ge (by omega) ht1)
  have hRr : (R : ℝ) ≤ (n : ℝ) ^ 3 := by exact_mod_cast hRn
  have hCc : h - 1 - (n : ℝ) ^ 3 ≤ C.card := by linarith
  have hc3pos : 0 ≤ c3 := by rw [hc3]; positivity
  have hq : 0 < (9 / 10 + 3 / (n : ℝ)) := by positivity
  have hdiv : (1 + (n : ℝ) ^ 3) * (9 / 10 + 3 / n) ≤ h / n := by
    rw [le_div_iff₀ hnpos]
    have h34 : 3 / (n : ℝ) ≤ 3 / 4 := by
      rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
    have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
    have : (1 + (n : ℝ) ^ 3) * (9 / 10 + 3 / n) ≤ 2 * ((n : ℝ) ^ 3 + 2) := by nlinarith
    nlinarith
  calc (9 / 10 + 2 / (n : ℝ)) * (h * h) ≤ (h - 1 - (n : ℝ) ^ 3) * c3 := by
        rw [hc3]
        have e : 2 / (n : ℝ) = 3 / n - 1 / n := by ring
        have : (h - 1 - (n : ℝ) ^ 3) * ((9 / 10 + 3 / n) * h) -
            (9 / 10 + 2 / n) * (h * h) = h * (h / n - (1 + (n : ℝ) ^ 3) * (9 / 10 + 3 / n)) := by
          field_simp; ring
        nlinarith [mul_nonneg hh0.le (sub_nonneg.2 hdiv)]
    _ ≤ C.card * c3 := mul_le_mul_of_nonneg_right hCc hc3pos

end ElboimSly.Paper.Heavy
