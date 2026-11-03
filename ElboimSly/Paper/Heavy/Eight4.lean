/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Eight3

/-!
# Lemma 6.8

ES22 Lemma 6.8 (§6; deviation F58, F61).

Let `2 t'_k + 4 ≤ t < τ_fast ∧ τ_jump ∧ τ' ∧ T(w)` (and `β < t_n`, the thresholds `HeavyT`), `w` a
cyclic path with the no-return property, and suppose `w(t) ∉ Λ_t`.  Then
`|𝒯(w) ∩ [t - t'_k, t]| ≥ (0.9 + 4/n) t'_k`.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {β t₀ : ℝ} {w : ℝ → Fin d → ℤ}

/-- ES22 Lemma 6.8. -/
theorem es6_eight (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hβ : 0 < β)
    (hβt : β < indScale t₀ n) (hT : HeavyT d n₀ E n) (hw : IsCyclicPath w)
    (hnr : HasNoReturn β w) {t : ℝ} (ht : 2 * heavyTkPrime d t₀ n + 4 ≤ t)
    (htf : ENNReal.ofReal t < pathTfastCube w n) (htj : ENNReal.ofReal t < pathTjumpCube w n)
    (htau : ENNReal.ofReal t < heavyTauPrime d t₀ n w)
    (htT : ENNReal.ofReal t < cycClosingTime β w) (hnot : w t ∉ badUnion d β t₀ n w t) :
    ENNReal.ofReal ((9 / 10 + 4 / (n : ℝ)) * heavyTkPrime d t₀ n) ≤
      volume (relaxedTimes β w ∩ Icc (t - heavyTkPrime d t₀ n) t) := by
  classical
  set k := heavyLevel d n with hk
  set tk := heavyTkPrime d t₀ n with htk
  set tn := indScale t₀ n with htn
  obtain ⟨hc1, hc2, -, -⟩ := scales_facts_c (d := d) (n := n) ht1 ht4 hT.t1.2
  have htk2 : 2 < tk := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hn4 : 4 ≤ n := hT.t4
  have hn1 : 1 ≤ n := by omega
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hδ := heavy_indDelta_pos (d := d) (by omega)
  set ι0 := heavyBlockIdx k (w t) with hι0
  set B := heavyBlock k ι0 with hB
  have hBne : B.Nonempty := heavyBlock_nonempty k ι0
  have hwt : w t ∈ B := mem_heavyBlock_idx k (w t)
  have hgood : ¬ BadByTime d β t₀ n w ι0 t := fun h => hnot (mem_iUnion₂.2 ⟨ι0, h, hwt⟩)
  set tst := heavyTStar β tk t with htst
  have hCI : tst ∈ cycIntTimes β := heavyTStar_mem hβ (by linarith)
  have h1 : t - tk - 1 < tst := lt_heavyTStar_add_one hβ
  have h2 : tst ≤ t - tk := heavyTStar_le hβ
  have step1 : ∀ s, tst ≤ s → s ≤ t → latDist (w s) B ≤ (2 : ℝ) ^ (k - 1) + 2 * (n : ℝ) ^ 3 :=
    fun s hs1 hs2 => eight_step1 hd ht1 ht4 hβ hT hw ht0 htf hgood hwt hCI h1 h2 hs1 hs2
  have hnum_a := eight_num_a hd ht1 ht4 hT
  have hnum_b := eight_num_b hd ht1 ht4 hT
  have hk1 : 1 ≤ k := by have := hT.t1.2; omega
  have h2k : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  have h2k2 : (2 : ℝ) ^ (k + 2) = 4 * 2 ^ k := by ring
  have hpk : (0 : ℝ) < 2 ^ (k - 1) := by positivity
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hrp : 0 ≤ tn ^ indDelta d := Real.rpow_nonneg (le_trans (by positivity) (indScale_gt_four_pow ht1 n).le) _
  have hpk2 : (0 : ℝ) < 2 ^ k := by positivity
  have hstN : latDist (w tst) B ≤ 2 ^ (k + 2) := by
    have := step1 tst le_rfl (by linarith)
    linarith
  -- good at tst, cover
  have hgood_st : ¬ BadByTime d β t₀ n w ι0 tst := fun h => hgood (h.mono (by linarith))
  have hts : tk + 3 ≤ tst := by linarith
  have htf' : ENNReal.ofReal tst < pathTfastCube w n :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith)) htf
  have htau' : ENNReal.ofReal tst < heavyTauPrime d t₀ n w :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith)) htau
  obtain ⟨G, hGcard, hGprops, hGcover⟩ :=
    claim69 hd hn0 ht1 ht4 hβ hT hw hts htf' htau' hgood_st
  -- segment at tst is relaxed
  have hrel : SegRelaxed β tk w (heavyLevelPrime d t₀ n) tst := by
    by_contra h
    exact hgood (Or.inl ⟨tst, hCI, hstN, by linarith,
      not_segClosed hnr hCI.1 (by linarith) htT, h⟩)
  -- proximity sets are small
  have hprox : ∀ b ∈ G, volume (proxSet tk w ((1.9 : ℝ) ^ k) b tst) <
      ENNReal.ofReal ((3.9 : ℝ) ^ k) := by
    intro b hb
    obtain ⟨hbCI, hb2, hbN⟩ := hGprops b hb
    by_contra hge
    push Not at hge
    refine hgood (Or.inr (Or.inr ⟨b, hbCI, tst, hCI, ?_, hstN, by linarith, by linarith,
      not_segMerge hnr hbCI.1 (by linarith) (by linarith) htT,
      not_segClosed hnr hbCI.1 (by linarith) htT,
      not_segClosed hnr hCI.1 (by linarith) htT, hge⟩))
    have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (k + 2) := by
      rw [pow_succ _ (k + 1)]; nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) (k + 1)]
    exact hbN.trans this
  -- measure bookkeeping
  set U1 := heavyU1 β tk w t with hU1
  set U2 := heavyU2 β tk tn w t with hU2
  set P : Set ℝ := Icc (t - tk) t with hP
  set R : Set ℝ := {u : ℝ | u ∈ Icc 0 tk ∧ IsRelaxedTimeWrt β w tst (tst + u)} with hR
  set R' : Set ℝ := (fun s => s + (-tst)) ⁻¹' R with hR'
  have hR'vol : volume R' = volume R := measure_preimage_add_right volume (-tst) R
  have hR'sub : R' ⊆ U1 ∪ Ico tst (t - tk) := by
    intro s hs
    obtain ⟨⟨hu0, hu1⟩, hrl⟩ := hs
    rw [show tst + (s + -tst) = s by ring] at hrl
    by_cases hc : t - tk ≤ s
    · left
      exact ⟨⟨⟨hc, by linarith⟩, ⟨by linarith, by linarith⟩⟩, hrl⟩
    · right
      exact ⟨by linarith, by linarith⟩
  have hIco : volume (Ico tst (t - tk)) ≤ ENNReal.ofReal 1 := by
    rw [Real.volume_Ico]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hU1P : U1 ⊆ P := fun s hs => hs.1.1
  have hU1sub : U1 ⊆ (U1 ∩ U2) ∪ (P \ U2) := by
    intro s hs
    by_cases h : s ∈ U2
    · exact Or.inl ⟨hs, h⟩
    · exact Or.inr ⟨hU1P hs, h⟩
  have hPU2 : P \ U2 ⊆ Ioc (tst + tk) t ∪ ⋃ b ∈ G, (fun s => s + (-tst)) ⁻¹'
      proxSet tk w ((1.9 : ℝ) ^ k) b tst := by
    rintro s ⟨hsP, hsU⟩
    by_cases hy : tst + tk < s
    · exact Or.inl ⟨hy, hsP.2⟩
    · right
      push Not at hy
      have hs1 : tst ≤ s := by linarith [hsP.1]
      have hex : ∃ s' ∈ Ico (0 : ℝ) tst, ‖w s - w s'‖ ≤ tn ^ indDelta d := by
        by_contra hno
        push Not at hno
        exact hsU ⟨⟨hs1, hsP.2⟩, hno⟩
      obtain ⟨s', hs', hns'⟩ := hex
      have hsd := step1 s hs1 hsP.2
      have hmem : w s' ∈ latNbhd B ((2 : ℝ) ^ k) := by
        have := latDist_le_add hBne (w s') (w s)
        rw [norm_sub_rev] at this
        show latDist (w s') B ≤ 2 ^ k
        linarith
      obtain ⟨b, hb, u₁, hu₁, hnb⟩ := hGcover s' hs'.1 hs'.2.le hmem
      refine mem_iUnion₂.2 ⟨b, hb, ?_⟩
      refine ⟨⟨by linarith, by linarith⟩, u₁, hu₁, ?_⟩
      rw [show tst + (s + -tst) = s by ring]
      have : ‖w (b + u₁) - w s‖ ≤ ‖w (b + u₁) - w s'‖ + ‖w s' - w s‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      rw [norm_sub_rev (w (b + u₁)) (w s')] at this
      rw [norm_sub_rev (w s') (w s)] at this
      linarith
  have hvolP : volume (P \ U2) ≤ ENNReal.ofReal 1 + ENNReal.ofReal (G.card * (3.9 : ℝ) ^ k) := by
    calc volume (P \ U2) ≤ volume (Ioc (tst + tk) t ∪ ⋃ b ∈ G, (fun s => s + (-tst)) ⁻¹'
          proxSet tk w ((1.9 : ℝ) ^ k) b tst) := measure_mono hPU2
      _ ≤ volume (Ioc (tst + tk) t) + volume (⋃ b ∈ G, (fun s => s + (-tst)) ⁻¹'
          proxSet tk w ((1.9 : ℝ) ^ k) b tst) := measure_union_le _ _
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (G.card * (3.9 : ℝ) ^ k) := by
          gcongr
          · rw [Real.volume_Ioc]; exact ENNReal.ofReal_le_ofReal (by linarith)
          · calc _ ≤ ∑ b ∈ G, volume ((fun s => s + (-tst)) ⁻¹'
                  proxSet tk w ((1.9 : ℝ) ^ k) b tst) := measure_biUnion_finset_le _ _
              _ = ∑ b ∈ G, volume (proxSet tk w ((1.9 : ℝ) ^ k) b tst) :=
                  Finset.sum_congr rfl fun b _ => measure_preimage_add_right volume (-tst) _
              _ ≤ ∑ _b ∈ G, ENNReal.ofReal ((3.9 : ℝ) ^ k) :=
                  Finset.sum_le_sum fun b hb => (hprox b hb).le
              _ = ENNReal.ofReal (G.card * (3.9 : ℝ) ^ k) := by
                  rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
                    ENNReal.ofReal_natCast]
  have hsub : U1 ∩ U2 ⊆ relaxedTimes β w ∩ Icc (t - tk) t := by
    intro s hs
    exact ⟨eight_step6 hd ht1 ht4 hβ hβt hT hw htj htau htk hCI hs.1 hs.2, heavyU1_subset hs.1⟩
  have hmain : ENNReal.ofReal ((9 / 10 + 1 / (heavyLevelPrime d t₀ n : ℝ)) * tk) ≤
      volume (relaxedTimes β w ∩ Icc (t - tk) t) +
        ENNReal.ofReal (2 + G.card * (3.9 : ℝ) ^ k) := by
    calc ENNReal.ofReal ((9 / 10 + 1 / (heavyLevelPrime d t₀ n : ℝ)) * tk) ≤ volume R := hrel
      _ = volume R' := hR'vol.symm
      _ ≤ volume (U1 ∪ Ico tst (t - tk)) := measure_mono hR'sub
      _ ≤ volume U1 + volume (Ico tst (t - tk)) := measure_union_le _ _
      _ ≤ volume ((U1 ∩ U2) ∪ (P \ U2)) + ENNReal.ofReal 1 := by
          gcongr
      _ ≤ (volume (U1 ∩ U2) + volume (P \ U2)) + ENNReal.ofReal 1 := by
          gcongr; exact measure_union_le _ _
      _ ≤ (volume (relaxedTimes β w ∩ Icc (t - tk) t) + (ENNReal.ofReal 1 +
            ENNReal.ofReal (G.card * (3.9 : ℝ) ^ k))) + ENNReal.ofReal 1 := by
          gcongr
      _ = volume (relaxedTimes β w ∩ Icc (t - tk) t) +
            ENNReal.ofReal (2 + G.card * (3.9 : ℝ) ^ k) := by
          have hb0 : (0 : ℝ) ≤ G.card * (3.9 : ℝ) ^ k := by positivity
          have e : ENNReal.ofReal 1 + ENNReal.ofReal (G.card * (3.9 : ℝ) ^ k) + ENNReal.ofReal 1 =
              ENNReal.ofReal (2 + G.card * (3.9 : ℝ) ^ k) := by
            rw [← ENNReal.ofReal_add (by norm_num) hb0,
              ← ENNReal.ofReal_add (by positivity) (by norm_num)]
            congr 1; ring
          rw [add_assoc, e]
  obtain ⟨he1, he2⟩ := scales_facts_e hd hn0 ht1 ht4 hT
  have hT9 := hT.t9
  have hnpos : (0 : ℝ) < n := by linarith
  have hden : (0 : ℝ) < 8 * indDelta d * n := by positivity
  have hkpos : (0 : ℝ) < (k : ℝ) ^ 4 := by
    have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    positivity
  have hL3 : (G.card : ℝ) * (3.9 : ℝ) ^ k ≤ heavyL d n * (3.9 : ℝ) ^ k :=
    mul_le_mul_of_nonneg_right hGcard (by positivity)
  have hdiv : (4 : ℝ) ^ k / (8 * indDelta d * n * (k : ℝ) ^ 4) <
      tk * (1 / (8 * indDelta d * n)) := by
    have : (4 : ℝ) ^ k / (8 * indDelta d * n * (k : ℝ) ^ 4) =
        ((4 : ℝ) ^ k / (k : ℝ) ^ 4) * (1 / (8 * indDelta d * n)) := by
      field_simp
    rw [this]
    exact mul_lt_mul_of_pos_right hc2 (by positivity)
  have hreal : (9 / 10 + 4 / (n : ℝ)) * tk + (2 + G.card * (3.9 : ℝ) ^ k) ≤
      (9 / 10 + 1 / (heavyLevelPrime d t₀ n : ℝ)) * tk := by
    have h1 : (1 / (8 * indDelta d * n)) * tk ≤ (1 / (heavyLevelPrime d t₀ n : ℝ) - 4 / n) * tk :=
      mul_le_mul_of_nonneg_right he2 (by linarith)
    nlinarith
  have hfin : ENNReal.ofReal ((9 / 10 + 4 / (n : ℝ)) * tk) +
      ENNReal.ofReal (2 + G.card * (3.9 : ℝ) ^ k) ≤
      volume (relaxedTimes β w ∩ Icc (t - tk) t) +
        ENNReal.ofReal (2 + G.card * (3.9 : ℝ) ^ k) := by
    refine le_trans ?_ hmain
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 hfin

end ElboimSly.Paper
