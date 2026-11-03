/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Claim69Aux
public import ElboimSly.Paper.Heavy.Es6FourMain

/-!
# Claim 6.9

ES22 Claim 6.9 (§6; deviations F11, F58).

Let `t'_k + 3 ≤ t_* < τ_fast ∧ τ'` and let `B ∈ ℬ_k` be good at time `t_*`.  Then there is a finite
set `G` of at most `L_cov = 3^{d+2} n^{γ+9}` cyclic integer times `b` with `b + t'_k ≤ t_* - 2` and
`d(w(b), B) ≤ 2^{k+1}` such that every `w(s)`, `s ≤ t_*`, in `N(B, 2^k)` is within `n^41` of
`w(b + u)` for some `b ∈ G`, `u ∈ [0, t'_k]`.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {β t₀ : ℝ} {w : ℝ → Fin d → ℤ} {ι : Fin d → ℤ}

/-- The grid point attached to a sub-block, an entrance index and a grid step. -/
noncomputable def claim69Pt (d : ℕ) (β t₀ : ℝ) (n : ℕ) (w : ℝ → Fin d → ℤ) (ι : Fin d → ℤ)
    (p : (Fin d → ℤ) × ℕ × ℕ) : ℝ :=
  cycFloor β ((heavyEntSeq w (heavyScaleJ n) (heavyLevel d n) ((heavyD n (heavyLevel d n) : ℕ) : ℝ≥0∞)
      (ι + p.1) p.2.1).toReal + p.2.2 * (heavyTkPrime d t₀ n - 1))

/-- Claim 6.9, the tail segment: the last cyclic integer time `b₀ ≤ t_* - t'_k - 2`. -/
theorem claim69_tail (hd : 5 ≤ d) (hβ : 0 < β) (hT : HeavyT d n₀ E n) (hw : IsCyclicPath w)
    {t_st : ℝ} (ht0 : 0 ≤ t_st) (hts : heavyTkPrime d t₀ n + 3 ≤ t_st)
    (htf : ENNReal.ofReal t_st < pathTfastCube w n)
    (hgood : ¬ BadByTime d β t₀ n w ι t_st) {s : ℝ}
    (hs : cycFloor β (t_st - heavyTkPrime d t₀ n - 2) ≤ s) (hst : s ≤ t_st)
    (hsN : latDist (w s) (heavyBlock (heavyLevel d n) ι) ≤ 2 ^ heavyLevel d n)
    (htk2 : 0 ≤ heavyTkPrime d t₀ n) :
    latDist (w (cycFloor β (t_st - heavyTkPrime d t₀ n - 2))) (heavyBlock (heavyLevel d n) ι) ≤
        2 ^ (heavyLevel d n + 1) ∧
      ∃ u ∈ Icc (0 : ℝ) (heavyTkPrime d t₀ n),
        ‖w s - w (cycFloor β (t_st - heavyTkPrime d t₀ n - 2) + u)‖ ≤ (n : ℝ) ^ 41 := by
  set k := heavyLevel d n with hk
  set tk := heavyTkPrime d t₀ n with htk
  set b0 := cycFloor β (t_st - tk - 2) with hb0
  have hn4 : 4 ≤ n := hT.t4
  have hn1 : 1 ≤ n := by omega
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hpos : 0 ≤ t_st - tk - 2 := by linarith
  have hb0CI : b0 ∈ cycIntTimes β := cycFloor_mem hβ hpos
  have hb0le : b0 ≤ t_st - tk - 2 := cycFloor_le hβ
  have hb0gt : t_st - tk - 2 < b0 + 1 := lt_cycFloor_add_one hβ
  have hn3 : (3 : ℝ) * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 41 := by
    have h1 : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 41 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h2 : (3 : ℝ) * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
      have : (n : ℝ) ^ 4 = (n : ℝ) * (n : ℝ) ^ 3 := by ring
      rw [this]; have : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
      nlinarith
    linarith
  have hn41 : (0 : ℝ) ≤ (n : ℝ) ^ 41 := by positivity
  rcases le_or_gt s (b0 + tk) with h1 | h1
  · have hy : s ≤ min (b0 + tk) t_st := le_min h1 hst
    have key := nofast_b (n₀ := n₀) (E := E) hd hβ hT hw ht0 htf hgood hb0CI hs hy
      (by linarith)
    refine ⟨key, s - b0, ⟨by linarith, by linarith⟩, ?_⟩
    simp
  · set y := b0 + tk with hy
    have hy0 : 0 ≤ y := by linarith [hb0CI.1]
    have hysg : y < s := h1
    have hL : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
    have hlt := norm_sub_lt_of_lt_pathTfast hw hL hy0 hysg
      (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) htf)
    have hceil : ⌈s - y⌉₊ ≤ 3 := Nat.ceil_le.2 (by push_cast; linarith)
    have hlt3 : ‖w s - w y‖ < 3 * (n : ℝ) ^ 3 := by
      calc ‖w s - w y‖ < (n : ℝ) ^ 3 * ⌈s - y⌉₊ := hlt
        _ ≤ (n : ℝ) ^ 3 * 3 := by gcongr; exact_mod_cast hceil
        _ = _ := by ring
    have hyB : latDist (w y) (heavyBlock k ι) ≤ 2 ^ k + (n : ℝ) ^ 41 := by
      have := latDist_le_add (heavyBlock_nonempty k ι) (w y) (w s)
      rw [norm_sub_rev] at this
      linarith
    have hyin : y ≤ min (b0 + tk) t_st := le_min le_rfl (by linarith)
    have key := nofast_b (n₀ := n₀) (E := E) hd hβ hT hw ht0 htf hgood hb0CI
      (by linarith : b0 ≤ y) hyin hyB
    refine ⟨key, tk, ⟨htk2, le_rfl⟩, ?_⟩
    linarith

theorem heavyTrials_le (d : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (heavyTrials d n : ℝ) ≤ 2 * (n : ℝ) ^ (escGamma d + 3) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : 3 ≤ escGamma d := le_max_left _ _
  have hnγ : (1 : ℝ) ≤ (n : ℝ) ^ (escGamma d + 3) := Real.one_le_rpow hn1 (by linarith)
  have := (Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ (escGamma d + 3) by positivity)).le
  unfold heavyTrials
  linarith

/-- ES22 Claim 6.9. -/
theorem claim69 (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hβ : 0 < β)
    (hT : HeavyT d n₀ E n) (hw : IsCyclicPath w) {t_st : ℝ}
    (hts : heavyTkPrime d t₀ n + 3 ≤ t_st) (htf : ENNReal.ofReal t_st < pathTfastCube w n)
    (htau : ENNReal.ofReal t_st < heavyTauPrime d t₀ n w)
    (hgood : ¬ BadByTime d β t₀ n w ι t_st) :
    ∃ G : Finset ℝ, (G.card : ℝ) ≤ heavyL d n ∧
      (∀ b ∈ G, b ∈ cycIntTimes β ∧ b + heavyTkPrime d t₀ n ≤ t_st - 2 ∧
        latDist (w b) (heavyBlock (heavyLevel d n) ι) ≤ 2 ^ (heavyLevel d n + 1)) ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ t_st → w s ∈ latNbhd (heavyBlock (heavyLevel d n) ι) (2 ^ heavyLevel d n) →
        ∃ b ∈ G, ∃ u ∈ Icc (0 : ℝ) (heavyTkPrime d t₀ n),
          ‖w s - w (b + u)‖ ≤ (n : ℝ) ^ 41 := by
  classical
  set k := heavyLevel d n with hk
  set tk := heavyTkPrime d t₀ n with htk
  set B := heavyBlock k ι with hB
  set j := heavyScaleJ n with hj
  have hBne : B.Nonempty := heavyBlock_nonempty k ι
  have hn4 : 4 ≤ n := hT.t4
  have hn1 : 1 ≤ n := by omega
  have hk16 : 16 ≤ k := hT.t1.2
  obtain ⟨hfa, -, -⟩ : (heavyKappa d n ≤ heavyLevelPrime d t₀ n ∧
      heavyLevelPrime d t₀ n ≤ heavyLevel d n - 2) ∧ (n₀ ≤ heavyLevelPrime d t₀ n ∧
      heavyLevelPrime d t₀ n < heavyLevel d n ∧ heavyLevel d n + 1 < n) ∧
      10 ≤ heavyLevelPrime d t₀ n := scales_facts_a hd hn0 ht1 ht4 hT
  obtain ⟨-, ⟨-, -, hkn⟩, -⟩ := scales_facts_a hd hn0 ht1 ht4 hT
  obtain ⟨hjk0, hm0k⟩ := scales_facts_b hd ht1 ht4 hT
  obtain ⟨hc1, hc2, -, -⟩ := scales_facts_c (d := d) (n := n) ht1 ht4 hk16
  have htk2 : 2 < tk := by linarith
  have ht0 : 0 ≤ t_st := by linarith
  have hjk : j ≤ k := hjk0.trans hm0k
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hn41 : (2 : ℝ) * (n : ℝ) ^ 20 ≤ (n : ℝ) ^ 41 := by
    have h1 : (n : ℝ) ^ 21 ≤ (n : ℝ) ^ 41 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h2 : (2 : ℝ) * (n : ℝ) ^ 20 ≤ (n : ℝ) ^ 21 := by
      have : (n : ℝ) ^ 21 = (n : ℝ) * (n : ℝ) ^ 20 := by ring
      rw [this]; have : (0 : ℝ) ≤ (n : ℝ) ^ 20 := by positivity
      nlinarith
    linarith
  have h2j : (2 : ℝ) ^ j < (n : ℝ) ^ 41 := by
    have := (heavyScaleJ_spec (by omega : 2 ≤ n)).2
    have h : (2 : ℝ) ^ j < 2 * (n : ℝ) ^ 20 := by exact_mod_cast this
    linarith
  set Dn : ℕ := heavyD n k with hDn
  have hDR : (Dn : ℝ) = (n : ℝ) ^ 2 * 4 ^ k := by simp [hDn, heavyD]
  have hknR : (k : ℝ) ≤ n := by
    have : k ≤ n := by omega
    exact_mod_cast this
  have hratio : (Dn : ℝ) / (tk - 1) ≤ 2 * (n : ℝ) ^ 6 := by
    have hk4 : (k : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 := by
      apply pow_le_pow_left₀ (by positivity) hknR
    have hkpos : (0 : ℝ) < (k : ℝ) ^ 4 := by
      have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      positivity
    have h4 : (4 : ℝ) ^ k < tk * (k : ℝ) ^ 4 := (div_lt_iff₀ hkpos).1 hc2
    rw [div_le_iff₀ (by linarith)]
    rw [hDR]
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have h5 : (n : ℝ) ^ 2 * 4 ^ k ≤ (n : ℝ) ^ 2 * (tk * (n : ℝ) ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ hn2.le
      nlinarith
    have h6 : (n : ℝ) ^ 2 * (tk * (n : ℝ) ^ 4) = (n : ℝ) ^ 6 * tk := by ring
    have h7 : (0 : ℝ) < (n : ℝ) ^ 6 := by positivity
    nlinarith
  set Z : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ : Fin d => ({-1, 0, 1} : Finset ℤ)) with hZ
  set K := heavyTrials d n with hK
  set M : ℕ := 2 * n ^ 6 with hM
  set I : Finset ((Fin d → ℤ) × ℕ × ℕ) := Z ×ˢ (Finset.range K ×ˢ Finset.range (M + 1)) with hI
  set pt := claim69Pt d β t₀ n w ι with hpt
  set b0 := cycFloor β (t_st - tk - 2) with hb0
  have hpos0 : 0 ≤ t_st - tk - 2 := by linarith
  have hb0CI : b0 ∈ cycIntTimes β := cycFloor_mem hβ hpos0
  have hb0le : b0 ≤ t_st - tk - 2 := cycFloor_le hβ
  let Valid : (Fin d → ℤ) × ℕ × ℕ → Prop := fun p =>
    pt p + tk ≤ t_st - 2 ∧ latDist (w (pt p)) B ≤ 2 ^ (k + 1)
  let G : Finset ℝ := (I.filter Valid).image pt ∪ (if latDist (w b0) B ≤ 2 ^ (k + 1) then {b0} else ∅)
  refine ⟨G, ?_, ?_, ?_⟩
  · -- cardinality
    have h1 : G.card ≤ I.card + 1 := by
      calc G.card ≤ ((I.filter Valid).image pt).card +
            (if latDist (w b0) B ≤ 2 ^ (k + 1) then ({b0} : Finset ℝ) else ∅).card :=
            Finset.card_union_le _ _
        _ ≤ I.card + 1 := by
          gcongr
          · exact Finset.card_image_le.trans (Finset.card_filter_le _ _)
          · split_ifs <;> simp
    have hIc : I.card = 3 ^ d * (K * (M + 1)) := by
      rw [hI, Finset.card_product, Finset.card_product, Finset.card_range, Finset.card_range, hZ,
        Fintype.card_piFinset]
      simp
    have hXpos : (1 : ℝ) ≤ (n : ℝ) ^ (escGamma d + 3) :=
      Real.one_le_rpow (by exact_mod_cast hn1) (by have : 3 ≤ escGamma d := le_max_left _ _; linarith)
    have hKR := heavyTrials_le d hn1
    have hn6 : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ (by exact_mod_cast hn1)
    have hexp : (n : ℝ) ^ (escGamma d + 9) = (n : ℝ) ^ (escGamma d + 3) * (n : ℝ) ^ 6 := by
      rw [show escGamma d + 9 = (escGamma d + 3) + (6 : ℕ) by push_cast; ring, Real.rpow_add (by positivity),
        Real.rpow_natCast]
    have h3d : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
    have hMR : ((M + 1 : ℕ) : ℝ) ≤ 3 * (n : ℝ) ^ 6 := by
      push_cast [hM]; nlinarith
    have hcast : ((I.card + 1 : ℕ) : ℝ) = 3 ^ d * ((K : ℝ) * ((M + 1 : ℕ) : ℝ)) + 1 := by
      rw [hIc]; push_cast; ring
    unfold heavyL
    rw [hexp]
    calc (G.card : ℝ) ≤ ((I.card + 1 : ℕ) : ℝ) := by exact_mod_cast h1
      _ = 3 ^ d * ((K : ℝ) * ((M + 1 : ℕ) : ℝ)) + 1 := hcast
      _ ≤ 3 ^ d * ((2 * (n : ℝ) ^ (escGamma d + 3)) * (3 * (n : ℝ) ^ 6)) + 1 := by
          gcongr
      _ ≤ 3 ^ (d + 2) * ((n : ℝ) ^ (escGamma d + 3) * (n : ℝ) ^ 6) := by
          have hp : (1 : ℝ) ≤ (n : ℝ) ^ (escGamma d + 3) * (n : ℝ) ^ 6 := by nlinarith
          have : (3 : ℝ) ^ (d + 2) = 3 ^ d * 9 := by ring
          rw [this]
          nlinarith
  · -- properties of elements
    intro b hb
    rcases Finset.mem_union.1 hb with hb | hb
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hb
      obtain ⟨-, hV1, hV2⟩ := Finset.mem_filter.1 hp
      refine ⟨cycFloor_mem hβ ?_, hV1, hV2⟩
      have ha : 0 ≤ (heavyEntSeq w j k (Dn : ℝ≥0∞) (ι + p.1) p.2.1).toReal := ENNReal.toReal_nonneg
      have : 0 ≤ (p.2.2 : ℝ) * (tk - 1) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
      show 0 ≤ (heavyEntSeq w j k (Dn : ℝ≥0∞) (ι + p.1) p.2.1).toReal + p.2.2 * (tk - 1)
      linarith
    · by_cases hc : latDist (w b0) B ≤ 2 ^ (k + 1)
      · rw [ite_eq_left hc, Finset.mem_singleton] at hb
        subst hb
        exact ⟨hb0CI, by linarith, hc⟩
      · rw [ite_eq_right hc] at hb; simp at hb
  · -- covering
    intro s hs0 hst hsN
    have hsN' : latDist (w s) B ≤ 2 ^ k := hsN
    rcases le_or_gt b0 s with hb0s | hsb0
    · obtain ⟨hd0, u, hu, hnorm⟩ := claim69_tail (n₀ := n₀) (E := E) hd hβ hT hw ht0 hts htf hgood
        hb0s hst hsN' (by linarith)
      refine ⟨b0, Finset.mem_union_right _ ?_, u, hu, hnorm⟩
      rw [ite_eq_left hd0]; exact Finset.mem_singleton_self _
    · have hex : ∃ b ∈ B, ‖w s - b‖ ≤ (2 : ℝ) ^ k := by
        have : latDist (w s) B ≤ ((2 ^ k : ℕ) : ℝ) := by push_cast; exact hsN'
        obtain ⟨b, hb, hnb⟩ := exists_le_of_latDist_le hBne this
        exact ⟨b, hb, by exact_mod_cast hnb⟩
      obtain ⟨z, hzZ, hsz⟩ := block_near k ι hex
      have hsub : ENNReal.ofReal t_st < heavyEntSeq w j k (Dn : ℝ≥0∞) (ι + z) K := by
        refine lt_of_lt_of_le htau ?_
        unfold heavyTauPrime
        exact iInf₂_le_of_le k hm0k (iInf_le_of_le (ι + z) le_rfl)
      obtain ⟨s'', hs''0, hs''s, ⟨i, hiK, hi1, hi2⟩, hmem⟩ :=
        heavy_entrance_conseq hw hjk hs0 hst hsub hsz
      have hnorm : ‖w s - w s''‖ < (n : ℝ) ^ 41 := by
        have h2 : ‖w s - w s''‖ < (2 : ℝ) ^ j := by
          rw [pi_norm_lt_iff (by positivity)]
          intro c
          have := abs_sub_lt_of_mem_heavyBlock (mem_heavyBlock_idx j (w s)) hmem c
          simp only [Int.norm_eq_abs, Pi.sub_apply]
          exact_mod_cast this
        linarith
      have hsi_top : heavyEntSeq w j k (Dn : ℝ≥0∞) (ι + z) i ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi1
      set a := (heavyEntSeq w j k (Dn : ℝ≥0∞) (ι + z) i).toReal with ha
      have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
      have hale : a ≤ s'' := ENNReal.toReal_le_of_le_ofReal hs''0 hi1
      have hs''lt : s'' < a + (Dn : ℝ) := by
        have h1 : ENNReal.ofReal s'' < ENNReal.ofReal (a + (Dn : ℝ)) := by
          rw [ENNReal.ofReal_add ha0 (by positivity), ha, ENNReal.ofReal_toReal hsi_top,
            ENNReal.ofReal_natCast]
          exact hi2
        exact ((ENNReal.ofReal_lt_ofReal_iff').1 h1).1
      obtain ⟨m, hmle, hc1, hc2⟩ := grid_exists hβ ha0 (by linarith : 1 < tk) hale hs''lt
      have hmM : m ≤ M := by
        have h1 : (m : ℝ) ≤ 2 * (n : ℝ) ^ 6 := hmle.trans hratio
        have : (m : ℝ) ≤ (M : ℝ) := by rw [hM]; push_cast; exact h1
        exact_mod_cast this
      set c := cycFloor β (a + m * (tk - 1)) with hc
      have hcnn : 0 ≤ a + m * (tk - 1) := by
        have : 0 ≤ (m : ℝ) * (tk - 1) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
        linarith
      have hcCI : c ∈ cycIntTimes β := cycFloor_mem hβ hcnn
      have hbtwn : s'' < b0 := lt_of_le_of_lt hs''s hsb0
      have hyB : latDist (w s'') B ≤ 2 ^ k + (n : ℝ) ^ 41 := by
        have := latDist_le_add hBne (w s'') (w s)
        rw [norm_sub_rev] at this
        linarith
      have hyin : s'' ≤ min (c + tk) t_st := le_min hc2.le (hs''s.trans hst)
      have hkey := nofast_b (n₀ := n₀) (E := E) hd hβ hT hw ht0 htf hgood hcCI hc1 hyin hyB
      have hpt : pt (z, i, m) = c := rfl
      have hVal : Valid (z, i, m) := by
        refine ⟨?_, ?_⟩
        · rw [hpt]; linarith
        · rw [hpt]; exact hkey
      have hmemI : (z, i, m) ∈ I := by
        simp only [hI, Finset.mem_product, Finset.mem_range]
        exact ⟨hzZ, hiK, by omega⟩
      refine ⟨c, Finset.mem_union_left _ (Finset.mem_image.2 ⟨(z, i, m),
        Finset.mem_filter.2 ⟨hmemI, hVal⟩, hpt⟩), s'' - c, ⟨by linarith, by linarith⟩, ?_⟩
      rw [show c + (s'' - c) = s'' by ring]
      exact hnorm.le

end ElboimSly.Paper
