/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Setting2
public import ElboimSly.Paper.Step.Lemma78FarLoc
public import ElboimSly.Paper.Step.Lemma78Geom
public import ElboimSly.Paper.Step.Lemma78FarAux
public import ElboimSly.Paper.Step.Lemma78FarMeasure
public import ElboimSly.Paper.Heavy.Claim69

/-!
# Lemma 7.8, far lemma: the near set

ES22 Lemma 6.8, "Cover of `V`" and "The near set" (ES22 §7): for `t` with
`W₂(t) ∉ E_t`, the set of `s ∈ [t - t'_k, t]` with `d(W₂(s), V) < ρ_k` has measure at most
`2^d L_cov 3.9^k + 1`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {β t₀ q T ρ : ℝ} {u : Fin d → ℤ}
  {W₁ W₂ : ℝ → Fin d → ℤ}

/-- ES22 Lemma 6.8, the near set. `ρ` stands for `ρ_k`. The hypotheses `hcl₁, hcl₂, hmg`
are the consequences of `Ω` (no closing and no merging by time `T`) for the segments, and the
inequalities `hN₂`, `hN₃` are the "`n` large" conditions
`2^{k-1} + 3n³ + 1 + ρ_k ≤ 2^k` and `ρ_k + n^{41} ≤ 1.9^k`. -/
theorem far_near_bound (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    (hβ : 0 < β) (hT : HeavyT d n₀ E n) (hq0 : 0 ≤ q) (hρ : 0 ≤ ρ)
    (hW₁ : IsCyclicPath W₁) (hw₂ : IsCyclicPath fun s => W₂ s - u)
    (hT₁f : ENNReal.ofReal T < pathTfastCube W₁ n)
    (hT₁τ : ENNReal.ofReal T < heavyTauPrime d t₀ n W₁)
    {t : ℝ} (ht : 2 * heavyTkPrime d t₀ n + 4 ≤ t) (htT : t ≤ T)
    (hT₂f : ENNReal.ofReal T < pathTfastCube (fun s => W₂ s - u) n)
    (hTk : heavyTkPrime d t₀ n + 3 ≤ T)
    (hnE : W₂ t ∉ step78Exc d β t₀ n q T u W₁ W₂ t)
    {ι : Fin d → ℤ} (hgood₂ : ¬ BadByTime d β t₀ n (fun s => W₂ s - u) ι t)
    (hwt : W₂ t - u ∈ heavyBlock (heavyLevel d n) ι)
    (hcl₁ : ∀ a ∈ cycIntTimes β, a + heavyTkPrime d t₀ n ≤ T →
      ¬ SegClosed β (heavyTkPrime d t₀ n) W₁ a)
    (hcl₂ : ∀ b ∈ step78CIN β q, b + heavyTkPrime d t₀ n ≤ T →
      ¬ SegClosed β (heavyTkPrime d t₀ n) W₂ b)
    (hmg : ∀ a ∈ cycIntTimes β, ∀ b ∈ step78CIN β q, a + heavyTkPrime d t₀ n ≤ T →
      b + heavyTkPrime d t₀ n ≤ T →
      ¬ Step78CrossMerge β (heavyTkPrime d t₀ n) q W₁ W₂ a b)
    (hN₂ : (2 : ℝ) ^ (heavyLevel d n - 1) + 3 * (n : ℝ) ^ 3 + 1 + ρ ≤ 2 ^ heavyLevel d n)
    (hN₃ : ρ + (n : ℝ) ^ 41 ≤ (1.9 : ℝ) ^ heavyLevel d n) :
    volume {s : ℝ | s ∈ Icc (t - heavyTkPrime d t₀ n) t ∧
        ∃ v ∈ W₁ '' Icc 0 T, ‖W₂ s - v‖ < ρ} ≤
      ENNReal.ofReal (2 ^ d * heavyL d n * (3.9 : ℝ) ^ heavyLevel d n + 1) := by
  classical
  set k := heavyLevel d n with hk
  set tk := heavyTkPrime d t₀ n with htkd
  set B := heavyBlock k ι with hB
  set w₂ : ℝ → Fin d → ℤ := fun s => W₂ s - u with hw₂def
  have hBne : B.Nonempty := heavyBlock_nonempty k ι
  have hn1 : 1 ≤ n := by have := hT.t4; omega
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hW₂ : ∀ s, W₂ s = u + w₂ s := fun s => by simp [hw₂def]
  -- the time `c = t**`
  have hn0r : (0 : ℝ) ≤ tk := by
    obtain ⟨hc1, hc2, -, -⟩ := scales_facts_c (d := d) (n := n) ht1 ht4 hT.t1.2
    linarith
  have hx0 : 0 ≤ q + (t - tk) := by linarith
  set c : ℝ := cycFloor β (q + (t - tk)) - q with hc
  have hcmem : q + c ∈ cycIntTimes β := by
    rw [hc, add_sub_cancel]; exact cycFloor_mem hβ hx0
  have hc_le : c ≤ t - tk := by have := cycFloor_le (β := β) (x := q + (t - tk)) hβ; linarith
  have hc_gt : t - tk - 1 < c := by
    have := lt_cycFloor_add_one (β := β) (x := q + (t - tk)) hβ; linarith
  have hc0 : 0 ≤ c := by
    have h1 : cycFloor β (q + 1) ∈ cycIntTimes β := cycFloor_mem hβ (by linarith)
    have h2 : q < cycFloor β (q + 1) := by
      have := lt_cycFloor_add_one (β := β) (x := q + 1) hβ; linarith
    have h3 : cycFloor β (q + 1) ≤ q + 1 := cycFloor_le hβ
    have h4 := le_cycFloor_of_mem hβ hx0 h1 (by linarith)
    rw [hc]; linarith
  have hcCIN : c ∈ step78CIN β q := ⟨hc0, hcmem⟩
  -- location of `w₂` on `[c, t]`
  set r1 : ℝ := (2 : ℝ) ^ (k - 1) + 3 * (n : ℝ) ^ 3 with hr1
  have hloc : ∀ s ∈ Icc c t, latDist (w₂ s) B ≤ r1 := by
    intro s hs
    have hs0 : 0 ≤ s := hc0.trans hs.1
    have hts_le : cycFloor β (t - tk) ≤ t - tk := cycFloor_le hβ
    by_cases hcs : cycFloor β (t - tk) ≤ s
    · have := far_location hd hβ hT hw₂ (by linarith) (lt_of_le_of_lt
        (ENNReal.ofReal_le_ofReal htT) hT₂f) hgood₂ hwt hcs hs.2
      linarith
    · push Not at hcs
      have hts_mem : cycFloor β (t - tk) ∈ cycIntTimes β := cycFloor_mem hβ (by linarith)
      have hts0 := hts_mem.1
      have hts1 : t - tk < cycFloor β (t - tk) + 1 := lt_cycFloor_add_one hβ
      have h1 := far_location hd hβ hT hw₂ (t := t) (by linarith) (lt_of_le_of_lt
        (ENNReal.ofReal_le_ofReal htT) hT₂f) hgood₂ hwt le_rfl (by linarith)
      have h2 := norm_lt_of_close (n := n) hw₂ (t := T) hn1 hT₂f hs0 hcs.le (by linarith [hs.1])
        (by linarith)
      have h3 := latDist_le_add hBne (w₂ s) (w₂ (cycFloor β (t - tk)))
      rw [norm_sub_rev] at h2
      linarith
  have hr1nn : 0 ≤ r1 := by positivity
  have hN2' : r1 + 1 ≤ 2 ^ k := by linarith
  -- blocks meeting the translate of `B`
  set A2 : Set (Fin d → ℤ) := (fun x => u + x) '' B with hA2
  obtain ⟨hMfin, hMcard⟩ := ncard_meetBlocks_translate_le (d := d) k u ι
  set M : Finset (Fin d → ℤ) := hMfin.toFinset with hM
  have hMmem : ∀ ι', ι' ∈ M ↔ ι' ∈ step78MeetBlocks k A2 := fun ι' => hMfin.mem_toFinset
  have hMc : (M.card : ℝ) ≤ 2 ^ d := by
    have : M.card = (step78MeetBlocks k A2).ncard := (Set.ncard_eq_toFinset_card _ hMfin).symm
    exact_mod_cast this ▸ hMcard
  have hctI : c ∈ Icc c t := ⟨le_rfl, by linarith⟩
  -- per-block facts
  have hblock : ∀ ι' ∈ M, ∃ y ∈ B, u + y ∈ heavyBlock k ι' := by
    intro ι' hι'
    obtain ⟨x, ⟨y, hy, rfl⟩, hx⟩ := (hMmem ι').1 hι'
    exact ⟨y, hy, hx⟩
  have hgoodblk : ∀ ι' ∈ M, ι' ∉ step78BadBlocks d β t₀ n q T W₁ W₂ t := by
    intro ι' hι' hbad
    obtain ⟨y, hy, hx⟩ := hblock ι' hι'
    apply hnE
    left
    have h1 : latDist (W₂ t) (heavyBlock k ι') ≤ ‖W₂ t - (u + y)‖ :=
      latDist_le_norm_of_mem hx _
    have h2 : ‖W₂ t - (u + y)‖ < 2 ^ k := by
      have := Heavy.norm_sub_lt_of_mem_heavyBlock hwt hy
      have e : W₂ t - (u + y) = W₂ t - u - y := by abel
      rw [e]; exact this
    simp only [mem_iUnion]
    refine ⟨ι', hbad, ?_⟩
    show latDist (W₂ t) _ ≤ _
    have : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hW2c : ∀ ι' ∈ M, latDist (W₂ c) (heavyBlock k ι') ≤ 2 ^ (k + 2) := by
    intro ι' hι'
    obtain ⟨y, hy, hx⟩ := hblock ι' hι'
    obtain ⟨a0, ha0, hn0'⟩ := exists_close_of_latDist_le hBne hr1nn (hloc c hctI)
    have h1 : latDist (W₂ c) (heavyBlock k ι') ≤ ‖W₂ c - (u + y)‖ :=
      latDist_le_norm_of_mem hx _
    have h2 : ‖W₂ c - (u + y)‖ ≤ ‖w₂ c - a0‖ + ‖a0 - y‖ := by
      have e : W₂ c - (u + y) = (w₂ c - a0) + (a0 - y) := by simp only [hw₂def]; abel
      rw [e]; exact norm_add_le _ _
    have h3 : ‖a0 - y‖ < 2 ^ k := Heavy.norm_sub_lt_of_mem_heavyBlock ha0 hy
    have : (2 : ℝ) ^ (k + 2) = 4 * 2 ^ k := by ring
    have : (0 : ℝ) < 2 ^ k := by positivity
    nlinarith
  have hex : ∀ ι' ∈ M, ∃ G : Finset ℝ, (G.card : ℝ) ≤ heavyL d n ∧
      (∀ b ∈ G, b ∈ cycIntTimes β ∧ b + tk ≤ T - 2 ∧
        latDist (W₁ b) (heavyBlock k ι') ≤ 2 ^ (k + 1)) ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ T → W₁ s ∈ latNbhd (heavyBlock k ι') (2 ^ k) →
        ∃ b ∈ G, ∃ u' ∈ Icc (0 : ℝ) tk, ‖W₁ s - W₁ (b + u')‖ ≤ (n : ℝ) ^ 41 := by
    intro ι' hι'
    exact claim69 hd hn0 ht1 ht4 hβ hT hW₁ hTk hT₁f hT₁τ (fun hb => hgoodblk ι' hι' (Or.inl hb))
  choose! G hG using hex
  -- the cross proximity sets
  set X : (Fin d → ℤ) → ℝ → Set ℝ := fun _ b => step78CrossProx tk ((1.9 : ℝ) ^ k) W₁ W₂ b c
    with hX
  have hXvol : ∀ ι' ∈ M, ∀ b ∈ G ι', volume (X ι' b) ≤ ENNReal.ofReal ((3.9 : ℝ) ^ k) := by
    intro ι' hι' b hb
    by_contra hne
    push Not at hne
    obtain ⟨hbi, hbT, hbd⟩ := (hG ι' hι').2.1 b hb
    have hcb : Step78CrossBad d β t₀ n q T W₁ W₂ ι' t := by
      unfold Step78CrossBad
      refine ⟨b, hbi, c, hcCIN, by linarith, by linarith, ?_, ?_, ?_, ?_, ?_, hne.le⟩
      · show latDist _ _ ≤ _
        exact hbd.trans (pow_le_pow_right₀ (by norm_num) (by omega))
      · exact hW2c ι' hι'
      · exact hcl₁ b hbi (by linarith)
      · exact hcl₂ c hcCIN (by linarith)
      · exact hmg b hbi c hcCIN (by linarith) (by linarith)
    exact hgoodblk ι' hι' (Or.inr hcb)
  set Nr : Set ℝ := {s : ℝ | s ∈ Icc (t - tk) t ∧ ∃ v ∈ W₁ '' Icc 0 T, ‖W₂ s - v‖ < ρ} with hNr
  have hcov : ∀ s ∈ Nr ∩ Icc c (c + tk), ∃ ι' ∈ M, ∃ b ∈ G ι', s - c ∈ X ι' b := by
    rintro s ⟨⟨hsI, v, ⟨s1, hs1, rfl⟩, hv⟩, hsc⟩
    have hsct : s ∈ Icc c t := ⟨hsc.1, hsI.2⟩
    obtain ⟨a, ha, han⟩ := exists_close_of_latDist_le hBne hr1nn (hloc s hsct)
    set p : Fin d → ℤ := u + a with hp
    have hpmem : heavyBlockIdx k p ∈ M :=
      (hMmem _).2 ⟨p, ⟨a, ha, rfl⟩, mem_heavyBlock_idx k p⟩
    have h1 : ‖W₂ s - p‖ = ‖w₂ s - a‖ := by
      congr 1; simp only [hp, hw₂def]; abel
    have h2 : ‖W₁ s1 - p‖ ≤ ‖W₁ s1 - W₂ s‖ + ‖W₂ s - p‖ := by
      have e : W₁ s1 - p = (W₁ s1 - W₂ s) + (W₂ s - p) := by abel
      rw [e]; exact norm_add_le _ _
    have h3 : ‖W₁ s1 - W₂ s‖ < ρ := by rw [norm_sub_rev]; exact hv
    have hlat : W₁ s1 ∈ latNbhd (heavyBlock k (heavyBlockIdx k p)) (2 ^ k) := by
      show latDist _ _ ≤ _
      refine (latDist_le_norm_of_mem (mem_heavyBlock_idx k p) _).trans ?_
      linarith
    obtain ⟨b, hb, u', hu', hn⟩ := (hG _ hpmem).2.2 s1 hs1.1 hs1.2 hlat
    refine ⟨_, hpmem, b, hb, ⟨⟨by linarith [hsc.1], by linarith [hsc.2]⟩, u', hu', ?_⟩⟩
    rw [show c + (s - c) = s by ring]
    have e : W₁ (b + u') - W₂ s = (W₁ (b + u') - W₁ s1) + (W₁ s1 - W₂ s) := by abel
    have : ‖W₁ (b + u') - W₂ s‖ ≤ ‖W₁ (b + u') - W₁ s1‖ + ‖W₁ s1 - W₂ s‖ := by
      rw [e]; exact norm_add_le _ _
    rw [norm_sub_rev (W₁ (b + u')) (W₁ s1)] at this
    linarith
  have hg : (0 : ℝ) ≤ (3.9 : ℝ) ^ k := by positivity
  have hL0 : (0 : ℝ) ≤ heavyL d n := by unfold heavyL; positivity
  have hmain := measure_near_le (S := Nr) (c := c) (tk := tk) (t := t) M G X hg hL0
    (fun ι' hι' => (hG ι' hι').1) hcov hXvol
    (fun s hs => ⟨by linarith [hs.1.1], hs.1.2⟩) (by linarith)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have : (M.card : ℝ) * heavyL d n * (3.9 : ℝ) ^ k ≤ 2 ^ d * heavyL d n * (3.9 : ℝ) ^ k := by
    gcongr
  linarith

end ElboimSly.Paper.Step

end
