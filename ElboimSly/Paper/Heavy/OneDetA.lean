/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Twelve
public import ElboimSly.Paper.Heavy.Cor610Main
public import ElboimSly.Paper.Heavy.Pieces
public import ElboimSly.Paper.Induction.RelaxedMeasRegen2

/-!
# Theorem 6.1, pathwise part: one clean window

Written proof: proof of ES22 Theorem 6.1 (ES22 §6).

* `regen_piece_exists`: for `a ≥ 0` and `k = 𝔑_a`, `σ_k ≤ a < σ_{k+1}`.
* `measurableSet_relaxedTimes_regen`: `𝒯 = {s ≥ 0 : s relaxed}` of the regenerated walk is measurable.
* `clean_window_bound`: if `a ≥ 0`, `h ≤...`, no regeneration time lies in `(a, a + h]`, and the
  current piece is in `Γ_n`, then `|𝒯 ∩ [a, a + h]| ≥ (0.9 + 3/n) h` (from ES22 Corollary 6.10).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {β t₀ : ℝ} [Fact (0 < β)]
  {ν : ℕ → Measure (RingSpace d β)}

theorem regen_piece_exists {a : ℝ} (ha : 0 ≤ a) :
    regenSigma ν (regenCount ν a) ≤ ENNReal.ofReal a ∧
      ENNReal.ofReal a < regenSigma ν (regenCount ν a + 1) :=
  ⟨(le_regenCount_iff ν ha _).1 le_rfl, not_le.1 fun h => absurd ((le_regenCount_iff ν ha _).2 h)
    (by omega)⟩

/-- The relaxed times of the regenerated walk form a measurable set. -/
theorem measurableSet_relaxedTimes_regen (hν : ∀ k, Good (ν k)) :
    MeasurableSet {s : ℝ | 0 ≤ s ∧ IsRelaxedTime ν s} := by
  have h := measurableSet_relaxedTimes (β := β) (Ω := Unit) (fun _ => ν) (fun k => measurable_const)
    (fun _ k => hν k)
  exact measurable_prodMk_left (x := ()) h

/-- Written proof: proof of ES22 Theorem 6.1, a clean window: `|𝒯 ∩ [a, a + h]| ≥ (0.9 + 3/n) h`. -/
theorem clean_window_bound (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    (hβt : β < indScale t₀ n) (hT : HeavyT d n₀ E n) (hν : ∀ k, Good (ν k))
    (hG : heavyGood d β t₀ n ν) {a : ℝ} (ha : 0 ≤ a)
    (hab : a + heavyH d t₀ n ≤ indScale t₀ n)
    (hclean : ∀ i, ¬ (ENNReal.ofReal a < regenSigma ν i ∧
      regenSigma ν i ≤ ENNReal.ofReal (a + heavyH d t₀ n))) :
    ENNReal.ofReal ((9 / 10 + 3 / (n : ℝ)) * heavyH d t₀ n) ≤
      volume ({s : ℝ | 0 ≤ s ∧ IsRelaxedTime ν s} ∩ Icc a (a + heavyH d t₀ n)) := by
  have hβ : 0 < β := Fact.out
  have hε : 0 < heavyEps d := heavyEps_pos (by omega)
  have hh0 : 0 < heavyH d t₀ n := by
    unfold heavyH
    have h1 := indScale_gt_four_pow ht1 n
    exact Real.rpow_pos_of_pos ((by positivity : (0 : ℝ) < 4 ^ n).trans h1) _
  set h := heavyH d t₀ n with hhdef
  set b := a + h with hb
  set k := regenCount ν a with hk
  obtain ⟨hσ1, hσ2⟩ := regen_piece_exists (ν := ν) ha
  rw [← hk] at hσ1 hσ2
  have hσb : ENNReal.ofReal b < regenSigma ν (k + 1) :=
    not_le.1 fun hle => hclean (k + 1) ⟨hσ2, hle⟩
  have hbt : 0 ≤ b := by linarith
  have hkR : k ≤ regenCount ν (indScale t₀ n) :=
    (le_regenCount_iff ν (by unfold indScale; positivity) k).2
      (hσ1.trans (ENNReal.ofReal_le_ofReal (by linarith)))
  have hΓ := hG.2 k hkR
  have hσfin : regenSigma ν k < ⊤ := lt_of_le_of_lt hσ1 ENNReal.ofReal_lt_top
  set σ := (regenSigma ν k).toReal with hσdef
  have hσ0 : 0 ≤ σ := ENNReal.toReal_nonneg
  have hσof : ENNReal.ofReal σ = regenSigma ν k := ENNReal.ofReal_toReal hσfin.ne
  have hσa : σ ≤ a := by
    have := hσof ▸ hσ1
    exact (ENNReal.ofReal_le_ofReal_iff ha).1 this
  set u := b - σ with hu
  have hu0 : 0 ≤ u := by linarith
  have hhu : h ≤ u := by rw [hu, hb]; linarith
  have hut : u ≤ indScale t₀ n := by rw [hu]; linarith
  -- u is below the closing time of the piece
  have hutreg : ENNReal.ofReal u < cycTreg (ν k) := by
    have h1 : ENNReal.ofReal b < regenSigma ν k + cycTreg (ν k) := by
      rw [← regenSigma_succ]; exact hσb
    have h2 : ENNReal.ofReal b = regenSigma ν k + ENNReal.ofReal u := by
      rw [← hσof, ← ENNReal.ofReal_add hσ0 hu0]; congr 1; rw [hu]; ring
    rw [h2] at h1
    exact (ENNReal.add_lt_add_iff_left hσfin.ne).1 h1
  obtain ⟨hcyc, hnr, hclose⟩ := es6_pieces_a hν k
  have hclose' : cycClosingTime β (heavyPiece ν k) = cycTreg (ν k) := hclose
  -- u < τ̌ of the piece
  have hlt : ENNReal.ofReal u < heavyTauCheck d β t₀ n (fun s : ℝ => cycWalk (ν k) 0 0 s) := by
    obtain ⟨-, hΓ2⟩ := hΓ
    have hmin : ENNReal.ofReal u ≤ min (cycClosingTime β (heavyPiece ν k))
        (ENNReal.ofReal (indScale t₀ n)) :=
      le_min (by rw [hclose']; exact hutreg.le) (ENNReal.ofReal_le_ofReal hut)
    have h3 := lt_of_le_of_lt hmin hΓ2
    unfold heavyTauCheck
    simp only [lt_min_iff] at h3 ⊢
    refine ⟨by rw [hclose]; exact hutreg, h3.1, h3.2.1, h3.2.2.1, h3.2.2.2⟩
  have hten := es6_ten hd hn0 ht1 ht4 hβ hβt hT hcyc hnr (t := u) (by
    exact hhu) hlt
  refine hten.trans (le_of_eq ?_)
  -- translate
  have hset : {s : ℝ | 0 ≤ s ∧ IsRelaxedTime ν s} ∩ Icc a b =
      (fun s => s + (-σ)) ⁻¹' (relaxedTimes β (fun s : ℝ => cycWalk (ν k) 0 0 s) ∩ Icc (u - h) u) := by
    ext s
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_preimage, relaxedTimes]
    constructor
    · rintro ⟨⟨hs0, hrel⟩, has, hsb⟩
      have hs1 : regenSigma ν k ≤ ENNReal.ofReal s := by
        rw [← hσof]; exact ENNReal.ofReal_le_ofReal (by linarith)
      have hs2 : ENNReal.ofReal s < regenSigma ν (k + 1) :=
        lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hsb) hσb
      obtain ⟨-, hiff⟩ := es6_pieces_b_relaxed hν hσfin hs0 hs1 hs2
      refine ⟨⟨by linarith, ?_⟩, by rw [hu, hb]; linarith, by rw [hu]; linarith⟩
      have := hiff.1 hrel
      simpa [sub_eq_add_neg] using this
    · rintro ⟨⟨hs0, hrel⟩, h1, h2⟩
      have hs0' : 0 ≤ s := by linarith
      have has : a ≤ s := by rw [hu, hb] at h1; linarith
      have hsb : s ≤ b := by rw [hu] at h2; linarith
      have hs1 : regenSigma ν k ≤ ENNReal.ofReal s := by
        rw [← hσof]; exact ENNReal.ofReal_le_ofReal (by linarith)
      have hs2 : ENNReal.ofReal s < regenSigma ν (k + 1) :=
        lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hsb) hσb
      obtain ⟨-, hiff⟩ := es6_pieces_b_relaxed hν hσfin hs0' hs1 hs2
      exact ⟨⟨hs0', hiff.2 (by simpa [sub_eq_add_neg] using hrel)⟩, has, hsb⟩
  rw [hset, measure_preimage_add_right]

end ElboimSly.Paper.Heavy
