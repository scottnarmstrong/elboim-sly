/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Eight4
public import ElboimSly.Paper.Heavy.Occupation
public import ElboimSly.Paper.Heavy.BadMeasMain
public import ElboimSly.Paper.Heavy.BadFinite
public import ElboimSly.Paper.Induction.RelaxedMeasRegen2
public import ElboimSly.Paper.Induction.RelaxedMeasWrt

/-!
# Corollary 6.10, ingredients

ES22 Corollary 6.10 (proof: "The exceptional set" and the measurability of `𝒯(w)`).

* `measurableSet_relaxedTimes_path`: `𝒯(w)` is Lebesgue (Borel) measurable for a cyclic path.
* `heavyBlockFinset_card`: a block of `ℬ_m` has `2^{m d}` vertices.
* `badCount_le_of_lt_tauBad`: before `τ_bad`, `b_t ≤ n`, and `b_t = 0` if `t_n^{5δ} ≤ β`.
* `volume_badUnion_le`: `Leb {s < t : w s ∈ Λ_t} ≤ b_t 2^{dk} β`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d n : ℕ} {β t₀ : ℝ} {w : ℝ → Fin d → ℤ}

/-- A cyclic path is measurable on `[0, ∞)` after clamping. -/
theorem measurable_clamp_of_cyclic (hw : IsCyclicPath w) :
    Measurable fun s : ℝ => w (max s 0) := by
  have hrc : ∀ s : ℝ≥0, ∀ᶠ u in 𝓝[≥] s, (fun r : ℝ≥0 => w r) u = (fun r : ℝ≥0 => w r) s := by
    intro s
    have h := hw.rc (s : ℝ) s.2
    have ht : Tendsto (fun u : ℝ≥0 => (u : ℝ)) (𝓝[≥] s) (𝓝[≥] (s : ℝ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (NNReal.continuous_coe.tendsto s).mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun u hu => by exact_mod_cast hu
    exact ht.eventually h
  have hm : Measurable (fun r : ℝ≥0 => w r) := Base.measurable_of_rc hrc
  have : (fun s : ℝ => w (max s 0)) = (fun r : ℝ≥0 => w r) ∘ (fun s : ℝ => s.toNNReal) := by
    funext s
    simp [Real.coe_toNNReal']
  rw [this]
  exact hm.comp measurable_real_toNNReal

/-- ES22 Corollary 6.10 (measurability of `𝒯(w)`). -/
theorem measurableSet_relaxedTimes_path (hβ : 0 < β) (hw : IsCyclicPath w) :
    MeasurableSet (relaxedTimes β w) := by
  have : Fact (0 < β) := ⟨hβ⟩
  have hW : Measurable fun p : Unit × ℝ => w (max p.2 0) := (measurable_clamp_of_cyclic hw).comp measurable_snd
  have ha : Measurable fun p : Unit × ℝ => (0 : ℝ) := measurable_const
  have hrc : ∀ (_ : Unit) (s : ℝ), ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), w (max s' 0) = w (max s 0) := by
    intro _ s
    by_cases hs : 0 ≤ s
    · obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 (hw.rc s hs)
      refine ⟨u - s, by simpa using hu, fun s' hs' => ?_⟩
      have h1 : s' ∈ Ico s u := ⟨hs'.1, by linarith [hs'.2]⟩
      rw [max_eq_left (hs.trans hs'.1), max_eq_left hs]
      exact hsub h1
    · push Not at hs
      refine ⟨-s, by linarith, fun s' hs' => ?_⟩
      rw [max_eq_right (by linarith [hs'.2] : s' ≤ 0), max_eq_right hs.le]
  have key := measurableSet_isRelaxedTimeWrt (β := β) (d := d) (fun _ s => w (max s 0))
    (fun _ _ => (0 : ℝ)) hW ha hrc
  have hsl : MeasurableSet {s : ℝ | IsRelaxedTimeWrt β (fun s => w (max s 0)) 0 s} :=
    measurable_prodMk_left (x := ()) key
  have e : relaxedTimes β w = Ici 0 ∩ {s : ℝ | IsRelaxedTimeWrt β (fun s => w (max s 0)) 0 s} := by
    ext s
    simp only [relaxedTimes, mem_ofPred_eq, mem_inter_iff, mem_Ici]
    refine and_congr_right fun hs => ?_
    exact ind_isRelaxedTimeWrt_congr (fun s hs => by rw [max_eq_left hs]) le_rfl hs
  rw [e]
  exact measurableSet_Ici.inter hsl

/-- The block as a finset. -/
noncomputable def heavyBlockFinset (m : ℕ) (ι : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun c => Finset.Ico (2 ^ m * ι c) (2 ^ m * ι c + 2 ^ m)

theorem coe_heavyBlockFinset (m : ℕ) (ι : Fin d → ℤ) :
    (heavyBlockFinset m ι : Set (Fin d → ℤ)) = heavyBlock m ι := by
  ext x
  simp only [heavyBlockFinset, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Ico, heavyBlock,
    mem_ofPred_eq]
  have hp : (0 : ℤ) < 2 ^ m := by positivity
  refine forall_congr' fun c => ?_
  constructor
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · have := (Int.ediv_lt_iff_lt_mul hp).2 (by linarith : x c < (ι c + 1) * 2 ^ m)
      omega
    · exact (Int.le_ediv_iff_mul_le hp).2 (by linarith)
  · intro h
    have h1 := (Int.le_ediv_iff_mul_le hp).1 h.ge
    have h2 := (Int.ediv_lt_iff_lt_mul hp).1 (by omega : x c / 2 ^ m < ι c + 1)
    constructor <;> nlinarith

theorem heavyBlockFinset_card (m : ℕ) (ι : Fin d → ℤ) :
    (heavyBlockFinset m ι).card = 2 ^ (m * d) := by
  unfold heavyBlockFinset
  rw [Fintype.card_piFinset]
  simp only [Int.card_Ico]
  have : ∀ c : Fin d, ((2 ^ m * ι c + 2 ^ m - 2 ^ m * ι c : ℤ)).toNat = 2 ^ m := by
    intro c
    have : (2 ^ m * ι c + 2 ^ m - 2 ^ m * ι c : ℤ) = ((2 ^ m : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul]

/-- ES22 Corollary 6.10. Before `τ_bad`, `b_t ≤ n`, and `b_t = 0` if `t_n^{5δ} ≤ β`. -/
theorem badCount_le_of_lt_tauBad (hw : IsCyclicPath w) (hβ : 0 < β)
    (htk : 0 ≤ heavyTkPrime d t₀ n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ENNReal.ofReal t < heavyTauBad d β t₀ n w) :
    badCount d β t₀ n w t ≤ n ∧ (indScale t₀ n ^ (5 * indDelta d) ≤ β → badCount d β t₀ n w t = 0) := by
  unfold heavyTauBad at ht
  by_cases hc : β < indScale t₀ n ^ (5 * indDelta d)
  · rw [ite_eq_left hc] at ht
    have := not_le.2 ht
    rw [heavyBadTime_le_iff hw hβ htk _ ht0] at this
    exact ⟨by omega, fun h => absurd h (not_le.2 hc)⟩
  · rw [ite_eq_right hc] at ht
    have := not_le.2 ht
    rw [heavyBadTime_le_iff hw hβ htk _ ht0] at this
    have h0 : badCount d β t₀ n w t = 0 := by omega
    exact ⟨by omega, fun _ => h0⟩

theorem badUnion_ncard_le (hβ : 0 < β) (htk : 0 ≤ heavyTkPrime d t₀ n) (t : ℝ) :
    (badUnion d β t₀ n w t).Finite ∧
      (badUnion d β t₀ n w t).ncard ≤ badCount d β t₀ n w t * 2 ^ (heavyLevel d n * d) := by
  classical
  have hfin := badSet_finite (w := w) (n := n) (t₀ := t₀) hβ htk t
  have e : badUnion d β t₀ n w t =
      ((hfin.toFinset.biUnion fun ι => heavyBlockFinset (heavyLevel d n) ι : Finset _) :
        Set (Fin d → ℤ)) := by
    ext x
    simp only [badUnion, mem_iUnion, Finset.coe_biUnion, Finite.coe_toFinset, mem_ofPred_eq,
      exists_prop, coe_heavyBlockFinset]
  rw [e]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [Set.ncard_coe_finset]
  calc _ ≤ ∑ ι ∈ hfin.toFinset, (heavyBlockFinset (heavyLevel d n) ι).card := Finset.card_biUnion_le
    _ = badCount d β t₀ n w t * 2 ^ (heavyLevel d n * d) := by
        simp only [heavyBlockFinset_card, Finset.sum_const, smul_eq_mul]
        rw [badCount, Set.ncard_eq_toFinset_card _ hfin]

/-- ES22 Corollary 6.10, "The exceptional set": `Leb {s < t : w s ∈ Λ_t} ≤ b_t 2^{dk} β`. -/
theorem volume_badUnion_le (hw : IsCyclicPath w) (hnr : HasNoReturn β w) (hβ : 0 < β)
    (htk : 0 ≤ heavyTkPrime d t₀ n) {t : ℝ}
    (htT : ENNReal.ofReal t ≤ cycClosingTime β w) :
    volume {s : ℝ | s ∈ Ico 0 t ∧ w s ∈ badUnion d β t₀ n w t} ≤
      ((badCount d β t₀ n w t * 2 ^ (heavyLevel d n * d) : ℕ) : ℝ≥0∞) * ENNReal.ofReal β := by
  obtain ⟨hf, hc⟩ := badUnion_ncard_le (w := w) (n := n) (t₀ := t₀) hβ htk t
  refine (volume_mem_finite_le hβ hw hnr htT hf).trans ?_
  gcongr

end ElboimSly.Paper.Heavy
