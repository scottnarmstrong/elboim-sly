/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Cor610

/-!
# Corollary 6.10, the statement

ES22 Corollary 6.10 (§6; deviations F12, F59).

Let `h = t_n^{ε/2} ≤ t < τ̌(w)`.  Then `|𝒯(w) ∩ [t - h, t]| ≥ (0.9 + 3/n) h`.

* `volume_badUnion_le_rpow`: the occupation bound for `Λ_t`.
* `es6_ten`: the corollary.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {β t₀ : ℝ} {w : ℝ → Fin d → ℤ}

/-- The occupation bound for `Λ_t`: `Leb {s < t : w s ∈ Λ_t} ≤ n t_n^{3ε/10}`. -/
theorem volume_badUnion_le_rpow (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    (hT : HeavyT d n₀ E n) (hw : IsCyclicPath w) (hnr : HasNoReturn β w) (hβ : 0 < β)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : ENNReal.ofReal t ≤ cycClosingTime β w)
    (htb : ENNReal.ofReal t < heavyTauBad d β t₀ n w) :
    volume {s : ℝ | s ∈ Ico 0 t ∧ w s ∈ badUnion d β t₀ n w t} ≤
      ENNReal.ofReal (n * indScale t₀ n ^ (3 * heavyEps d / 10)) := by
  have hδ := heavy_indDelta_pos (d := d) (by omega)
  have htk : 0 ≤ heavyTkPrime d t₀ n := by
    unfold heavyTkPrime indScale; have : 0 < t₀ := by linarith
    positivity
  refine (volume_badUnion_le hw hnr hβ htk htT).trans ?_
  obtain ⟨hb1, hb2⟩ := badCount_le_of_lt_tauBad hw hβ htk ht0 htb
  by_cases hc : indScale t₀ n ^ (5 * indDelta d) ≤ β
  · rw [hb2 hc]; simp
  · push Not at hc
    obtain ⟨_, _, h3⟩ := scales_facts_d hd ht1 ht4 hT
    have htn1 : (1 : ℝ) ≤ indScale t₀ n :=
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)).trans (indScale_gt_four_pow ht1 n).le
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hdd := indDelta_mul_d (d := d) (by omega)
    have hexp : 2 * indDelta d * d + 5 * indDelta d ≤ 3 * heavyEps d / 10 := by
      have h5 : (5 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith
    have hpow : indScale t₀ n ^ (2 * indDelta d * d) * indScale t₀ n ^ (5 * indDelta d) ≤
        indScale t₀ n ^ (3 * heavyEps d / 10) := by
      rw [← Real.rpow_add (by linarith)]
      exact Real.rpow_le_rpow_of_exponent_le htn1 hexp
    have h2 : (((2 : ℕ) : ℝ) ^ (heavyLevel d n * d)) ≤ indScale t₀ n ^ (2 * indDelta d * d) := by
      rw [mul_comm]; exact_mod_cast h3
    push_cast
    calc ((badCount d β t₀ n w t : ℝ) * 2 ^ (heavyLevel d n * d)) * β
        ≤ (n : ℝ) * indScale t₀ n ^ (2 * indDelta d * d) * indScale t₀ n ^ (5 * indDelta d) := by
          have hb : (badCount d β t₀ n w t : ℝ) ≤ n := by exact_mod_cast hb1
          have hrp : 0 ≤ indScale t₀ n ^ (2 * indDelta d * d) := by positivity
          exact mul_le_mul (mul_le_mul hb h2 (by positivity) (by positivity)) hc.le hβ.le
            (by positivity)
      _ ≤ _ := by rw [mul_assoc]; gcongr

/-- ES22 Corollary 6.10. -/
theorem es6_ten (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hβ : 0 < β)
    (hβt : β < indScale t₀ n) (hT : HeavyT d n₀ E n) (hw : IsCyclicPath w)
    (hnr : HasNoReturn β w) {t : ℝ} (hht : heavyH d t₀ n ≤ t)
    (htc : ENNReal.ofReal t < heavyTauCheck d β t₀ n w) :
    ENNReal.ofReal ((9 / 10 + 3 / (n : ℝ)) * heavyH d t₀ n) ≤
      volume (relaxedTimes β w ∩ Icc (t - heavyH d t₀ n) t) := by
  classical
  have hε := heavyEps_pos (d := d) (by omega)
  have hn4 : 4 ≤ n := hT.t4
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn4r : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hk16 := hT.t1.2
  obtain ⟨hc1, hc2, _, _⟩ := scales_facts_c (d := d) (n := n) ht1 ht4 hk16
  set tk := heavyTkPrime d t₀ n with htkdef
  set tn := indScale t₀ n with htndef
  set h := heavyH d t₀ n with hhdef
  set X := tn ^ (3 * heavyEps d / 10) with hXdef
  have htk2 : 2 ≤ tk := hc1.trans hc2.le
  have htn1 : (1 : ℝ) ≤ tn :=
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)).trans (indScale_gt_four_pow ht1 n).le
  have hX0 : 0 ≤ X := by positivity
  -- numerics from (T10)
  have hS : 2 * n * (3 * tk + 4 + n * X) ≤ h := by
    have hA := tkPrime_le_rpow (d := d) (n := n) (by omega) ht1 ht4 hk16
    have hB := tn_pow_le (d := d) (n := n) (t₀ := t₀) (by omega) ht1 ht4
    have hC := hT.t10.1
    have hH := heavyH_ge (d := d) (n := n) (by omega) ht1
    have : 2 * (n : ℝ) * (3 * tk + 4 + n * X) ≤
        2 * n * (3 * 4 ^ (4 * indDelta d * n + 1) + 4 +
          n * (4 : ℝ) ^ (3 * heavyEps d * (n + 1) / 10)) := by gcongr
    linarith
  have hh0 : 0 < h := by
    have hpos : 0 < 3 * tk + 4 + n * X := by nlinarith [mul_nonneg hnpos.le hX0]
    have : 0 < 2 * (n : ℝ) * (3 * tk + 4 + n * X) := by positivity
    linarith
  have ht0 : 0 ≤ t := hh0.le.trans hht
  simp only [heavyTauCheck, lt_min_iff] at htc
  obtain ⟨htT, htf, htj, htp, htb⟩ := htc
  -- the exceptional set
  set U : Set ℝ := Ico 0 (2 * tk + 4) ∪ {s : ℝ | s ∈ Ico 0 t ∧ w s ∈ badUnion d β t₀ n w t} ∪ {t}
    with hU
  have hLam := volume_badUnion_le_rpow hd ht1 ht4 hT hw hnr hβ ht0 htT.le htb
  have hUvol : volume U ≤ ENNReal.ofReal (2 * tk + 4 + n * X) := by
    calc volume U ≤ volume (Ico 0 (2 * tk + 4) ∪
            {s : ℝ | s ∈ Ico 0 t ∧ w s ∈ badUnion d β t₀ n w t}) + volume ({t} : Set ℝ) :=
          measure_union_le _ _
      _ ≤ (volume (Ico (0 : ℝ) (2 * tk + 4)) +
          volume {s : ℝ | s ∈ Ico 0 t ∧ w s ∈ badUnion d β t₀ n w t}) + 0 := by
          gcongr
          · exact measure_union_le _ _
          · simp
      _ ≤ ENNReal.ofReal (2 * tk + 4) + ENNReal.ofReal (n * X) := by
          rw [add_zero]
          gcongr
          simp
      _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hUm : MeasurableSet U := by
    have hA : MeasurableSet {s : ℝ | s ∈ Ico 0 t ∧ w s ∈ badUnion d β t₀ n w t} := by
      have : {s : ℝ | s ∈ Ico 0 t ∧ w s ∈ badUnion d β t₀ n w t} =
          Ico 0 t ∩ (fun s : ℝ => w (max s 0)) ⁻¹' badUnion d β t₀ n w t := by
        ext s
        simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [max_eq_left h1.1]⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [max_eq_left h1.1] at h2⟩
      rw [this]
      exact measurableSet_Ico.inter (measurable_clamp_of_cyclic hw
        (Set.to_countable _).measurableSet)
    exact (measurableSet_Ico.union hA).union (measurableSet_singleton t)
  -- the good times
  set T := relaxedTimes β w with hTdef
  have hTm : MeasurableSet T := measurableSet_relaxedTimes_path hβ hw
  set a := t - h + tk with hadef
  set G := Icc a t \ U with hGdef
  have hGm : MeasurableSet G := measurableSet_Icc.diff hUm
  set c : ℝ := 9 / 10 + 4 / (n : ℝ) with hcdef
  have hgood : ∀ s ∈ G, ENNReal.ofReal (c * tk) ≤ volume (T ∩ Icc (s - tk) s) := by
    intro s hs
    have hsI : s ∈ Icc a t := hs.1
    have hsU : s ∉ U := hs.2
    have hs0 : 0 ≤ s := by
      have : 0 ≤ a := by rw [hadef]; linarith
      linarith [hsI.1]
    have hs1 : 2 * tk + 4 ≤ s := by
      by_contra hlt; push Not at hlt
      exact hsU (Or.inl (Or.inl ⟨hs0, hlt⟩))
    have hst : s < t := lt_of_le_of_ne hsI.2 (fun e => hsU (Or.inr (by simp [e])))
    have hnot : w s ∉ badUnion d β t₀ n w s := by
      intro hm
      refine hsU (Or.inl (Or.inr ⟨⟨hs0, hst⟩, ?_⟩))
      simp only [badUnion, mem_iUnion, mem_ofPred_eq] at hm ⊢
      obtain ⟨ι, hι, hx⟩ := hm
      exact ⟨ι, hι.mono hst.le, hx⟩
    have hlt : ∀ x : ℝ≥0∞, ENNReal.ofReal t < x → ENNReal.ofReal s < x := fun x hx =>
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst.le) hx
    exact es6_eight hd hn0 ht1 ht4 hβ hβt hT hw hnr hs1 (hlt _ htf) (hlt _ htj) (hlt _ htp)
      (hlt _ htT) hnot
  -- averaging
  have hup := lintegral_window_le hTm (a := a) (b := t) (tk := tk) (by linarith)
  have e1 : a - tk = t - h := by rw [hadef]; ring
  rw [e1] at hup
  have hlow : ENNReal.ofReal (c * tk) * volume G ≤
      ∫⁻ s in Icc a t, volume (T ∩ Icc (s - tk) s) := by
    calc ENNReal.ofReal (c * tk) * volume G = ∫⁻ _ in G, ENNReal.ofReal (c * tk) := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ s in G, volume (T ∩ Icc (s - tk) s) := setLIntegral_mono' hGm hgood
      _ ≤ _ := lintegral_mono_set sdiff_subset
  -- measure of G
  have hGvol : ENNReal.ofReal (h - tk - (2 * tk + 4 + n * X)) ≤ volume G := by
    have h1 : volume (Icc a t) ≤ volume G + volume U := by
      calc volume (Icc a t) ≤ volume (G ∪ U) := measure_mono (fun x hx => by
            by_cases hxU : x ∈ U
            · exact Or.inr hxU
            · exact Or.inl ⟨hx, hxU⟩)
        _ ≤ _ := measure_union_le _ _
    rw [Real.volume_Icc] at h1
    have e2 : t - a = h - tk := by rw [hadef]; ring
    rw [e2] at h1
    have h2 : ENNReal.ofReal (h - tk) ≤ volume G + ENNReal.ofReal (2 * tk + 4 + n * X) :=
      h1.trans (by gcongr)
    rw [ENNReal.ofReal_sub _ (by positivity)]
    exact tsub_le_iff_right.2 h2
  -- conclude
  have hcm : ENNReal.ofReal tk * ENNReal.ofReal (c * (h - tk - (2 * tk + 4 + n * X))) ≤
      ENNReal.ofReal tk * volume (T ∩ Icc (t - h) t) := by
    calc _ = ENNReal.ofReal (c * tk) * ENNReal.ofReal (h - tk - (2 * tk + 4 + n * X)) := by
          have hc0 : 0 ≤ c := by rw [hcdef]; positivity
          rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ tk),
            ← ENNReal.ofReal_mul (mul_nonneg hc0 (by linarith : 0 ≤ tk))]
          congr 1; ring
      _ ≤ ENNReal.ofReal (c * tk) * volume G := by gcongr
      _ ≤ _ := hlow.trans hup
  have hcm' := (ENNReal.mul_le_mul_iff_right (by simpa using (by linarith : 0 < tk))
    ENNReal.ofReal_ne_top).1 hcm
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hcm'
  have hc2 : c ≤ 2 := by
    rw [hcdef]
    have : 4 / (n : ℝ) ≤ 1 := by rw [div_le_one hnpos]; exact hn4r
    linarith
  have hSn : 0 ≤ 3 * tk + 4 + n * X := by positivity
  have hq : 2 * (3 * tk + 4 + n * X) ≤ h / n := by
    rw [le_div_iff₀ hnpos]; linarith
  have key : (9 / 10 + 3 / (n : ℝ)) * h ≤ c * (h - tk - (2 * tk + 4 + n * X)) := by
    have : c * (h - tk - (2 * tk + 4 + n * X)) - (9 / 10 + 3 / (n : ℝ)) * h =
        h / n - c * (3 * tk + 4 + n * X) := by
      rw [hcdef]; field_simp; ring
    nlinarith
  exact key

end ElboimSly.Paper.Heavy
