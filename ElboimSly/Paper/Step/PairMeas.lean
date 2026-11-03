/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Induction.RelaxedMeasWrt
public import ElboimSly.Paper.Step.ZetaGap
public import ElboimSly.Paper.Step.RelaxedAdapted
public import Mathlib

/-!
# Measurability of the window event `¬ WinOK` for a pair of right-constant paths

Measurability of relaxed times (abstract form), applied to the event of ES22 Theorem 6.1.

For a measurable space `Ω` and families `w : Ω → ℝ≥0 → ℤ^d`, `α : Ω → ℝ≥0 → ℝ` that are measurable
at each time and right-locally constant in time, the event
`{ω | ¬ WinOK T h n {t | 0 ≤ t ∧ IsRelaxedTimeWrt β (stepExt (w ω)) (α ω t.toNNReal) t}}`
is measurable (`measurableSet_not_winOK`). This is what lets an equality in law of the pair
`(W, α)` transfer the probability of the event.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper

/-- Jointly measurable in `(ω, t)` for right-continuous paths. -/
theorem measurable_uncurry_of_rc {Ω V : Type*} [MeasurableSpace Ω] [TopologicalSpace V]
    [MeasurableSpace V] [BorelSpace V] [TopologicalSpace.PseudoMetrizableSpace V]
    (g : Ω → ℝ → V) (hg : ∀ t, Measurable fun ω => g ω t)
    (hrc : ∀ ω t, Tendsto (g ω) (𝓝[≥] t) (𝓝 (g ω t))) :
    Measurable fun p : Ω × ℝ => g p.1 p.2 := by
  let q : ℕ → ℝ → ℝ := fun m t => ((⌊((m : ℝ) + 1) * t⌋ : ℝ) + 1) / ((m : ℝ) + 1)
  have hgn : ∀ m : ℕ, Measurable fun p : Ω × ℝ => g p.1 (q m p.2) := by
    intro m
    have h1 : Measurable fun x : Ω × ℤ => g x.1 (((x.2 : ℝ) + 1) / ((m : ℝ) + 1)) :=
      measurable_from_prod_countable_left (fun k : ℤ => hg (((k : ℝ) + 1) / ((m : ℝ) + 1)))
    have h2 : Measurable fun p : Ω × ℝ => (p.1, ⌊((m : ℝ) + 1) * p.2⌋) :=
      measurable_fst.prodMk (Int.measurable_floor.comp (measurable_const.mul measurable_snd))
    exact h1.comp h2
  refine measurable_of_tendsto_metrizable hgn (tendsto_pi_nhds.2 fun p => ?_)
  have hm : ∀ m : ℕ, (0 : ℝ) < (m : ℝ) + 1 := fun m => by positivity
  have hlo : ∀ m : ℕ, p.2 ≤ q m p.2 := fun m => by
    show p.2 ≤ ((⌊((m : ℝ) + 1) * p.2⌋ : ℝ) + 1) / ((m : ℝ) + 1)
    rw [le_div_iff₀ (hm m)]
    have := Int.lt_floor_add_one (((m : ℝ) + 1) * p.2)
    linarith
  have hhi : ∀ m : ℕ, q m p.2 ≤ p.2 + 1 / ((m : ℝ) + 1) := fun m => by
    show ((⌊((m : ℝ) + 1) * p.2⌋ : ℝ) + 1) / ((m : ℝ) + 1) ≤ _
    have e : p.2 + 1 / ((m : ℝ) + 1) = (((m : ℝ) + 1) * p.2 + 1) / ((m : ℝ) + 1) := by
      field_simp
    rw [e]
    have := Int.floor_le (((m : ℝ) + 1) * p.2)
    exact div_le_div_of_nonneg_right (by linarith) (hm m).le
  have hq : Tendsto (fun m : ℕ => q m p.2) atTop (𝓝[≥] p.2) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hlo⟩
    have h0 : Tendsto (fun m : ℕ => p.2 + 1 / ((m : ℝ) + 1)) atTop (𝓝 p.2) := by
      have := (tendsto_const_nhds (x := p.2)).add tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [add_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 hlo hhi
  exact (hrc p.1 p.2).comp hq

/-- Plateaus of the extension of a right-constant path on `ℝ≥0` to `ℝ`. -/
theorem ext_plateau {V : Type*} {g : ℝ≥0 → V} (hrc : ∀ s, ∀ᶠ u in 𝓝[≥] s, g u = g s) (s : ℝ) :
    ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), g s'.toNNReal = g s.toNNReal := by
  by_cases hs : s < 0
  · refine ⟨-s, by linarith, fun s' hs' => ?_⟩
    rw [Real.toNNReal_of_nonpos (by linarith [hs'.2] : s' ≤ 0), Real.toNNReal_of_nonpos hs.le]
  · push Not at hs
    obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (hrc s.toNNReal)
    have hu : s < (u' : ℝ) := by
      have : (s.toNNReal : ℝ) < u' := by exact_mod_cast hu'
      rwa [Real.coe_toNNReal _ hs] at this
    refine ⟨(u' : ℝ) - s, by linarith, fun s' hs' => ?_⟩
    have hs'0 : 0 ≤ s' := hs.trans hs'.1
    exact hsub ⟨Real.toNNReal_le_toNNReal hs'.1, by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs'0]; linarith [hs'.2]⟩

theorem tendsto_ext_of_rc {V : Type*} [TopologicalSpace V] {g : ℝ≥0 → V}
    (hrc : ∀ s, ∀ᶠ u in 𝓝[≥] s, g u = g s) (s : ℝ) :
    Tendsto (fun r : ℝ => g r.toNNReal) (𝓝[≥] s) (𝓝 (g s.toNNReal)) := by
  obtain ⟨ε, hε, h⟩ := ext_plateau hrc s
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ico_mem_nhdsGE (show s < s + ε by linarith)] with u hu
  exact (h u hu).symm

section Win

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]

/-- Lipschitz bound for the window mass. -/
theorem window_mass_le (S : Set ℝ) (h t t' : ℝ) :
    volume (S ∩ Icc t' (t' + h)) ≤
      volume (S ∩ Icc t (t + h)) + 2 * ENNReal.ofReal |t - t'| := by
  have hsub : S ∩ Icc t' (t' + h) ⊆ (S ∩ Icc t (t + h)) ∪ Ico t' t ∪ Ioc (t + h) (t' + h) := by
    intro x ⟨hxS, hx1, hx2⟩
    by_cases h1 : t ≤ x
    · by_cases h2 : x ≤ t + h
      · exact Or.inl (Or.inl ⟨hxS, h1, h2⟩)
      · exact Or.inr ⟨by linarith, hx2⟩
    · exact Or.inl (Or.inr ⟨hx1, by linarith⟩)
  calc volume (S ∩ Icc t' (t' + h))
      ≤ volume ((S ∩ Icc t (t + h)) ∪ Ico t' t ∪ Ioc (t + h) (t' + h)) := measure_mono hsub
    _ ≤ volume ((S ∩ Icc t (t + h)) ∪ Ico t' t) + volume (Ioc (t + h) (t' + h)) :=
        measure_union_le _ _
    _ ≤ volume (S ∩ Icc t (t + h)) + volume (Ico t' t) + volume (Ioc (t + h) (t' + h)) := by
        gcongr; exact measure_union_le _ _
    _ ≤ volume (S ∩ Icc t (t + h)) + 2 * ENNReal.ofReal |t - t'| := by
        rw [Real.volume_Ico, Real.volume_Ioc]
        have e1 : ENNReal.ofReal (t - t') ≤ ENNReal.ofReal |t - t'| :=
          ENNReal.ofReal_le_ofReal (le_abs_self _)
        have e2 : ENNReal.ofReal (t' + h - (t + h)) ≤ ENNReal.ofReal |t - t'| :=
          ENNReal.ofReal_le_ofReal (by rw [abs_sub_comm]; linarith [le_abs_self (t' - t)])
        rw [two_mul, ← add_assoc]
        gcongr

/-- **Measurability of the window event.** -/
theorem measurableSet_not_winOK (w : Ω → ℝ≥0 → Fin d → ℤ) (α : Ω → ℝ≥0 → ℝ)
    (hw : ∀ t, Measurable fun ω => w ω t) (hα : ∀ t, Measurable fun ω => α ω t)
    (hwr : ∀ ω s, ∀ᶠ u in 𝓝[≥] s, w ω u = w ω s) (hαr : ∀ ω s, ∀ᶠ u in 𝓝[≥] s, α ω u = α ω s)
    (T h : ℝ) (n : ℕ) :
    MeasurableSet {ω | ¬ WinOK T h n
      {t : ℝ | 0 ≤ t ∧ IsRelaxedTimeWrt β (stepExt (w ω)) (α ω t.toNNReal) t}} := by
  classical
  set W : Ω → ℝ → Fin d → ℤ := fun ω r => w ω r.toNNReal with hW
  set A : Ω → ℝ → ℝ := fun ω r => α ω r.toNNReal with hA
  have hWm : Measurable fun p : Ω × ℝ => W p.1 p.2 :=
    measurable_uncurry_of_rc W (fun t => (hw t.toNNReal))
      (fun ω s => tendsto_ext_of_rc (hwr ω) s)
  have hAm : Measurable fun p : Ω × ℝ => A p.1 p.2 :=
    measurable_uncurry_of_rc A (fun t => (hα t.toNNReal))
      (fun ω s => tendsto_ext_of_rc (hαr ω) s)
  have hrc : ∀ ω s, ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), W ω s' = W ω s :=
    fun ω s => ext_plateau (hwr ω) s
  have hS := measurableSet_isRelaxedTimeWrt (β := β) W A hWm hAm hrc
  set S : Set (Ω × ℝ) := {p | 0 ≤ p.2 ∧ IsRelaxedTimeWrt β (W p.1) (A p.1 p.2) p.2} with hSdef
  have hSm : MeasurableSet S := (measurableSet_le measurable_const measurable_snd).inter hS
  set c : ℝ≥0∞ := ENNReal.ofReal ((9 / 10 + 2 / (n : ℝ)) * h) with hc
  have hF : ∀ t : ℝ, Measurable fun ω => volume ({r : ℝ | (ω, r) ∈ S} ∩ Icc t (t + h)) := by
    intro t
    have hm : MeasurableSet {p : Ω × ℝ | p.2 ∈ Icc t (t + h) ∧ p ∈ S} :=
      (measurable_snd measurableSet_Icc).inter hSm
    have := measurable_measure_prodMk_left (ν := (volume : Measure ℝ)) hm
    convert this using 2 with ω
    congr 1
    ext r
    simp [and_comm]
  -- reduce to a countable family of times
  have key : ∀ ω, WinOK T h n {t : ℝ | 0 ≤ t ∧ IsRelaxedTimeWrt β (stepExt (w ω)) (α ω t.toNNReal) t}
      ↔ ∀ q : ℚ, 0 ≤ (q : ℝ) * (T - h) → (q : ℝ) * (T - h) + h ≤ T →
        c ≤ volume ({r : ℝ | (ω, r) ∈ S} ∩ Icc ((q : ℝ) * (T - h)) ((q : ℝ) * (T - h) + h)) := by
    intro ω
    have hset : {t : ℝ | 0 ≤ t ∧ IsRelaxedTimeWrt β (stepExt (w ω)) (α ω t.toNNReal) t} =
        {r : ℝ | (ω, r) ∈ S} := rfl
    rw [hset]
    constructor
    · intro hwin q h1 h2
      exact hwin _ h1 h2
    · intro hq t ht0 htT
      -- density
      rcases eq_or_lt_of_le (sub_nonneg.2 (by linarith : h ≤ T)) with hz | hpos
      · have : t = 0 := by linarith
        subst this
        have := hq 0 (by simp) (by simpa using htT)
        simpa using this
      · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
        have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
        set Δ := T - h with hΔ
        obtain ⟨M, hM⟩ := exists_nat_gt (Δ / (ε / 4 : ℝ))
        have hM0 : (0 : ℝ) < M := lt_of_le_of_lt (by positivity) hM
        have hMΔ : Δ / M < ε / 4 := by
          rw [div_lt_iff₀ hM0]
          rw [div_lt_iff₀ (by positivity)] at hM
          linarith
        set r := t / Δ with hr
        have hr0 : 0 ≤ r := div_nonneg ht0 hpos.le
        have hr1 : r ≤ 1 := by rw [hr, div_le_one hpos]; linarith
        set k : ℤ := ⌊r * M⌋ with hk
        have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast Int.floor_nonneg.2 (by positivity)
        have hkle : (k : ℝ) ≤ r * M := Int.floor_le _
        have hklt : r * M < k + 1 := Int.lt_floor_add_one _
        set q : ℚ := (k : ℚ) / M with hqdef
        have hqR : (q : ℝ) = (k : ℝ) / M := by simp [hqdef]
        have hq0 : 0 ≤ (q : ℝ) := by rw [hqR]; positivity
        have hq1 : (q : ℝ) ≤ r := by
          rw [hqR, div_le_iff₀ hM0]; exact hkle
        set t' : ℝ := (q : ℝ) * Δ with ht'
        have ht'0 : 0 ≤ t' := mul_nonneg hq0 hpos.le
        have ht'1 : t' + h ≤ T := by
          have : t' ≤ Δ := by
            calc t' ≤ r * Δ := mul_le_mul_of_nonneg_right hq1 hpos.le
              _ ≤ 1 * Δ := mul_le_mul_of_nonneg_right hr1 hpos.le
              _ = Δ := one_mul _
          linarith
        have hrt : r * Δ = t := by rw [hr]; field_simp
        have hdiff : |t - t'| < ε / 4 := by
          have h1 : 0 ≤ t - t' := by
            rw [← hrt]; exact (sub_nonneg.2 (mul_le_mul_of_nonneg_right hq1 hpos.le))
          rw [abs_of_nonneg h1]
          have h2 : r - q ≤ 1 / M := by
            rw [hqR]
            have : r < ((k : ℝ) + 1) / M := by rw [lt_div_iff₀ hM0]; exact hklt
            have e : ((k : ℝ) + 1) / M = k / M + 1 / M := by ring
            linarith
          calc t - t' = (r - q) * Δ := by rw [← hrt]; ring
            _ ≤ (1 / M) * Δ := mul_le_mul_of_nonneg_right h2 hpos.le
            _ = Δ / M := by ring
            _ < ε / 4 := hMΔ
        have hqt := hq q ht'0 ht'1
        have hlip := window_mass_le {r : ℝ | (ω, r) ∈ S} h t t'
        have hbd : 2 * ENNReal.ofReal |t - t'| ≤ (ε : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (by linarith)
        calc c ≤ _ := hqt
          _ ≤ _ := hlip
          _ ≤ _ := by gcongr
  have hset : {ω | ¬ WinOK T h n
      {t : ℝ | 0 ≤ t ∧ IsRelaxedTimeWrt β (stepExt (w ω)) (α ω t.toNNReal) t}} =
      ⋃ q : ℚ, ({ω : Ω | 0 ≤ (q : ℝ) * (T - h) ∧ (q : ℝ) * (T - h) + h ≤ T} ∩
        {ω | volume ({r : ℝ | (ω, r) ∈ S} ∩ Icc ((q : ℝ) * (T - h)) ((q : ℝ) * (T - h) + h)) < c}) := by
    ext ω
    simp only [mem_ofPred_eq, key ω, not_forall, mem_iUnion, mem_inter_iff, not_le]
    constructor
    · rintro ⟨q, h1, h2, h3⟩; exact ⟨q, ⟨h1, h2⟩, h3⟩
    · rintro ⟨q, ⟨h1, h2⟩, h3⟩; exact ⟨q, h1, h2, h3⟩
  rw [hset]
  refine MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter ?_
  exact measurableSet_lt (hF _) measurable_const

end Win

end ElboimSly.Paper.Step
