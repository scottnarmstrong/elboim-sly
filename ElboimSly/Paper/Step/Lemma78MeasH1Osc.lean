/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78MeasH1
public import ElboimSly.Paper.Step.Lemma78Setting2
public import Mathlib

/-!
# Measurability of `ℋ₁` (Lemma 7.8), part 2: `Osc₁`, `ℋ₁ ∈ ℱ⁺₀ ⊆ ℱ_{ζ₁}`

The event `Osc₁` of a right-continuous path is detected on the countable set of rational times of
`[0, T]` together with `T` (`step78Osc_iff_rat`), hence is measurable (`measurableSet_step78Osc`).
Together with `measurableSet_tauHat_gt` this gives `ℋ₁ ∈ ℱ⁺₀ = ℱ_{t'_n}` for the first walk of
Lemma 7.8 (`step78_measurableSet_H1`), and then `ℋ₁ ∈ ℱ_σ` for every `(ℱ⁺_t)`-stopping time `σ`
(`step78_measurableSet_H1_stopping`), which is the form of the `hH` premise of
`step78_few_excursions`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {Ω : Type*}

/-- The rational times of `[0, T]`, together with `T`. -/
def measH1Times (T : ℝ≥0) : Set ℝ := {r | 0 ≤ r ∧ r ≤ T ∧ (r = T ∨ ∃ q : ℚ, r = q)}

theorem measH1Times_countable (T : ℝ≥0) : (measH1Times T).Countable :=
  ((Set.countable_singleton (T : ℝ)).union (Set.countable_range (fun q : ℚ => (q : ℝ)))).mono
    (fun _ hr => by
      rcases hr.2.2 with h | ⟨q, hq⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, hq.symm⟩)

theorem measH1_exists_times {w : ℝ → Fin d → ℤ}
    (hw : ∀ s : ℝ, 0 ≤ s → ∀ᶠ u in 𝓝[≥] s, w u = w s) {T : ℝ≥0} {c s s' : ℝ}
    (hs0 : 0 ≤ s) (hss' : s < s') (hs'T : s' ≤ T) (hc : s' - s ≤ c) :
    ∃ r ∈ measH1Times T, ∃ r' ∈ measH1Times T, |r - r'| ≤ c ∧ w r = w s ∧ w r' = w s' := by
  obtain ⟨e1, he1, H1⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hw s hs0)
  obtain ⟨e2, he2, H2⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hw s' (hs0.trans hss'.le))
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (lt_min (mem_Ioi.1 he1) hss')
  have hrs : s < r := hr1
  have hrt : (r : ℝ) < s' := lt_of_lt_of_le hr2 (min_le_right _ _)
  have hwr : w r = w s := H1 ⟨hrs.le, lt_of_lt_of_le hr2 (min_le_left _ _)⟩
  have hrT : (r : ℝ) ∈ measH1Times T :=
    ⟨hs0.trans hrs.le, (hrt.trans_le hs'T).le, Or.inr ⟨r, rfl⟩⟩
  rcases hs'T.eq_or_lt with heq | hlt
  · refine ⟨r, hrT, s', ⟨hs0.trans hss'.le, hs'T, Or.inl heq⟩, ?_, hwr, rfl⟩
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨r', hr'1, hr'2⟩ := exists_rat_btwn
      (show s' < min (min e2 T) (r + c) from
        lt_min (lt_min (mem_Ioi.1 he2) hlt) (by linarith))
    have h2 : (r' : ℝ) < e2 := lt_of_lt_of_le hr'2 ((min_le_left _ _).trans (min_le_left _ _))
    have h3 : (r' : ℝ) < T := lt_of_lt_of_le hr'2 ((min_le_left _ _).trans (min_le_right _ _))
    have h4 : (r' : ℝ) < r + c := lt_of_lt_of_le hr'2 (min_le_right _ _)
    refine ⟨r, hrT, r', ⟨by linarith [hs0.trans hss'.le], h3.le, Or.inr ⟨r', rfl⟩⟩, ?_, hwr,
      H2 ⟨hr'1.le, h2⟩⟩
    rw [abs_le]; constructor <;> linarith

/-- `Osc₁` of a right-continuous path is detected on `measH1Times`. -/
theorem step78Osc_iff_rat {w : ℝ → Fin d → ℤ}
    (hw : ∀ s : ℝ, 0 ≤ s → ∀ᶠ u in 𝓝[≥] s, w u = w s) (T : ℝ≥0) (n : ℕ) :
    Step78Osc n (T : ℝ) w ↔ ∀ r ∈ measH1Times T, ∀ r' ∈ measH1Times T,
      |r - r'| ≤ (3.6 : ℝ) ^ n → ‖w r - w r'‖ ≤ (1.9 : ℝ) ^ n := by
  have hb : (0 : ℝ) ≤ (1.9 : ℝ) ^ n := by positivity
  constructor
  · intro h r hr r' hr' hd
    exact h r ⟨hr.1, hr.2.1⟩ r' ⟨hr'.1, hr'.2.1⟩ hd
  · intro h s hs s' hs' hd
    by_contra hlt
    rw [not_le] at hlt
    have key : ∀ s s' : ℝ, 0 ≤ s → s < s' → s' ≤ T → s' - s ≤ (3.6 : ℝ) ^ n →
        (1.9 : ℝ) ^ n < ‖w s - w s'‖ → False := by
      intro s s' hs0 hss' hs'T hc hl
      obtain ⟨r, hr, r', hr', hd', e1, e2⟩ := measH1_exists_times hw hs0 hss' hs'T hc
      have := h r hr r' hr' hd'
      rw [e1, e2] at this
      linarith
    rcases lt_trichotomy s s' with hss | hss | hss
    · exact key s s' hs.1 hss hs'.2 (by rw [abs_le] at hd; linarith [hd.1]) hlt
    · subst hss; simp at hlt; linarith
    · refine key s' s hs'.1 hss hs.2 (by rw [abs_le] at hd; linarith [hd.2]) ?_
      rwa [norm_sub_rev]

theorem measurableSet_step78Osc {m : MeasurableSpace Ω} {W : Ω → ℝ → Fin d → ℤ}
    (hW : ∀ ω, IsCyclicPath (W ω)) {Tn : ℝ≥0}
    (hmeas : ∀ s : ℝ≥0, s ≤ Tn → Measurable[m] (fun ω => W ω (s : ℝ))) (n : ℕ) :
    MeasurableSet[m] {ω | Step78Osc n (Tn : ℝ) (W ω)} := by
  let : MeasurableSpace Ω := m
  have hat : ∀ r ∈ measH1Times Tn, Measurable fun ω => W ω r := by
    intro r hr
    have := hmeas r.toNNReal (Real.toNNReal_le_iff_le_coe.2 hr.2.1)
    simpa [Real.coe_toNNReal _ hr.1] using this
  have hset : {ω | Step78Osc n (Tn : ℝ) (W ω)} = ⋂ r ∈ measH1Times Tn, ⋂ r' ∈ measH1Times Tn,
      ⋂ (_ : |r - r'| ≤ (3.6 : ℝ) ^ n), {ω | ‖W ω r - W ω r'‖ ≤ (1.9 : ℝ) ^ n} := by
    ext ω
    rw [mem_ofPred_eq, step78Osc_iff_rat (fun s hs => (hW ω).rc s hs)]
    simp only [mem_iInter, mem_ofPred_eq]
  rw [hset]
  refine MeasurableSet.biInter (measH1Times_countable Tn) fun r hr => ?_
  refine MeasurableSet.biInter (measH1Times_countable Tn) fun r' hr' => ?_
  refine MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le ((measurable_of_countable (fun v : Fin d → ℤ => ‖v‖)).comp
    ((hat r hr).sub (hat r' hr'))) measurable_const

/-- `ℋ₁ = {τ̂(W) > T} ∩ Osc₁` is `m`-measurable when `W ω s`, `s ≤ T`, is. -/
theorem measurableSet_step78H1 {m : MeasurableSpace Ω} {W : Ω → ℝ → Fin d → ℤ}
    (hW : ∀ ω, IsCyclicPath (W ω)) {Tn : ℝ≥0}
    (hmeas : ∀ s : ℝ≥0, s ≤ Tn → Measurable[m] (fun ω => W ω (s : ℝ)))
    {β : ℝ} (t₀ : ℝ) {n : ℕ} (hβ : 0 < β) (ht₀ : 0 < t₀) (hn : 1 ≤ n) :
    MeasurableSet[m] {ω | Step78H1 d β t₀ n (Tn : ℝ) (W ω)} :=
  (measurableSet_tauHat_gt hW hmeas t₀ hβ ht₀ hn).inter (measurableSet_step78Osc hW hmeas n)

/-- `ℋ₁ ∈ ℱ_σ` for every stopping time `σ`, as soon as `ℋ₁ ∈ ℱ_0`. -/
theorem measurableSet_stopping_of_zero {ι : Type*} [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [OrderBot ι] {m : MeasurableSpace Ω} {f : Filtration ι m}
    {σ : Ω → WithTop ι} (hσ : IsStoppingTime f σ) {S : Set Ω} (hS : MeasurableSet[f ⊥] S) :
    MeasurableSet[hσ.measurableSpace] S :=
  ⟨le_iSup (fun t => (f t : MeasurableSpace Ω)) ⊥ _ hS, fun i =>
    (f.mono bot_le _ hS).inter (hσ i)⟩

section Adapt

variable {β : ℝ} [Fact (0 < β)] (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0)
  (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N : Ω → Measure (CycS Unit d β)}
  (hN : IsPoissonPointProcess N (cycIntensity Unit d β) Pr) (h𝒢 : 𝒢₀ ≤ mΩ)

omit mΩ in
/-- The first walk `W₁ = W^{N}_{0,0}` is a family of cyclic paths. -/
theorem step78_isCyclicPath_walk1 (ω : Ω) :
    IsCyclicPath (fun s : ℝ => ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) 0 0 s) :=
  isCyclicPath_cycWalk ((cycGood_cycNgood N ω) ())

/-- **`ℋ₁ ∈ ℱ⁺₀`** (setting of Lemma 7.8): `ℋ₁` depends only on `W₁|_{[0, t'_n]}`, which is read off
the truncated record, hence is `ℱ_{t'_n} = ℱ⁺₀`-measurable. -/
theorem step78_measurableSet_H1 {t₀ : ℝ} {n : ℕ} (ht₀ : 0 < t₀) (hn : 1 ≤ n) :
    MeasurableSet[step78Filt u q Tn 𝒢₀ hN h𝒢 0]
      {ω | Step78H1 d β t₀ n (Tn : ℝ)
        (fun s : ℝ => ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) 0 0 s)} := by
  have hβ : 0 < β := Fact.out
  have h := measurableSet_step78H1 (m := cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢
      Pr Tn) (W := fun ω s => ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) 0 0 s)
    (fun ω => step78_isCyclicPath_walk1 (N := N) ω)
    (fun s hs => step78_measurable_walk1 u q Tn 𝒢₀ hN h𝒢 hs) t₀ hβ ht₀ hn
  exact (cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr).mono
    (le_of_eq (add_zero Tn).symm) _ h

/-- **`ℋ₁ ∈ ℱ_σ`** for every `(ℱ⁺_t)`-stopping time `σ`; for `σ = ζ₁` this is the `hH` premise of
`step78_few_excursions`. -/
theorem step78_measurableSet_H1_stopping {t₀ : ℝ} {n : ℕ} (ht₀ : 0 < t₀) (hn : 1 ≤ n)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime (step78Filt u q Tn 𝒢₀ hN h𝒢) σ) :
    MeasurableSet[hσ.measurableSpace]
      {ω | Step78H1 d β t₀ n (Tn : ℝ)
        (fun s : ℝ => ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) 0 0 s)} :=
  measurableSet_stopping_of_zero hσ (step78_measurableSet_H1 u q Tn 𝒢₀ hN h𝒢 ht₀ hn)

end Adapt

end ElboimSly.Paper.Step

end
