/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78LawBad
public import ElboimSly.Paper.Step.Lemma78Decomp
public import ElboimSly.Paper.Step.Lemma78TauBound
public import ElboimSly.Paper.Step.Lemma78CountCover
public import ElboimSly.Paper.Step.Lemma78ExcRc
public import ElboimSly.Paper.Step.Lemma78ExcAux
public import ElboimSly.Paper.Step.Lemma78MeasH1Osc
public import Mathlib

/-!
# One excursion succeeds with probability at least `1/2`

One excursion succeeds with probability at least frac12. For `G ∈ ℱ⁺_{ζ_{i+1}}` with `G ⊆ ℋ₁ ∩ {ζ_{i+1} < t'_n}`,
`P(G ∩ {ζ'_{i+1} < t'_n}) ≤ (C_τ β^{-δ/30} + bracket) P(G)`: the pathwise reduction
(`Step78Data.decomp`), the `τ'` bound, and the freezing lemma for the pair `(W₂(ζ), V)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

universe u

/-- The far radius `ρ_k = 1.9^k / 2` of Lemma 7.8. -/
noncomputable def step78Rho (d n : ℕ) : ℝ := (1.9 : ℝ) ^ heavyLevel d n / 2

/-- Fixed constants of §5 for the threshold conditions `HeavyT` (which depend on `E` only through
`N₅`, so any choice works). -/
def step78E0 : HeavyEscConsts := ⟨1, 1, 0, one_pos, one_pos⟩

/-- The bracket of one excursion succeeds with probability at least frac12 without the `τ'` term. -/
noncomputable def step78BracketS (d : ℕ) (C42 β : ℝ) (n : ℕ) (L : ℝ) : ℝ :=
  2 * (β ^ 2)⁻¹ + (C42 * L ^ (-(1 : ℝ) / 30) + (Real.exp (-(((n - 1 : ℕ) : ℝ) ^ 2)) +
    2 * (10 / 9 : ℝ) ^ n * (ElboimSly.Brownian.Cfar d *
      (3 * (19 / 10 : ℝ) ^ n / Real.sqrt ((389 / 100 : ℝ) ^ n)) ^ (d - 2))))

/-- The full bracket of one excursion succeeds with probability at least frac12. -/
noncomputable def step78Bracket (d : ℕ) (Cτ C42 β : ℝ) (n : ℕ) (L : ℝ) : ℝ :=
  Cτ * β ^ (-indDelta d / 30) + step78BracketS d C42 β n L

theorem step78BracketS_nonneg {d : ℕ} {C42 β L : ℝ} (n : ℕ) (hC : 0 ≤ C42) (hβ : 0 < β)
    (hL : 0 ≤ L) : 0 ≤ step78BracketS d C42 β n L := by
  unfold step78BracketS
  have := ElboimSly.Brownian.Cfar_pos d
  positivity

theorem step78_card_le {Tn : ℝ} (_hT0 : 0 ≤ Tn) {n : ℕ} (hT : Tn ≤ (4 : ℝ) ^ n) {c : ℝ}
    (hc : c ≤ Tn / (3.6 : ℝ) ^ n + 1) : c ≤ 2 * (10 / 9 : ℝ) ^ n := by
  have h1 : Tn / (3.6 : ℝ) ^ n ≤ (10 / 9 : ℝ) ^ n := by
    rw [div_le_iff₀ (by positivity)]
    calc Tn ≤ (4 : ℝ) ^ n := hT
      _ = (10 / 9 : ℝ) ^ n * (3.6 : ℝ) ^ n := by
        rw [← mul_pow]; norm_num
  have h2 : (1 : ℝ) ≤ (10 / 9 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  linarith

/-- The fresh walk `R(ω) = (regenWalk of the slices of N'')` is a.e. measurable. -/
theorem step78_aemeasurable_regen {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*}
    [MeasurableSpace Ω] {Pr : Measure Ω} {N'' : Ω → Measure (ℕ × RingSpace d β)}
    (hN'' : IsPoissonPointProcess N'' ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pr) :
    AEMeasurable (fun ω (t : ℝ≥0) => ElboimSly.regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ))
      Pr := by
  refine (measurable_regW.comp hN''.measurable).aemeasurable.congr ?_
  filter_upwards [ae_cycGood hN''] with ω hω
  funext t
  exact (regenWalk_eq_contGlue (ν := fun k => cycSlice k (N'' ω)) hω t).symm

variable {d : ℕ}

/-- **one excursion succeeds with probability at least frac12** (the bound for one excursion): for `G ∈ ℱ⁺_{ζ_{i+1}}` with
`G ⊆ ℋ₁ ∩ {ζ_{i+1} < t'_n}`, `P(G ∩ {ζ'_{i+1} < t'_n}) ≤ bracket · P(G)`. The numerical
conditions on `n` (`HeavyT`, the range of `L = ρ_k - 1`, `t'_n < 4ⁿ`) are hypotheses here and are
discharged for `n` large in `Lemma78Numerics`. -/
theorem step78_excursion (hd : 5 ≤ d) :
    ∃ Cτ C42 : ℝ, 0 < Cτ ∧ 0 < C42 ∧ ∀ n₁ : ℕ, ∃ β₀ : ℝ, ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ)
      (t₀ : ℝ), β₀ ≤ β → ∀ (hreg : StepRegime d n₁ β n t₀), HeavyT d n₁ step78E0 n →
      (4 : ℝ) ^ (n₁ + 1) ≤ step78Rho d n - 1 → step78Rho d n - 1 ≤ (4 : ℝ) ^ n →
      indScale t₀ n ^ indDelta d ≤ step78Rho d n - 1 →
      (6 * 3 ^ d : ℝ) ^ 6 ≤ step78Rho d n - 1 →
      ∀ (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0), (Tn : ℝ) < (4 : ℝ) ^ n →
      ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
        {N N' : Ω → Measure (CycS Unit d β)} {N'' : Ω → Measure (ℕ × RingSpace d β)}
        (hN : IsPoissonPointProcess N (cycIntensity Unit d β) Pr)
        (hN' : IsPoissonPointProcess N' (cycIntensity Unit d β) Pr)
        (hN'' : IsPoissonPointProcess N''
          ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pr)
        (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
        (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
          (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)
        (hI3 : Indep (MeasurableSpace.comap N'' inferInstance)
          (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ MeasurableSpace.comap N' inferInstance ⊔
            cycNull Pr) Pr)
        (h𝒢 : 𝒢₀ ≤ mΩ) (i : ℕ) {G : Set Ω},
        MeasurableSet[(Step78Data.isStoppingTime_zp_zeta
          (step78_frame u q Tn 𝒢₀ hN h𝒢 (by omega) hreg.2.1 n (step78Rho d n))
          (i + 1)).2.measurableSpace] G →
        G ⊆ {ω | Step78H1 d β t₀ n (Tn : ℝ)
          (fun s : ℝ => cycWalk (cycSlice () (cycNgood N ω)) 0 0 s)} →
        G ⊆ {ω | (step78SliceData (cycNgood N) u q Tn n (step78Rho d n)).zeta (i + 1) ω <
          (Tn : WithTop ℝ≥0)} →
        Pr (G ∩ {ω | (step78SliceData (cycNgood N) u q Tn n (step78Rho d n)).zp (i + 1) ω <
          (Tn : WithTop ℝ≥0)}) ≤
          ENNReal.ofReal (step78Bracket d Cτ C42 β n (step78Rho d n - 1)) * Pr G := by
  obtain ⟨Cτ, hCτ, Ht⟩ := step78_tau_bound.{u} hd
  obtain ⟨C42, hC42, Hb⟩ := step78_law_Sbad hd
  refine ⟨Cτ, C42, hCτ, hC42, fun n₁ => ?_⟩
  obtain ⟨β41, Ht1⟩ := Ht n₁
  refine ⟨max β41 (max ((10 : ℝ) ^ 14) ((4 : ℝ) ^ (n₁ + 2))), ?_⟩
  intro β _ n t₀ hβ hreg hHT hL1 hL2 hL3 hL4 u q Tn hTn Ω 𝒢₀ mΩ Pr N N' N'' hN hN' hN'' hI1 hI2
    hI3 h𝒢 i G hG hGH hGZ
  have hβ41 : β41 ≤ β := (le_max_left _ _).trans hβ
  have hβ14 : (10 : ℝ) ^ 14 ≤ β := ((le_max_left _ _).trans (le_max_right _ _)).trans hβ
  have hβ4 : (4 : ℝ) ^ (n₁ + 2) ≤ β := ((le_max_right _ _).trans (le_max_right _ _)).trans hβ
  have := hN.isProbabilityMeasure
  have hβ0 : 0 < β := Fact.out
  have ht1 : 1 < t₀ := hreg.2.2.2.1.1
  have ht4 : t₀ ≤ 4 := hreg.2.2.2.1.2
  set ρ : ℝ := step78Rho d n with hρ
  set D := step78SliceData (cycNgood N) u q Tn n ρ with hD
  have hF := step78_frame u q Tn 𝒢₀ hN h𝒢 (by omega : 1 ≤ d) hreg.2.1 n ρ
  have hC : Step78Closing D := step78_closing u q Tn n ρ
  have hZst := (Step78Data.isStoppingTime_zp_zeta hF (i + 1)).2
  have hT := step78_isStoppingTime_T u q Tn 𝒢₀ hN h𝒢 hZst
  have hGT : MeasurableSet[hT.measurableSpace] G :=
    step78_measurableSpace_le u q Tn 𝒢₀ hN h𝒢 hZst hG
  set Z := D.zeta (i + 1) with hZ
  set M : Set Ω := {ω | step78T Tn Z ω ≠ ⊤} with hM
  set Y : Ω → ℝ≥0 → Fin d → ℤ := fun ω => contGlue β.toNNReal
    (planFirst (step78Plan d β u q Tn) N N' (step78T Tn Z) (step78Delta N u q Z) ω)
    (contSeq N'' ω) with hY
  -- the law of the fresh walk
  obtain ⟨Ω₀, mΩ₀, Pr₀, N₀, hPr₀, hN₀, -⟩ :=
    exists_isPoissonPointProcess (cycIntensity ℕ d β)
  set R : Ω → ℝ≥0 → Fin d → ℤ :=
    fun ω t => ElboimSly.regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ) with hR
  have hRm : AEMeasurable R Pr := step78_aemeasurable_regen hN''
  have hνlaw : Pr.map R = Pr₀.map (avoidPath N₀) := step78_map_regen_eq_avoid hN'' hN₀
  obtain ⟨hc1, hc2⟩ := step78_couple_zeta u q Tn 𝒢₀ hN hN' hN'' hI1 hI2 hI3 h𝒢
    (by omega : 1 ≤ d) hreg.2.1 n ρ (i + 1)
  have hGM : G ⊆ M := by
    intro ω hω
    have h := hGZ hω
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (h.trans (WithTop.coe_lt_top Tn)).ne
    show step78T Tn Z ω ≠ ⊤
    rw [step78T, ← hr, ← WithTop.coe_add]
    exact WithTop.coe_ne_top
  -- the frozen pair `(W₂(ζ), V)`
  set x : Ω → (Fin d → ℤ) × Set (Fin d → ℤ) :=
    fun ω => (D.w (ElboimSly.SRW.stopReal Z ω) ω, D.V ω) with hx
  have hVfin : ∀ ω, (D.V ω).Finite := by
    intro ω
    have := step78_visited_finite
      (step78_isRegPath_cycWalk (ν := cycNgood N ω) (cycGood_cycNgood N ω) 0 0 Tn) Tn
    refine this.subset ?_
    rintro _ ⟨s, ⟨hs0, hs1⟩, rfl⟩
    exact ⟨s.toNNReal, Real.toNNReal_le_iff_le_coe.2 hs1, by simp [Real.coe_toNNReal _ hs0]⟩
  have hcount : (range x).Countable := by
    refine ((Set.countable_univ : (univ : Set (Fin d → ℤ)).Countable).prod
      (Set.countable_ofPred_finite_subset (Set.countable_univ : (univ : Set (Fin d → ℤ)).Countable))
      ).mono ?_
    rintro _ ⟨ω, rfl⟩
    exact ⟨mem_univ _, hVfin ω, subset_univ _⟩
  have hδ := step78_measurable_delta u q Tn 𝒢₀ hN h𝒢 hT
  have hx1 : Measurable[hT.measurableSpace] (fun ω => (x ω).1) := by
    have : Measurable[hT.measurableSpace] (fun ω => (step78Delta N u q Z ω).2.1) :=
      (measurable_fst.comp measurable_snd).comp hδ
    exact this
  have hVm : ∀ y, MeasurableSet[hT.measurableSpace] {ω | y ∈ D.V ω} := fun y =>
    step78_ms_le u q Tn 𝒢₀ hN h𝒢 hZst _ (measurableSet_stopping_of_zero hZst (hF.hV y))
  have hxm : ∀ e, MeasurableSet[hT.measurableSpace] {ω | x ω = e} := by
    intro e
    have h1 : MeasurableSet[hT.measurableSpace] {ω | (x ω).1 = e.1} :=
      hx1 (measurableSet_singleton e.1)
    have h2 : MeasurableSet[hT.measurableSpace] {ω | D.V ω = e.2} := by
      have : {ω | D.V ω = e.2} = ⋂ y : Fin d → ℤ, {ω | y ∈ D.V ω ↔ y ∈ e.2} := by
        ext ω; simp [Set.ext_iff]
      rw [this]
      refine MeasurableSet.iInter fun y => ?_
      by_cases hy : y ∈ e.2
      · simpa [hy] using hVm y
      · have : {ω | y ∈ D.V ω ↔ y ∈ e.2} = {ω | y ∈ D.V ω}ᶜ := by
          ext ω; simp [hy]
        rw [this]
        exact (hVm y).compl
    have : {ω | x ω = e} = {ω | (x ω).1 = e.1} ∩ {ω | D.V ω = e.2} := by
      ext ω; simp only [mem_ofPred_eq, mem_inter_iff, Prod.ext_iff, hx]
    rw [this]
    exact h1.inter h2
  have hind : ∀ A, MeasurableSet[hT.measurableSpace] A → ∀ Γ, MeasurableSet Γ →
      Pr (A ∩ M ∩ Y ⁻¹' Γ) = Pr (A ∩ M) * (Pr.map R) Γ := by
    intro A hA Γ hΓ
    rw [Measure.map_apply_of_aemeasurable hRm hΓ]
    exact hc1 hA hΓ
  set L : ℝ := ρ - 1 with hLdef
  have hL0 : 0 ≤ L := le_trans (by positivity) hL1
  have hε : ∀ ω ∈ G, (Pr.map R) (step78Sbad d β n (x ω).1 (x ω).2) ≤
      ENNReal.ofReal (step78BracketS d C42 β n L) := by
    intro ω hωG
    obtain ⟨hτhat, hosc⟩ := hGH hωG
    have hlt := hGZ hωG
    obtain ⟨r, hr, -, hfar, -, -⟩ := Step78Data.zeta_succ_attained hF hC ω i hlt
    have hsr : ElboimSly.SRW.stopReal Z ω = r := by
      unfold ElboimSly.SRW.stopReal; rw [hZ, hr]; rfl
    have hxω : x ω = (D.w r ω, D.V ω) := by simp only [hx, hsr]
    rw [hxω, hνlaw]
    have hgood : CycGood (cycNgood N ω) := cycGood_cycNgood N ω
    set w1 : ℝ → Fin d → ℤ := fun s => cycWalk (cycSlice () (cycNgood N ω)) 0 0 s with hw1
    have hcyc : IsCyclicPath w1 := isCyclicPath_cycWalk (hgood ())
    have hT0 : (0 : ℝ) ≤ Tn := Tn.2
    have hτ' := hτhat
    unfold heavyTauHat heavyTauCheck at hτ'
    simp only [lt_min_iff] at hτ'
    have hj : ENNReal.ofReal Tn < pathTjumpCube w1 n := hτ'.2.2.2.1
    have hτ : ENNReal.ofReal Tn < heavyTauPrime d t₀ n w1 := hτ'.2.2.2.2.1
    have hfar' : ∀ u' : Fin d → ℤ, (∃ v ∈ D.V ω, ‖D.w r ω + u' - v‖ ≤ 1) → L ≤ ‖u'‖ := by
      rintro u' ⟨v, hv, hn⟩
      have h1 := hfar v hv
      have h2 : ‖D.w r ω - v‖ ≤ ‖D.w r ω + u' - v‖ + ‖u'‖ := by
        calc ‖D.w r ω - v‖ = ‖(D.w r ω + u' - v) - u'‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      show ρ - 1 ≤ ‖u'‖
      have h3 : ρ ≤ ‖D.w r ω - v‖ := h1
      linarith
    have hcnt : ∀ r' : ℝ, L ≤ r' →
        (({u : Fin d → ℤ | ∃ v ∈ D.V ω, ‖D.w r ω + u - v‖ ≤ 1} ∩ {u | ‖u‖ ≤ r'}).ncard : ℝ)
          ≤ r' ^ (8 / 3 : ℝ) :=
      fun r' hr' => step78_count_V hd ht1 ht4 hHT hcyc hT0 hj hτ (D.w r ω) hL3 hL4 hr'
    obtain ⟨Zc, hcov, hcard⟩ := step78_cover_V hT0 hosc
    have hlaw := Hb β n₁ n t₀ hreg hβ14 hβ4 hN₀ hL1 hL2 (D.w r ω) (D.V ω) hfar' hcnt Zc hcov
    have hcardE : (Zc.card : ℝ≥0∞) ≤ ENNReal.ofReal (2 * (10 / 9 : ℝ) ^ n) := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (step78_card_le hT0 hTn.le hcard)
    have hCf := ElboimSly.Brownian.Cfar_pos d
    refine hlaw.trans ?_
    unfold step78BracketS
    have hA : 0 ≤ ElboimSly.Brownian.Cfar d *
        (3 * (19 / 10 : ℝ) ^ n / Real.sqrt ((389 / 100 : ℝ) ^ n)) ^ (d - 2) := by positivity
    have hb : 0 ≤ C42 * L ^ (-(1 : ℝ) / 30) := by positivity
    calc _ ≤ ENNReal.ofReal (2 * (β ^ 2)⁻¹) + ENNReal.ofReal (C42 * L ^ (-(1 : ℝ) / 30)) +
          (ENNReal.ofReal (Real.exp (-(((n - 1 : ℕ) : ℝ) ^ 2))) +
            ENNReal.ofReal (2 * (10 / 9 : ℝ) ^ n) * ENNReal.ofReal (ElboimSly.Brownian.Cfar d *
              (3 * (19 / 10 : ℝ) ^ n / Real.sqrt ((389 / 100 : ℝ) ^ n)) ^ (d - 2))) := by
          gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  -- freezing
  have hfr : Pr (G ∩ {ω | Y ω ∈ (fun e : (Fin d → ℤ) × Set (Fin d → ℤ) =>
      step78Sbad d β n e.1 e.2) (x ω)}) ≤
      ENNReal.ofReal (step78BracketS d C42 β n L) * Pr G :=
    step78_freeze_le2 (P := Pr) ⟨hT.measurableSpace, hT.measurableSpace_le⟩ hcount hxm (Pr.map R) M
      hind (fun e => measurableSet_step78Sbad β n e.1 e.2) hGT hGM hε
  -- the `τ'` event
  have hrel : ∀ ω ∈ G, ∃ t : ℝ≥0, D.zeta (i + 1) ω = t ∧ (t : ℝ) ∈ D.relaxed ω := by
    intro ω hω
    obtain ⟨r, hr, hrel, -⟩ := Step78Data.zeta_succ_attained hF hC ω i (hGZ hω)
    exact ⟨r, hr, hrel⟩
  set B1 : Set Ω := {ω | ∃ t : ℝ≥0, Z ω = t ∧ hitTime β (D.path ω) 0 (t : ℝ)
    (fun s => D.path ω (t : ℝ) + Y ω s.toNNReal) < ENNReal.ofReal ((4 : ℝ) ^ n)} with hB1
  have hτb : Pr (G ∩ B1) ≤ ENNReal.ofReal (Cτ * β ^ (-indDelta d / 30)) * Pr G :=
    Ht1 β n t₀ hβ41 hreg u q Tn 𝒢₀ hN hN' hN'' hI1 hI2 hI3 h𝒢 ρ (i + 1) hG hrel
  -- the pathwise inclusion
  have hρ1 : 1 < ρ := by
    have : (1 : ℝ) ≤ (4 : ℝ) ^ (n₁ + 1) := one_le_pow₀ (by norm_num)
    linarith
  have hsub : G ∩ {ω | D.zp (i + 1) ω < (Tn : WithTop ℝ≥0)} ≤ᵐ[Pr]
      (G ∩ B1) ∪ (G ∩ {ω | Y ω ∈ (fun e : (Fin d → ℤ) × Set (Fin d → ℤ) =>
        step78Sbad d β n e.1 e.2) (x ω)}) := by
    filter_upwards [hc2] with ω hω hmem
    obtain ⟨hωG, hzp⟩ := hmem
    have hlt := hGZ hωG
    obtain ⟨r, hr, -, -, -, -⟩ := Step78Data.zeta_succ_attained hF hC ω i hlt
    have hsr : ElboimSly.SRW.stopReal Z ω = r := by
      unfold ElboimSly.SRW.stopReal; rw [hZ, hr]; rfl
    have hne : Z ω ≠ ⊤ := by rw [hZ, hr]; exact WithTop.coe_ne_top
    have hrT : r < Tn := WithTop.coe_lt_coe.1 (hr ▸ hlt)
    have hgood : CycGood (cycNgood N ω) := cycGood_cycNgood N ω
    have h0 : ∀ ω', D.w 0 ω' = D.u := by
      intro ω'
      show cycWalk (cycSlice () (cycNgood N ω')) u q ((0 : ℝ≥0) : ℝ) = u
      rw [NNReal.coe_zero]
      exact cycWalk_zero (cycGood_cycNgood N ω' ()) u q
    have hcpl : ∀ s : ℝ≥0, (r : WithTop ℝ≥0) + (s : WithTop ℝ≥0) ≤ D.bTime Z ω →
        D.w (r + s) ω = D.w r ω + Y ω s := by
      intro s hs
      have hb : Z ω + (s : WithTop ℝ≥0) ≤ step78B N u q Tn Z ω := by rw [hZ, hr]; exact hs
      have h := hω hne s hb
      rw [hsr] at h
      have hc : D.w (r + s) ω = D.w r ω + (cycWalk (cycSlice () (cycNgood N ω)) u q
          ((r : ℝ) + s) - cycWalk (cycSlice () (cycNgood N ω)) u q (r : ℝ)) := by
        show cycWalk (cycSlice () (cycNgood N ω)) u q ((r + s : ℝ≥0) : ℝ) = _
        have e : D.w r ω = cycWalk (cycSlice () (cycNgood N ω)) u q (r : ℝ) := rfl
        rw [NNReal.coe_add, e]; abel
      rw [hc, h]
    have hdec := Step78Data.decomp hF hC hρ1 hTn h0 ω i hr hrT hzp
      (X := Y ω) (rc_freshWalk (step78Plan d β u q Tn) N N' N'' (step78T Tn Z)
        (step78Delta N u q Z) ω) hcpl
    rcases hdec with hS | hH
    · refine Or.inr ⟨hωG, ?_⟩
      show Y ω ∈ step78Sbad d β n (D.w (ElboimSly.SRW.stopReal Z ω) ω) (D.V ω)
      rw [hsr]; exact hS
    · exact Or.inl ⟨hωG, r, hr, hH⟩
  calc Pr (G ∩ {ω | D.zp (i + 1) ω < (Tn : WithTop ℝ≥0)})
      ≤ Pr ((G ∩ B1) ∪ (G ∩ {ω | Y ω ∈ (fun e : (Fin d → ℤ) × Set (Fin d → ℤ) =>
        step78Sbad d β n e.1 e.2) (x ω)})) := measure_mono_ae hsub
    _ ≤ Pr (G ∩ B1) + Pr (G ∩ {ω | Y ω ∈ (fun e : (Fin d → ℤ) × Set (Fin d → ℤ) =>
        step78Sbad d β n e.1 e.2) (x ω)}) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Cτ * β ^ (-indDelta d / 30)) * Pr G +
        ENNReal.ofReal (step78BracketS d C42 β n L) * Pr G := add_le_add hτb hfr
    _ = ENNReal.ofReal (step78Bracket d Cτ C42 β n L) * Pr G := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity)
          (step78BracketS_nonneg n hC42.le hβ0 hL0)]
        rfl

end ElboimSly.Paper.Step

end
