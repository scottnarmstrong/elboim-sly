/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.BlockEvents
public import ElboimSly.Paper.Base.BaseH4
public import ElboimSly.Paper.Bridge.WienerBridge
public import ElboimSly.Paper.Step.Cor72
public import Mathlib

/-!
# The core of Lemma 7.6 (conditional on Corollary 7.2 and the `σ`-estimate)

ES22 Lemma 7.6, Steps 3-5.

`lemma76_core`: for given block parameters `(ℓ, T)` and a `σ ∈ [1, 2]` with
`σ² = E[Y₁²]` (the variance of the first coordinate of the block functional), the regenerated walk
admits a `(σ, t_n^{θ_H})`-coupling up to time `t_n` with failure probability
`e^{-c n³}`, `c = ½ min {c_cat, c_tr, 1/7}`. The coupling is the law of the pair
`(W^♭|_{[0,t_n]}, B)` on the probability space of `lemma76_space`.

**Conditional**: assumes `StepCor72` (Corollary 7.2) and `StepTr` (Lemma 7.4); the variance
identity `hvar` is the definition of `σ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper ElboimSly.Paper.Base ElboimSly.Bridge

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem lemma76_core (hd : 1 ≤ d) {cCat : ℝ} {βCat : ℕ → ℝ} (hCor : StepCor72 d cCat βCat)
    (hcCat : 0 < cCat) {cTr : ℝ} {βTr : ℕ → ℝ} (hTr : StepTr d cTr βTr) (hcTr : 0 < cTr)
    {n₁ n : ℕ} {t₀ : ℝ} (hR : StepRegime d n₁ β n t₀) (hβc : βCat n₁ ≤ β) (hβt : βTr n₁ ≤ β) (hn₁ : 8 * d ≤ n₁)
    (hnX : StrongApprox.nX d ≤ n) (hn16 : 16 ≤ n)
    {ℓ : ℕ} {T : ℝ≥0} (hℓ : 1 ≤ ℓ) (hT : 0 < T)
    (hℓa : indScale t₀ n ^ ((79 : ℝ) / 200) / 2 ≤ ℓ)
    (hℓb : (ℓ : ℝ) ≤ 2 * indScale t₀ n ^ ((79 : ℝ) / 200)) (hℓT : (ℓ : ℝ) * T = indScale t₀ n)
    (hTlo : Real.sqrt (indScale t₀ n) ≤ T) (hThi : (T : ℝ) ≤ indScale t₀ n)
    (hrad : (ℓ : ℝ) * indScale t₀ n ^ (2 * heavyEps d) + 4 * ((n : ℝ) ^ 2 * Real.sqrt T) ≤
      3 / 8 * indScale t₀ n ^ indThetaH)
    (hbig : ((4 * d + 3) * ℓ : ℝ) ≤
      Real.exp (min (min cCat cTr) (1 / 7) / 2 * (n : ℝ) ^ 3))
    {Ωe : Type} [MeasurableSpace Ωe] {Pe : Measure Ωe} {N : Ωe → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2)
    (hvar : ∫ w, (blockY T ((n : ℝ) ^ 2 * Real.sqrt T) w ⟨0, hd⟩) ^ 2 ∂ppLaw Pe N T = σ ^ 2) :
    AdmitsBMCoupling d (indScale t₀ n).toNNReal
      (Pe.map (fun ω (t : Set.Icc (0 : ℝ≥0) (indScale t₀ n).toNNReal) =>
        regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ)))
      σ (indScale t₀ n ^ indThetaH)
      (Real.exp (-(min (min cCat cTr) (1 / 7) / 2 * (n : ℝ) ^ 3))) := by
  obtain ⟨-, hβ1, hn1, ht0, htn_lt, -⟩ := id hR
  obtain ⟨htn_gt, htn_le⟩ := indScale_bounds (n := n) ht0
  have htn0 : 0 < indScale t₀ n := lt_trans (by positivity) htn_gt
  set tn := indScale t₀ n with htn
  obtain ⟨Ω'', _, P'', X'', B, hP'', hX'', hXp'', hB, hE3⟩ := lemma76_space hd hnX htn_gt
    htn_le hℓa hℓb hT (by rw [hℓT]; linarith) (by linarith) hσ2 hN hvar
  have := hP''
  set K : ℝ := (n : ℝ) ^ 2 * Real.sqrt T with hK
  set s : ℕ → ℝ≥0 := fun _ => T with hs
  set T' : ℝ≥0 := tn.toNNReal with hT'
  have hT'c : (T' : ℝ) = tn := Real.coe_toNNReal _ htn0.le
  have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hKpos : 0 < K := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have := Real.sqrt_pos.2 hTR
    rw [hK]; positivity
  have hT'eq : (ℓ : ℝ≥0) * T = T' := by
    apply NNReal.coe_injective; push_cast; rw [hℓT, hT'c]
  have hP2 : stepPartial s ℓ = T' := by rw [stepPartial_const, hT'eq]
  set c' : ℝ := min (min cCat cTr) (1 / 7) with hc'
  -- the events
  set E1 : Set Ω'' := {ω | ∃ u : ℝ≥0, u ≤ stepPartial s ℓ ∧
    (ℓ : ℝ) * tn ^ (2 * heavyEps d) ≤
      ‖stepReg β (stepShift 0 (X'' ω)) u - stepNatTilde β 0 s ℓ (X'' ω) u‖} with hE1
  set E2 : Set Ω'' := ⋃ j ∈ Finset.range ℓ, {ω | stepWj β 0 s (X'' ω) j ∈ farSet K T} with hE2
  set E3 : Set Ω'' := {ω | ∃ j : Fin ℓ, tn ^ ((41 : ℝ) / 100) / 8 ≤
      ‖∑ i ∈ Finset.univ.filter (· ≤ j), travelX β 0 T K X'' i ω -
        σ • B ((((j : ℕ) + 1 : ℕ) : ℝ≥0) * T) ω‖} with hE3def
  set E4 : Set Ω'' := {ω | ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧ ∃ u : ℝ≥0, ((j - 1 : ℕ) : ℝ≥0) * T ≤ u ∧
    u ≤ j * T ∧ K ≤ ‖B u ω - B (j * T) ω‖} with hE4
  have hP1 : P'' E1 ≤ ENNReal.ofReal (((ℓ : ℝ) - 1) * Real.exp (-(cCat * (n : ℝ) ^ 3))) := by
    have h := hCor n₁ hR.1 β n t₀ hβc hR Ω'' P'' X'' hX'' hXp'' 0 ℓ s hℓ (fun _ => hT)
      (by rw [hP2, hT'c])
    rw [← ENNReal.ofReal_toReal (measure_ne_top P'' E1)]
    exact ENNReal.ofReal_le_ofReal h
  have hP2' : P'' E2 ≤ ℓ * ENNReal.ofReal (Real.exp (-(cTr * (n : ℝ) ^ 3))) := by
    refine measure_blocks_far hX'' hXp'' hN T K ℓ ?_
    exact hTr n₁ hn₁ β n t₀ hβt hR Ωe Pe N hN (T : ℝ) hTlo hThi
  have hP4 : P'' E4 ≤ (4 * d * ℓ : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 2) ^ 2 / 16)) := by
    have h := hB.oscillation_grid_le (P := P'') (h := T) hT.ne' hKpos ℓ
    have e : -K ^ 2 / (16 * (T : ℝ)) = -((n : ℝ) ^ 2) ^ 2 / 16 := by
      rw [hK, mul_pow, Real.sq_sqrt hTR.le]; field_simp
    rw [e] at h
    exact h
  have hsum := lemma76_sum_le hcCat hcTr hn16 hℓ (by simpa [hc'] using hbig)
  -- total bound on the bad event
  have hbad : P'' (E1 ∪ E2 ∪ E3 ∪ E4) ≤ ENNReal.ofReal (Real.exp (-(c' / 2 * (n : ℝ) ^ 3))) := by
    have hneg : -((n : ℝ) ^ 2) ^ 2 / 16 = -(((n : ℝ) ^ 2) ^ 2 / 16) := neg_div _ _
    rw [hneg] at hP4
    have hℓ0 : (0 : ℝ) ≤ ℓ := by positivity
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have hA2 : (ℓ : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(cTr * (n : ℝ) ^ 3))) =
        ENNReal.ofReal ((ℓ : ℝ) * Real.exp (-(cTr * (n : ℝ) ^ 3))) := by
      rw [ENNReal.ofReal_mul hℓ0, ENNReal.ofReal_natCast]
    have hA4 : (4 * d * ℓ : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(((n : ℝ) ^ 2) ^ 2 / 16))) =
        ENNReal.ofReal ((4 * d * ℓ : ℝ) * Real.exp (-(((n : ℝ) ^ 2) ^ 2 / 16))) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      simp
    rw [hA2] at hP2'
    rw [hA4] at hP4
    calc P'' (E1 ∪ E2 ∪ E3 ∪ E4) ≤ P'' E1 + P'' E2 + P'' E3 + P'' E4 :=
          le_trans (measure_union_le _ _) (add_le_add (le_trans (measure_union_le _ _)
            (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
      _ ≤ ENNReal.ofReal (((ℓ : ℝ) - 1) * Real.exp (-(cCat * (n : ℝ) ^ 3))) +
          ENNReal.ofReal ((ℓ : ℝ) * Real.exp (-(cTr * (n : ℝ) ^ 3))) +
          ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 3 / 7)) +
          ENNReal.ofReal ((4 * d * ℓ : ℝ) * Real.exp (-(((n : ℝ) ^ 2) ^ 2 / 16))) :=
          add_le_add (add_le_add (add_le_add hP1 hP2') hE3) hP4
      _ = ENNReal.ofReal (((ℓ : ℝ) - 1) * Real.exp (-(cCat * (n : ℝ) ^ 3)) +
          (ℓ : ℝ) * Real.exp (-(cTr * (n : ℝ) ^ 3)) + Real.exp (-(n : ℝ) ^ 3 / 7) +
          (4 * d * ℓ : ℝ) * Real.exp (-(((n : ℝ) ^ 2) ^ 2 / 16))) := by
          have hℓ1' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
          have n1 : 0 ≤ ((ℓ : ℝ) - 1) * Real.exp (-(cCat * (n : ℝ) ^ 3)) :=
            mul_nonneg (by linarith) (Real.exp_pos _).le
          have n2 : 0 ≤ (ℓ : ℝ) * Real.exp (-(cTr * (n : ℝ) ^ 3)) := by positivity
          have n3 : 0 ≤ Real.exp (-(n : ℝ) ^ 3 / 7) := (Real.exp_pos _).le
          have n4 : 0 ≤ (4 * d * ℓ : ℝ) * Real.exp (-(((n : ℝ) ^ 2) ^ 2 / 16)) := by positivity
          rw [ENNReal.ofReal_add (add_nonneg (add_nonneg n1 n2) n3) n4,
            ENNReal.ofReal_add (add_nonneg n1 n2) n3, ENNReal.ofReal_add n1 n2]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hsum
  -- the coupling measure
  have hWm : Measurable fun ω (t : ℝ≥0) => stepReg β (X'' ω) t :=
    measurable_stepReg_path hX''.1 fun ω => (hXp'' ω).toIsRegPath
  have hstep : ∀ ω, IsStepPath (fun t : ℝ≥0 => stepReg β (X'' ω) t) := fun ω =>
    ⟨(isRegPath_stepReg (hXp'' ω).toIsRegPath).rc, (isRegPath_stepReg (hXp'' ω).toIsRegPath).fin⟩
  let Bp : Ω'' → C(ℝ≥0, Fin d → ℝ) := fun ω => ⟨fun t => B t ω, (hB.continuous_zero ω).1⟩
  have hBp : Measurable Bp := measurable_pathC hB
  let Fm : Ω'' → WalkPath d T' × C(ℝ≥0, Fin d → ℝ) := fun ω =>
    (walkPathOf T' (hstep ω), Bp ω)
  have hF1 : Measurable fun ω => walkPathOf T' (hstep ω) :=
    Measurable.subtype_mk ((measurable_restrictIcc T').comp hWm)
  have hFm : Measurable Fm := hF1.prodMk hBp
  refine ⟨P''.map Fm, ⟨by rw [Measure.map_apply hFm MeasurableSet.univ]; simp⟩, ?_, ?_, ?_⟩
  · have hg : Measurable fun p : WalkPath d T' × C(ℝ≥0, Fin d → ℝ) => p.1.1 :=
      measurable_subtype_coe.comp measurable_fst
    rw [Measure.map_map hg hFm]
    have e1 : ((fun p : WalkPath d T' × C(ℝ≥0, Fin d → ℝ) => p.1.1) ∘ Fm) =
        restrictIcc T' ∘ (fun ω (t : ℝ≥0) => stepReg β (X'' ω) t) := rfl
    rw [e1, ← Measure.map_map (measurable_restrictIcc T') hWm, stepReg_law hX'' hXp'' hN,
      AEMeasurable.map_map_of_aemeasurable (measurable_restrictIcc T').aemeasurable
        (aemeasurable_regenWalk_path hN)]
    rfl
  · rw [Measure.map_map measurable_snd hFm]
    exact isWienerMeasure_map_pathC hB
  · have hA := measurableSet_failEvent (d := d) (T := T') σ (tn ^ indThetaH)
    refine (Measure.map_apply hFm hA).trans_le (le_trans (measure_mono ?_) hbad)
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hcon
    have hθ : indThetaH = (41 : ℝ) / 100 := by unfold indThetaH; norm_num
    have hPart : stepPartial s ℓ = (ℓ : ℝ≥0) * T := stepPartial_const T ℓ
    have hE1' : ∀ u : ℝ≥0, u ≤ (ℓ : ℝ≥0) * T → ‖stepReg β (stepShift 0 (X'' ω)) u -
        stepNatTilde β 0 s ℓ (X'' ω) u‖ < (ℓ : ℝ) * tn ^ (2 * heavyEps d) := by
      intro u hu
      by_contra hcon'
      exact c1 ⟨u, by rw [hPart]; exact hu, not_lt.1 hcon'⟩
    have hE2' : ∀ i < ℓ, stepWj β 0 s (X'' ω) i ∉ farSet K T := fun i hi hmem =>
      c2 (mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hi, hmem⟩)
    have hE3' : ∀ j < ℓ, ‖∑ i ∈ Finset.range (j + 1),
        (fun c => ((truncEnd T K (stepWj β 0 s (X'' ω) i) c : ℤ) : ℝ)) -
          σ • B ((((j + 1 : ℕ)) : ℝ≥0) * T) ω‖ < tn ^ ((41 : ℝ) / 100) / 8 := by
      intro j hj
      by_contra hcon'
      apply c3
      refine ⟨⟨j, hj⟩, ?_⟩
      have := sum_filter_fin_le (fun i => travelX β 0 T K X'' i ω) ⟨j, hj⟩
      rw [this]
      exact not_lt.1 hcon'
    have hE4' : ∀ j : ℕ, 1 ≤ j → j ≤ ℓ → ∀ u : ℝ≥0, ((j - 1 : ℕ) : ℝ≥0) * T ≤ u → u ≤ j * T →
        ‖B u ω - B (j * T) ω‖ < K := by
      intro j hj1 hjℓ u hu1 hu2
      by_contra hcon'
      exact c4 ⟨j, hj1, hjℓ, u, hu1, hu2, not_lt.1 hcon'⟩
    have hpt : ∀ u : ℝ≥0, u ≤ (ℓ : ℝ≥0) * T →
        ‖(fun c => ((stepReg β (X'' ω) u c : ℤ) : ℝ)) - σ • B u ω‖ < tn ^ indThetaH / 2 := by
      intro u hu
      have h := lemma76_pathwise (β := β) (hXp'' ω) hℓ (K := K) (σ := σ)
        (ε' := (ℓ : ℝ) * tn ^ (2 * heavyEps d)) (r₃ := tn ^ ((41 : ℝ) / 100) / 8)
        (by linarith) hσ2 (fun t => B t ω) hE1' hE2' hE3' hE4' u hu
      rw [hθ] at hrad ⊢
      linarith
    have hsup : (⨆ t : Set.Icc (0 : ℝ≥0) T', failTime (d := d) σ (Fm ω) t) ≤
        ENNReal.ofReal (tn ^ indThetaH / 2) := by
      refine iSup_le fun t => ?_
      unfold failTime
      refine ENNReal.ofReal_le_ofReal (hpt t ?_).le
      have ht' : (t : ℝ≥0) ≤ T' := t.2.2
      exact ht'.trans_eq hT'eq.symm
    have htθ : 0 < tn ^ indThetaH := Real.rpow_pos_of_pos htn0 _
    have h1 : ENNReal.ofReal (tn ^ indThetaH) ≤ ENNReal.ofReal (tn ^ indThetaH / 2) :=
      hω.trans hsup
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    linarith

end ElboimSly.Paper.Step
