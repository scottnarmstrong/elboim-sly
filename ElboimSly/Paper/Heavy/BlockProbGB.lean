/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BlockProbPieces
public import ElboimSly.Paper.Heavy.BlockProbShift
public import ElboimSly.Paper.Heavy.BlockProbBM
public import ElboimSly.Paper.Heavy.GoodLocalMeas
public import ElboimSly.Paper.Step.RegenMeas
public import ElboimSly.Paper.Induction.RelaxedMeasRegen2
public import ElboimSly.Foundations.Interchange.GoodAs
public import Mathlib

/-!
# Failure probabilities of (GB1) and (GB2) for one starting datum

Probability that a block is bad, proof of (GB1) and (GB2).

Let `N'` be a Poisson point process of intensity `# ⊗ μ_β` on `ℕ × S_β` and `ν_j = copyEnv N' j`.
* `gb1_prob`: if (H1) holds at the time `t` (i.e. `P(W|[0,t] relaxed path) ≥ 1 - p`), then for every
  `(u, q)` the probability that `W^{ν_0}_{u,q}` neither closes by `t` nor has relaxed measure at
  least `(0.9 + 1/κ) t` is at most `p`.
* `gb2_prob`: if the law of `W|[0,t]` admits a `(σ, ε)`-coupling with failure probability `η`, then
  the probability that `W^{ν_0}_{u,q}` moves further than `R` from `u` within time `t` is at most
  `η + 4d exp(-(l/σ)²/(2t))` whenever `l + ε ≤ R`.
Both reduce to `(u, q) = (0, 0)` by translation invariance (`prob_shiftEnv_eq`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {N : Ω → Measure (ℕ × RingSpace d β)}

theorem ae_all_good_copyEnv
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P) :
    ∀ᵐ ω ∂P, ∀ k, Good (copyEnv (N ω) k) :=
  ae_all_iff.2 fun k => Interchange.ae_good (Roots.isPoissonPointProcess_copyEnv hN k)

theorem nullMeasurableSet_isRelaxedPath
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    (t : ℝ) : NullMeasurableSet {ω | IsRelaxedPath (fun k => copyEnv (N ω) k) t} P := by
  classical
  have hP := hN.isProbabilityMeasure
  have hgood := ae_all_good_copyEnv hN
  obtain ⟨ω₀, hω₀⟩ := hgood.exists
  set ν₀ : Measure (RingSpace d β) := copyEnv (N ω₀) 0 with hν₀
  have hg₀ : Good ν₀ := hω₀ 0
  have hmeas : ∀ k, Measurable fun ω => copyEnv (N ω) k := fun k =>
    (Roots.isPoissonPointProcess_copyEnv hN k).measurable
  let ν' : Ω → ℕ → Measure (RingSpace d β) := fun ω k =>
    if Good (copyEnv (N ω) k) then copyEnv (N ω) k else ν₀
  have hν'm : ∀ k, Measurable fun ω => ν' ω k := fun k =>
    Measurable.ite (measurableSet_good.preimage (hmeas k)) (hmeas k) measurable_const
  have hν'g : ∀ ω k, Good (ν' ω k) := by
    intro ω k
    by_cases h : Good (copyEnv (N ω) k)
    · simp [ν', h]
    · simp [ν', h, hg₀]
  have hA' := measurableSet_isRelaxedPath ν' hν'm hν'g t
  refine hA'.nullMeasurableSet.congr ?_
  filter_upwards [hgood] with ω hω
  have : ν' ω = fun k => copyEnv (N ω) k := funext fun k => by simp [ν', hω k]
  simp only [this]

/-- (GB1) at the origin. -/
theorem gb1_prob_zero
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    {t : ℝ} (ht : 0 ≤ t) {κ : ℕ} (hκ : scaleIndex t = κ) {p : ℝ} (hp1 : p ≤ 1)
    (hH1 : ENNReal.ofReal (1 - p) ≤
      P {ω | IsRelaxedPath (fun k => copyEnv (N ω) k) t}) :
    P {ω | Good (copyEnv (N ω) 0) ∧ ¬ cycClosesBy (copyEnv (N ω) 0) 0 0 t ∧
      volume {s : ℝ | s ∈ Icc 0 t ∧
        IsRelaxedTimeWrt β (fun r => cycWalk (copyEnv (N ω) 0) 0 0 r) 0 s} <
        ENNReal.ofReal ((9 / 10 + 1 / (κ : ℝ)) * t)} ≤ ENNReal.ofReal p := by
  have hP := hN.isProbabilityMeasure
  have hgood := ae_all_good_copyEnv hN
  have hnull := nullMeasurableSet_isRelaxedPath hN t
  have hsub : {ω | Good (copyEnv (N ω) 0) ∧ ¬ cycClosesBy (copyEnv (N ω) 0) 0 0 t ∧
      volume {s : ℝ | s ∈ Icc 0 t ∧
        IsRelaxedTimeWrt β (fun r => cycWalk (copyEnv (N ω) 0) 0 0 r) 0 s} <
        ENNReal.ofReal ((9 / 10 + 1 / (κ : ℝ)) * t)} ≤ᵐ[P]
      {ω | IsRelaxedPath (fun k => copyEnv (N ω) k) t}ᶜ := by
    filter_upwards [hgood] with ω hω hmem
    obtain ⟨-, hnc, hv⟩ := hmem
    intro hrel
    have hlt : ENNReal.ofReal t < cycTreg (copyEnv (N ω) 0) := by
      by_contra hcon
      exact hnc ((cycClosesBy_zero_iff ht).2 (not_lt.1 hcon))
    have hset := relaxedSet_regen_eq (ν := fun k => copyEnv (N ω) k) hω hlt
    simp only [mem_ofPred_eq, IsRelaxedPath] at hrel
    rw [hset, hκ] at hrel
    exact absurd hv (not_lt.2 hrel)
  refine (measure_mono_ae hsub).trans ?_
  rw [prob_compl_eq_one_sub₀ hnull]
  calc 1 - P {ω | IsRelaxedPath (fun k => copyEnv (N ω) k) t} ≤ 1 - ENNReal.ofReal (1 - p) :=
        tsub_le_tsub_left hH1 _
    _ = ENNReal.ofReal p := by
        have h := ENNReal.ofReal_sub 1 (show 0 ≤ 1 - p by linarith)
        rw [ENNReal.ofReal_one] at h
        rw [← h]; congr 1; ring

theorem measurableSet_gb1_fail (u : Fin d → ℤ) (q t c : ℝ) :
    MeasurableSet {ν : Measure (RingSpace d β) | Good ν ∧ ¬ cycClosesBy ν u q t ∧
      volume {s : ℝ | s ∈ Icc 0 t ∧ IsRelaxedTimeWrt β (fun r => cycWalk ν u q r) 0 s} <
        ENNReal.ofReal c} := by
  refine measurableSet_good_and (P := fun ν => ¬ cycClosesBy ν u q t ∧
      volume {s : ℝ | s ∈ Icc 0 t ∧ IsRelaxedTimeWrt β (fun r => cycWalk ν u q r) 0 s} <
        ENNReal.ofReal c) ?_
  exact (measurableSet_closes u q t).compl.inter
    (measurableSet_lt (measurable_relaxedVolume u q t) measurable_const)

/-- (GB1) for a general datum `(u, q)`. -/
theorem gb1_prob
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    {t : ℝ} (ht : 0 ≤ t) {κ : ℕ} (hκ : scaleIndex t = κ) {p : ℝ} (hp1 : p ≤ 1)
    (hH1 : ENNReal.ofReal (1 - p) ≤
      P {ω | IsRelaxedPath (fun k => copyEnv (N ω) k) t}) (u : Fin d → ℤ) (q : ℝ) :
    P {ω | Good (copyEnv (N ω) 0) ∧ ¬ cycClosesBy (copyEnv (N ω) 0) u q t ∧
      volume {s : ℝ | s ∈ Icc 0 t ∧
        IsRelaxedTimeWrt β (fun r => cycWalk (copyEnv (N ω) 0) u q r) 0 s} <
        ENNReal.ofReal ((9 / 10 + 1 / (κ : ℝ)) * t)} ≤ ENNReal.ofReal p := by
  have hν := Roots.isPoissonPointProcess_copyEnv hN 0
  have hβ : 0 < β := Fact.out
  set c := (9 / 10 + 1 / (κ : ℝ)) * t
  have hB := measurableSet_gb1_fail (β := β) (0 : Fin d → ℤ) 0 t c
  have hsub : {ω | Good (copyEnv (N ω) 0) ∧ ¬ cycClosesBy (copyEnv (N ω) 0) u q t ∧
      volume {s : ℝ | s ∈ Icc 0 t ∧
        IsRelaxedTimeWrt β (fun r => cycWalk (copyEnv (N ω) 0) u q r) 0 s} <
        ENNReal.ofReal c} ⊆
      {ω | shiftEnv u q (copyEnv (N ω) 0) ∈ {ν : Measure (RingSpace d β) | Good ν ∧
        ¬ cycClosesBy ν 0 0 t ∧
        volume {s : ℝ | s ∈ Icc 0 t ∧
          IsRelaxedTimeWrt β (fun r => cycWalk ν 0 0 r) 0 s} < ENNReal.ofReal c}} := by
    rintro ω ⟨hg, hnc, hv⟩
    refine ⟨good_shiftEnv hg, ?_, ?_⟩
    · rintro ⟨m, hm1, hm2, h0⟩
      refine hnc ⟨m, hm1, hm2, ?_⟩
      have := cycWalk_shiftEnv hg u q (s := (m : ℝ) * β) (by positivity)
      rw [h0] at this
      exact (sub_eq_zero.1 this.symm)
    · have e : {s : ℝ | s ∈ Icc 0 t ∧
          IsRelaxedTimeWrt β (fun r => cycWalk (shiftEnv u q (copyEnv (N ω) 0)) 0 0 r) 0 s} =
          {s : ℝ | s ∈ Icc 0 t ∧
            IsRelaxedTimeWrt β (fun r => cycWalk (copyEnv (N ω) 0) u q r) 0 s} := by
        ext s
        simp only [mem_ofPred_eq]
        refine and_congr_right fun hs => ?_
        rw [isRelaxedTimeWrt_congr_Icc hβ hs.1 (w' := fun r => cycWalk (copyEnv (N ω) 0) u q r - u)
          (fun r hr => cycWalk_shiftEnv hg u q hr.1)]
        exact isRelaxedTimeWrt_sub_const u 0 s
      rw [e]; exact hv
  refine (measure_mono hsub).trans ?_
  rw [prob_shiftEnv_eq hν u q hB]
  exact gb1_prob_zero hN ht hκ hp1 hH1

theorem measurableSet_gb2_fail (u : Fin d → ℤ) (q t R : ℝ) :
    MeasurableSet {ν : Measure (RingSpace d β) | Good ν ∧
      ∃ s ∈ Icc (0 : ℝ) t, R < ‖cycWalk ν u q s - u‖} := by
  refine measurableSet_good_and (P := fun ν => ∃ s ∈ Icc (0 : ℝ) t, R < ‖cycWalk ν u q s - u‖) ?_
  have := (measurableSet_gb2 (β := β) u q t R).compl
  convert this using 1
  ext ν
  simp [and_assoc]

/-- (GB2) at the origin, from the Brownian coupling. -/
theorem gb2_prob_zero
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    {t : ℝ} (ht : 0 < t) {σ ε η R l : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (hl : 0 < l)
    (hlR : l + ε ≤ R)
    (hC : AdmitsBMCoupling d t.toNNReal
      (P.map (fun ω (τ : Set.Icc (0 : ℝ≥0) t.toNNReal) =>
        regenWalk (fun k => copyEnv (N ω) k) ((τ : ℝ≥0) : ℝ))) σ ε η) :
    P {ω | Good (copyEnv (N ω) 0) ∧ ∃ s ∈ Icc (0 : ℝ) t, R < ‖cycWalk (copyEnv (N ω) 0) 0 0 s - 0‖} ≤
      ENNReal.ofReal η + (4 * d : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(l / σ) ^ 2 / (2 * t))) := by
  have hgood := ae_all_good_copyEnv hN
  have hTc : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ ht.le
  have hT0 : t.toNNReal ≠ 0 := by
    intro h; rw [← NNReal.coe_eq_zero, hTc] at h; linarith
  have hF := aemeasurable_regenWalk_Icc hN t.toNNReal
  have hrlc : ∀ᵐ ω ∂P, ∀ q : Set.Icc (0 : ℝ≥0) t.toNNReal, ∃ ε > 0,
      ∀ q' : Set.Icc (0 : ℝ≥0) t.toNNReal, (q : ℝ≥0) ≤ q' → (q' : ℝ≥0) < q + ε →
        regenWalk (fun k => copyEnv (N ω) k) ((q' : ℝ≥0) : ℝ) =
          regenWalk (fun k => copyEnv (N ω) k) ((q : ℝ≥0) : ℝ) := by
    filter_upwards [hgood] with ω hω q
    obtain ⟨ε₀, hε₀, h⟩ := regenWalk_rlc hω (s := ((q : ℝ≥0) : ℝ)) (NNReal.coe_nonneg _)
    refine ⟨ε₀.toNNReal, by simpa using hε₀, fun q' h1 h2 => h _ ⟨?_, ?_⟩⟩
    · exact_mod_cast h1
    · have : ((q' : ℝ≥0) : ℝ) < ((q : ℝ≥0) : ℝ) + ε₀ := by
        have := (NNReal.coe_lt_coe).2 h2
        rw [NNReal.coe_add, Real.coe_toNNReal _ hε₀.le] at this
        exact this
      exact this
  have hex := exit_prob_of_coupling (R := R) (l := l) hT0 hF hrlc hσ hε hl hlR hC
  have hsub : {ω | Good (copyEnv (N ω) 0) ∧ ∃ s ∈ Icc (0 : ℝ) t,
      R < ‖cycWalk (copyEnv (N ω) 0) 0 0 s - 0‖} ≤ᵐ[P]
      {ω | ∃ τ : Set.Icc (0 : ℝ≥0) t.toNNReal,
        R < ‖(fun τ : Set.Icc (0 : ℝ≥0) t.toNNReal =>
          regenWalk (fun k => copyEnv (N ω) k) ((τ : ℝ≥0) : ℝ)) τ‖} := by
    filter_upwards [hgood] with ω hω hmem
    obtain ⟨-, s, hs, hR⟩ := hmem
    rw [sub_zero] at hR
    obtain ⟨s', hs', hR'⟩ := exists_regenWalk_of_cycWalk hω hs hR
    refine ⟨⟨s'.toNNReal, zero_le, ?_⟩, ?_⟩
    · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs'.1, hTc]; exact hs'.2
    · simp only [Real.coe_toNNReal _ hs'.1]; exact hR'
  have hE : (2 * (t.toNNReal : ℝ)) = 2 * t := by rw [hTc]
  refine (measure_mono_ae hsub).trans ?_
  simpa [hTc] using hex

/-- (GB2) for a general datum `(u, q)`. -/
theorem gb2_prob
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    {t : ℝ} (ht : 0 < t) {σ ε η R l : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (hl : 0 < l)
    (hlR : l + ε ≤ R)
    (hC : AdmitsBMCoupling d t.toNNReal
      (P.map (fun ω (τ : Set.Icc (0 : ℝ≥0) t.toNNReal) =>
        regenWalk (fun k => copyEnv (N ω) k) ((τ : ℝ≥0) : ℝ))) σ ε η)
    (u : Fin d → ℤ) (q : ℝ) :
    P {ω | Good (copyEnv (N ω) 0) ∧ ∃ s ∈ Icc (0 : ℝ) t, R < ‖cycWalk (copyEnv (N ω) 0) u q s - u‖} ≤
      ENNReal.ofReal η + (4 * d : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(l / σ) ^ 2 / (2 * t))) := by
  have hν := Roots.isPoissonPointProcess_copyEnv hN 0
  have hB := measurableSet_gb2_fail (β := β) (0 : Fin d → ℤ) 0 t R
  have hsub : {ω | Good (copyEnv (N ω) 0) ∧ ∃ s ∈ Icc (0 : ℝ) t,
      R < ‖cycWalk (copyEnv (N ω) 0) u q s - u‖} ⊆
      {ω | shiftEnv u q (copyEnv (N ω) 0) ∈ {ν : Measure (RingSpace d β) | Good ν ∧
        ∃ s ∈ Icc (0 : ℝ) t, R < ‖cycWalk ν 0 0 s - 0‖}} := by
    rintro ω ⟨hg, s, hs, hR⟩
    refine ⟨good_shiftEnv hg, s, hs, ?_⟩
    rw [cycWalk_shiftEnv hg u q hs.1, sub_zero]; exact hR
  refine (measure_mono hsub).trans ?_
  rw [prob_shiftEnv_eq hν u q hB]
  exact gb2_prob_zero hN ht hσ hε hl hlR hC

end ElboimSly.Paper.Heavy
