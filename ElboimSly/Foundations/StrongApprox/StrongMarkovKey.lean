/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.DyadicStop
public import ElboimSly.Foundations.StrongApprox.ExitMeas
public import ElboimSly.Foundations.Brownian.DimOne
public import Mathlib

/-!
# Strong Markov property: the finite-dimensional identity

Strong Markov property at stopping times of the natural filtration, Steps 0--2 (Part II).

For a standard real Brownian motion `β` and a stopping time `τ` of its natural filtration with
`τ < ∞` a.s., and `A` in the stopped `σ`-algebra, every bounded continuous `f` of finitely many
coordinates of the shifted process `β'` satisfies
`E[1_A f(β')] = P(A) E[f(β)]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {β : ℝ≥0 → Ω → ℝ}

omit mΩ in
lemma realFiltration_mono (β : ℝ≥0 → Ω → ℝ) : Monotone (realFiltration β) :=
  fun _ _ h => iSup₂_le fun s hs => le_iSup₂_of_le s (hs.trans h) le_rfl

lemma realFiltration_le (hβ : ∀ t, Measurable (β t)) (a : ℝ≥0) : realFiltration β a ≤ mΩ :=
  iSup₂_le fun s _ => (hβ s).comap_le

omit mΩ in
lemma measurable_realFiltration {s a : ℝ≥0} (h : s ≤ a) :
    Measurable[realFiltration β a] (β s) := by
  intro t ht
  exact (le_iSup₂_of_le s h le_rfl :
    MeasurableSpace.comap (β s) inferInstance ≤ realFiltration β a) _ ⟨t, ht, rfl⟩

lemma isProcess_of_realBM [IsProbabilityMeasure P] (h : IsStandardRealBM β P) :
    IsProcess β :=
  ⟨fun ω => ((isStandardRealBM_iff.1 h).2.1 ω), (isStandardRealBM_iff.1 h).1⟩

lemma measurable_of_stopping {τ : Ω → ℝ≥0∞} {β : ℝ≥0 → Ω → ℝ} (hβ : ∀ t, Measurable (β t))
    (hτ : ∀ t : ℝ≥0, MeasurableSet[realFiltration β t] {ω | τ ω ≤ t}) : Measurable τ := by
  refine measurable_of_Iic fun x => ?_
  induction x using ENNReal.recTopCoe with
  | top => simp
  | coe t => exact realFiltration_le hβ t _ (hτ t)

/-- Strong Markov property at stopping times of the natural filtration, Step 2. -/
theorem lintegral_stopped_shift [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P)
    {τ : Ω → ℝ≥0∞} (hτ : ∀ t : ℝ≥0, MeasurableSet[realFiltration β t] {ω | τ ω ≤ t})
    (hfin : ∀ᵐ ω ∂P, τ ω < ⊤) {A : Set Ω} (hAm : MeasurableSet A)
    (hA : ∀ t : ℝ≥0, MeasurableSet[realFiltration β t] (A ∩ {ω | τ ω ≤ t}))
    (I : Finset ℝ≥0) (f : (I → ℝ) →ᵇ ℝ≥0) :
    ∫⁻ ω, A.indicator (fun ω => (f (fun i : I => procShift τ β i ω) : ℝ≥0∞)) ω ∂P =
      P A * ∫⁻ ω, (f (fun i : I => β i ω) : ℝ≥0∞) ∂P := by
  have hproc : IsProcess β := isProcess_of_realBM hβ
  have hτm : Measurable τ := measurable_of_stopping hproc.2 hτ
  set c : ℝ≥0∞ := ∫⁻ ω, (f (fun i : I => β i ω) : ℝ≥0∞) ∂P with hc
  -- the functional `Φ`
  have hrestr : Measurable fun w : ℝ≥0 → ℝ => (fun i : I => w i) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply (i : ℝ≥0)
  have hΦm : Measurable fun w : ℝ≥0 → ℝ => (f (fun i : I => w i) : ℝ≥0∞) :=
    (measurable_coe_nnreal_ennreal).comp (f.continuous.measurable.comp hrestr)
  have hpath : Measurable (realPath β : Ω → ℝ≥0 → ℝ) :=
    measurable_pi_iff.2 fun t => hproc.2 t
  have hcw : ∫⁻ w, (f (fun i : I => w i) : ℝ≥0∞) ∂realWiener = c := by
    rw [← hβ.map_realPath, lintegral_map hΦm hpath]
    rfl
  -- Step A: the discrete identity
  have stepA : ∀ n : ℕ, ∫⁻ ω, A.indicator
      (fun ω => (f (fun i : I => procShift (fun ω => dyadic n (τ ω)) β i ω) : ℝ≥0∞)) ω ∂P =
        P A * c := by
    intro n
    set τn : Ω → ℝ≥0∞ := fun ω => dyadic n (τ ω) with hτn
    have hτnm : Measurable τn := (measurable_dyadic n).comp hτm
    have hτnfin : ∀ᵐ ω ∂P, τn ω < ⊤ := hfin.mono fun ω h => (dyadic_lt_top_iff n _).2 h
    set T : Set ℝ≥0 := Set.range (fun m : ℕ => ((m + 1 : ℕ) : ℝ≥0) / 2 ^ n) with hT
    have hTc : T.Countable := Set.countable_range _
    have hτT : ∀ ω, τn ω ≠ ⊤ → ∃ a ∈ T, τn ω = a := by
      intro ω h
      have hlt : τ ω < ⊤ := (dyadic_lt_top_iff n _).1 (lt_top_iff_ne_top.2 h)
      lift τ ω to ℝ≥0 using hlt.ne with t ht
      refine ⟨_, ⟨⌊(2 : ℝ≥0) ^ n * t⌋₊, rfl⟩, ?_⟩
      simp only [hτn]
      rw [← ht, dyadic_coe]
    have hτ' : ∀ a ∈ T, MeasurableSet[realFiltration β a] {ω | τn ω = a} := by
      rintro a ⟨m, rfl⟩
      have := measurableSet_inter_dyadic_eq (realFiltration_mono β) hτ (A := Set.univ)
        (fun t => by simpa using hτ t) n m
      simpa using this
    have hE : ∀ a ∈ T, MeasurableSet[realFiltration β a] (A ∩ {ω | τn ω = a}) := by
      rintro a ⟨m, rfl⟩
      exact measurableSet_inter_dyadic_eq (realFiltration_mono β) hτ hA n m
    have key := hβ.lintegral_discrete_stopping hTc hτT hτ' hE
      (Φ := fun _ w => (f (fun i : I => w i) : ℝ≥0∞))
      (hΦm.comp measurable_snd)
    simp only [hcw] at key
    have hnull : P {ω | τn ω < ⊤}ᶜ = 0 := ae_iff.1 hτnfin
    have hSm : MeasurableSet {ω | τn ω < ⊤} := hτnm measurableSet_Iio
    have h1 : ∫⁻ ω, A.indicator
        (fun ω => (f (fun i : I => procShift τn β i ω) : ℝ≥0∞)) ω ∂P =
        ∫⁻ ω, (A ∩ {ω | τn ω < ⊤}).indicator
          (fun ω => (f (fun i : I => procShift τn β i ω) : ℝ≥0∞)) ω ∂P := by
      refine lintegral_congr_ae (hτnfin.mono fun ω h => ?_)
      by_cases hω : ω ∈ A
      · have : ω ∈ A ∩ {ω | τn ω < ⊤} := ⟨hω, h⟩
        rw [Set.indicator_of_mem hω, Set.indicator_of_mem this]
      · have : ω ∉ A ∩ {ω | τn ω < ⊤} := fun h' => hω h'.1
        rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem this]
    have h2 : ∫⁻ ω, (A ∩ {ω | τn ω < ⊤}).indicator
          (fun ω => (f (fun i : I => procShift τn β i ω) : ℝ≥0∞)) ω ∂P =
        ∫⁻ ω, (A ∩ {ω | τn ω < ⊤}).indicator
          (fun ω => (f (fun i : I => realShift β (τn ω).toNNReal ω i) : ℝ≥0∞)) ω ∂P := by
      refine lintegral_congr fun ω => ?_
      by_cases hω : ω ∈ A ∩ {ω | τn ω < ⊤}
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        have : (fun i : I => procShift τn β i ω) =
            fun i : I => realShift β (τn ω).toNNReal ω i := by
          funext i
          have hne : dyadic n (τ ω) ≠ ⊤ := hω.2.ne
          simp [procShift, shiftAt_apply, hτn, hne, realShift]
        rw [this]
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
    rw [h1, h2, key, lintegral_indicator_const (hAm.inter hSm), measure_inter_conull hnull,
      mul_comm]
  -- Step B: pass to the limit
  set τn : ℕ → Ω → ℝ≥0∞ := fun n ω => dyadic n (τ ω) with hτn
  have hτnm : ∀ n, Measurable (τn n) := fun n => (measurable_dyadic n).comp hτm
  have hG : ∀ n, Measurable fun ω => A.indicator
      (fun ω => (f (fun i : I => procShift (τn n) β i ω) : ℝ≥0∞)) ω := by
    intro n
    refine Measurable.indicator ?_ hAm
    refine measurable_coe_nnreal_ennreal.comp (f.continuous.measurable.comp ?_)
    exact measurable_pi_iff.2 fun i => (hproc.shift (hτnm n)).2 i
  obtain ⟨B, hB⟩ : ∃ B : ℝ≥0, ∀ x, f x ≤ B := by
    obtain ⟨C, hC⟩ := f.bounded
    refine ⟨f 0 + C.toNNReal, fun x => ?_⟩
    have h1 := hC x 0
    rw [NNReal.dist_eq] at h1
    have h2 : (f x : ℝ) ≤ f 0 + C := by linarith [(abs_le.1 h1).2]
    rw [← NNReal.coe_le_coe]
    push_cast
    exact h2.trans (by linarith [Real.le_coe_toNNReal C])
  have hbound : ∀ n, (fun ω => A.indicator
      (fun ω => (f (fun i : I => procShift (τn n) β i ω) : ℝ≥0∞)) ω) ≤ᵐ[P]
      fun _ => (B : ℝ≥0∞) := by
    intro n
    refine Eventually.of_forall fun ω => ?_
    beta_reduce
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      exact_mod_cast hB _
    · rw [Set.indicator_of_notMem hω]; exact zero_le
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => A.indicator
      (fun ω => (f (fun i : I => procShift (τn n) β i ω) : ℝ≥0∞)) ω) atTop
      (nhds (A.indicator (fun ω => (f (fun i : I => procShift τ β i ω) : ℝ≥0∞)) ω)) := by
    filter_upwards [hfin] with ω h
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω]
      refine ENNReal.tendsto_coe.2 ((f.continuous.tendsto _).comp ?_)
      refine tendsto_pi_nhds.2 fun i => ?_
      have hc : Continuous fun t => β t ω := (hproc.1 ω).1
      have hd := dyadic_tendsto h
      have hfun : ∀ n, procShift (τn n) β i ω =
          β ((dyadic n (τ ω)).toNNReal + i) ω - β (dyadic n (τ ω)).toNNReal ω := by
        intro n
        have hne : dyadic n (τ ω) ≠ ⊤ := ((dyadic_lt_top_iff n _).2 h).ne
        simp [procShift, shiftAt_apply, hτn, hne]
      have hlim' : procShift τ β i ω =
          β ((τ ω).toNNReal + i) ω - β (τ ω).toNNReal ω := by
        simp [procShift, shiftAt_apply, h.ne]
      simp only [hfun, hlim']
      exact ((hc.tendsto _).comp (hd.add_const _)).sub ((hc.tendsto _).comp hd)
    · simp only [Set.indicator_of_notMem hω]
      exact tendsto_const_nhds
  have hdct := tendsto_lintegral_of_dominated_convergence (μ := P) (fun _ => (B : ℝ≥0∞))
    hG hbound (by simp) hlim
  have hdct' := hdct.congr (fun n => stepA n)
  exact tendsto_nhds_unique hdct' tendsto_const_nhds

end ElboimSly.StrongApprox
