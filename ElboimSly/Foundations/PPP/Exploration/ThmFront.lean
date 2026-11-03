/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ThmLawInf
import Mathlib

/-!
# Sequential first-point exploration: the front

Sequential first-point exploration (f), first part: almost surely `V_k(S) ∈ {0, 1}` and
`R̃_k(H_k, ·) = ρ_k` holds `V_k`-a.e.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U] {μ : Measure S}
  [SigmaFinite μ] {R : S → ℝ≥0∞} {h : ℝ≥0} {W : Measure (Measure S)}

/-- Almost surely `V(S) ∈ {0, 1}`. -/
theorem ae_V_univ_zero_or_one (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) :
    ∀ᵐ ν ∂W, probeV μ R h ν Set.univ = 0 ∨ probeV μ R h ν Set.univ = 1 := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ h) with h0 | hh
  · subst h0
    filter_upwards [ae_goodSet hW hP MeasurableSet.univ, ae_region_zero_eq_zero hW hP] with ν hν h0'
    refine Or.inl ?_
    rw [probeV_eq_zero_of_measure_zero hν.1 (by simpa using h0')]
    simp
  · filter_upwards [ae_succ_V_univ hW hP hh, ae_goodSet hW hP MeasurableSet.univ] with ν h1 hν
    by_cases hs : 1 ≤ tau μ ν (probeRegion R h)
    · exact Or.inr (h1 hs)
    · refine Or.inl ?_
      obtain ⟨hlf, hreg, -, -⟩ := hν
      obtain ⟨n, hn⟩ := hreg.2
      simp only [Set.inter_univ] at hn
      rw [tau_of_mem μ hlf, hn] at hs
      have : n = 0 := by
        by_contra hn0
        exact hs (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn0)
      rw [probeV_eq_zero_of_measure_zero hlf (by rw [hn, this]; simp)]
      simp

/-- Almost surely `R = ρ` holds `V`-a.e. -/
theorem ae_V_front (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) :
    ∀ᵐ ν ∂W, probeV μ R h ν {y | R y ≠ probeRho μ R h ν} = 0 := by
  have hR := hP.measurable
  filter_upwards [ae_goodSet hW hP MeasurableSet.univ] with ν hν
  obtain ⟨hlf, hreg, -, -⟩ := hν
  have hm : MeasurableSet {y | R y ≠ probeRho μ R h ν} :=
    (measurableSet_eq_fun hR measurable_const).compl
  unfold probeV
  rw [tau_of_mem μ hlf, Measure.restrict_apply hm]
  refine measure_mono_null (fun y hy => ?_) (measure_lt_rho_eq_zero hlf hreg)
  exact lt_of_le_of_ne hy.2 hy.1

namespace ExplRun

variable {sch : ExplScheme μ U} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  (run : ExplRun sch P)

include run

/-- If the section `{o | (η, o) ∈ B}` is `W`-null for every `η`, then almost surely the outcome of
step `k` avoids `B`. -/
theorem ae_last_not_mem {k : ℕ} {B : Set (Hist U S k × Outcome S)} (hB : MeasurableSet B)
    (h0 : ∀ η : Hist U S k, ∀ᵐ ν ∂(P.map run.N), (η, sch.stepAt k η ν) ∉ B) :
    ∀ᵐ ω ∂P, (run.H k ω, (run.H (k + 1) ω).last) ∉ B := by
  have := run.prob
  let g : Hist U S (k + 1) → ℝ≥0∞ := fun η' => B.indicator 1 (η'.init, η'.last)
  have hg : Measurable g := (measurable_one.indicator hB).comp
    ((Hist.measurable_init k).prodMk (Hist.measurable_last k))
  have h1 := run.stepLaw hg
  have h2 : ∀ η : Hist U S k, ∫⁻ o, g (η.snoc o) ∂(sch.kernelAt k η) = 0 := by
    intro η
    have : ∀ o : Outcome S, g (η.snoc o) = B.indicator 1 (η, o) := by
      intro o; simp [g]
    simp_rw [this]
    have hφ : Measurable fun o : Outcome S => B.indicator (1 : Hist U S k × Outcome S → ℝ≥0∞) (η, o) :=
      (measurable_one.indicator hB).comp (measurable_const.prodMk measurable_id)
    have hψ : Measurable fun ν : Measure S => sch.stepAt k η ν :=
      (sch.measurable_stepAt k).comp (measurable_const.prodMk measurable_id)
    rw [← sch.lintegral_stepAt run.isPPPLaw k η hφ]
    refine (lintegral_eq_zero_iff (f := fun ν => B.indicator (1 : Hist U S k × Outcome S → ℝ≥0∞)
      (η, sch.stepAt k η ν)) (hφ.comp hψ)).2 ?_
    filter_upwards [h0 η] with ν hν
    simp [Set.indicator_of_notMem hν]
  simp_rw [h2] at h1
  simp only [lintegral_zero] at h1
  have := (lintegral_eq_zero_iff (hg.comp (run.measurable_H (k + 1)))).1 h1
  filter_upwards [this] with ω hω hmem
  have hinit : (run.H (k + 1) ω).init = run.H k ω := sch.Hfun_init k _
  have : g (run.H (k + 1) ω) = 1 := by
    simp only [g, hinit]
    exact Set.indicator_of_mem hmem _
  simp only [Function.comp, Pi.zero_apply] at hω
  rw [this] at hω
  exact one_ne_zero hω

/-- Sequential first-point exploration (f): almost surely `V_k(S) ∈ {0, 1}`. -/
theorem ae_V_univ (k : ℕ) :
    ∀ᵐ ω ∂P, (run.H (k + 1) ω).last.2 Set.univ = 0 ∨ (run.H (k + 1) ω).last.2 Set.univ = 1 := by
  let B : Set (Hist U S k × Outcome S) := {q | q.2.2 Set.univ ≠ 0 ∧ q.2.2 Set.univ ≠ 1}
  have hm : Measurable fun q : Hist U S k × Outcome S => q.2.2 Set.univ :=
    (Measure.measurable_coe MeasurableSet.univ).comp (measurable_snd.comp measurable_snd)
  have hB : MeasurableSet B := (measurableSet_eq_fun hm measurable_const).compl.inter
    (measurableSet_eq_fun hm measurable_const).compl
  have := run.ae_last_not_mem (k := k) hB fun η => by
    filter_upwards [ae_V_univ_zero_or_one run.isPPPLaw (sch.isProbe_Rt k η)] with ν hν hmem
    rcases hν with h0 | h1
    · exact hmem.1 h0
    · exact hmem.2 h1
  filter_upwards [this] with ω hω
  by_contra hcon
  push Not at hcon
  exact hω hcon

/-- Sequential first-point exploration (f): almost surely `R̃_k(H_k, ·) = ρ_k` holds `V_k`-a.e. -/
theorem ae_front (k : ℕ) :
    ∀ᵐ ω ∂P, (run.H (k + 1) ω).last.2
      {y | sch.Rt k (run.H k ω) y ≠ (run.H (k + 1) ω).last.1} = 0 := by
  let Z : Set (((Hist U S k × ℝ≥0∞)) × S) := {p | sch.Rt k p.1.1 p.2 ≠ p.1.2}
  have hZ : MeasurableSet Z := (measurableSet_eq_fun
    ((sch.measurable_Rt k).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    (measurable_snd.comp measurable_fst)).compl
  let B : Set (Hist U S k × Outcome S) :=
    {q | 0 < tau μ q.2.2 {y | sch.Rt k q.1 y ≠ q.2.1}}
  have hB : MeasurableSet B := by
    have := measurable_tau_section μ hZ
    exact measurableSet_lt measurable_const (this.comp
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)))
  have := run.ae_last_not_mem (k := k) hB fun η => by
    filter_upwards [ae_V_front run.isPPPLaw (sch.isProbe_Rt k η)] with ν hν hmem
    have hlf : probeV μ (sch.Rt k η) (sch.h k η) ν ∈ lfSet μ := by
      unfold probeV; exact restrict_mem_lfSet (tau_mem_lfSet μ ν) _
    have : tau μ (sch.stepAt k η ν).2 {y | sch.Rt k η y ≠ (sch.stepAt k η ν).1} = 0 := by
      show tau μ (probeV μ (sch.Rt k η) (sch.h k η) ν) _ = 0
      rw [tau_of_mem μ hlf]; exact hν
    exact absurd hmem (by simp [B, this])
  filter_upwards [this] with ω hω
  have hlf : (run.H (k + 1) ω).last.2 ∈ lfSet μ := by
    have hl : (run.H (k + 1) ω).last = sch.stepAt k (sch.Hfun k (run.X ω)) (run.X ω).2 :=
      sch.Hfun_last k _
    rw [hl]
    show probeV μ _ _ _ ∈ lfSet μ
    unfold probeV; exact restrict_mem_lfSet (tau_mem_lfSet μ _) _
  by_contra hcon
  exact hω (by
    show 0 < tau μ _ _
    rw [tau_of_mem μ hlf]
    exact pos_iff_ne_zero.2 hcon)

end ExplRun

end ElboimSly
