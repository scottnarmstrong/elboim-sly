/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es5IntMeas
public import ElboimSly.Paper.Escape.Es5IntCond
public import ElboimSly.Paper.Escape.Es52StopT
public import ElboimSly.Paper.Escape.Es52Refl7
public import Mathlib

/-!
# `π_B` is the canonical version `Φ_{ℰ}(ρ_T)` (step 5a of interface with S6)

Interface with S6 (proof), first entrance times and the escape stopping time, resampling formula (b).

* `escYg_eq_indicator`: `Y_B` restricted to good environments is the indicator of `escYSet`.
* `escPi_ae_eq_resPhi`: almost surely, `escPi = Φ_{escYSet}(ρ_T)` (so `escPi = escPiG` almost
  surely).  The point is that `ν ↦ RM(ρ_T) + ν|_{S ∖ R_T}` is good for `Π_μ`-almost every `ν`,
  because `Φ_{bad}(ρ_T) = P(N bad | ℱ_T) = 0` almost surely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
  {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ (k + 2) β)}

theorem escYg_eq_indicator (n : ℕ) (tn : ℝ) (u : Fin (k + 2) → ℤ) :
    escYg (β := β) n tn u = (escYSet (β := β) tn n u).indicator (fun _ => (1 : ℝ≥0∞)) := by
  funext ν
  unfold escYg escY
  by_cases hν : CycGood ν
  · by_cases h : escXi (escWalk ν) (escBlock (escJ n) u) ≤ ENNReal.ofReal tn ∧
        EscEvent n (escJ n) (escWalk ν) (escXi (escWalk ν) (escBlock (escJ n) u)).toReal
    · have hm : ν ∈ escYSet (β := β) tn n u := ⟨hν, h⟩
      simp [hν, h, hm]
    · have hm : ν ∉ escYSet (β := β) tn n u := fun hm => h hm.2
      simp [hν, h, hm]
  · have hm : ν ∉ escYSet (β := β) tn n u := fun hm => hν hm.1
    simp [hν, hm]

theorem resPhi_le_one (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (T : Ω → WithTop ℝ≥0)
    (X : Set (Measure (CycS ℕ (k + 2) β))) (ω : Ω) :
    resPhi (regPlan (k + 2) β) Pr N T X ω ≤ 1 := by
  have hPr := S.space.ppp.isProbabilityMeasure
  unfold resPhi resampleProb
  have : IsProbabilityMeasure (Pr.map N) :=
    (Measure.isProbabilityMeasure_map_iff S.space.ppp.measurable.aemeasurable).2 hPr
  exact prob_le_one

/-- **Step 5a.** Almost surely `π_B = Φ_{escYSet}(ρ_T)`, the canonical version of
`P(N ∈ escYSet | ℱ_T)`, `T = ξ_B ∧ t_n` (from the good version of the environment). -/
theorem escPi_ae_eq_resPhi (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (tn : ℝ)
    (hn : 0 < n) (u : Fin (k + 2) → ℤ) :
    ∀ᵐ ω ∂Pr, escPi Pr N n (escJ n) tn (escBlock (escJ n) u) ω =
      resPhi (regPlan (k + 2) β) Pr N (escTg N tn n u) (escYSet (β := β) tn n u) ω := by
  have hPr := S.space.ppp.isProbabilityMeasure
  have hgood : ∀ᵐ ω ∂Pr, CycGood (N ω) := CycSchemeEnv.ae_cycGood' S.space.ppp
  have hT := isStoppingTime_escTg S tn u
  have hfin : Pr {ω | escTg N tn n u ω ≠ ⊤} = 1 := by
    have : {ω | escTg N tn n u ω ≠ ⊤} = univ := by
      ext ω; simp [escTg_ne_top]
    rw [this]; exact measure_univ
  have hbadm : MeasurableSet {ν : Measure (CycS ℕ (k + 2) β) | ¬ CycGood ν} :=
    measurableSet_cycGood.compl
  have hc := resPhi_toReal_ae_eq_condExp (regPlan (k + 2) β) 𝒢₀ S.space.ppp S.space.ppp'
    S.space.indep S.space.indep' hK_regPlan S.space.le hT hfin hbadm
  have hind : ((N ⁻¹' {ν : Measure (CycS ℕ (k + 2) β) | ¬ CycGood ν}).indicator
      (fun _ => (1 : ℝ))) =ᵐ[Pr] 0 := by
    filter_upwards [hgood] with ω hω
    simp [Set.indicator, hω]
  have hz := (condExp_congr_ae (m := hT.measurableSpace) hind).trans
    (Filter.EventuallyEq.of_eq (condExp_zero (m := hT.measurableSpace) (μ := Pr)))
  have hres0 : ∀ᵐ ω ∂Pr, resPhi (regPlan (k + 2) β) Pr N (escTg N tn n u)
      {ν | ¬ CycGood ν} ω = 0 := by
    filter_upwards [hc, hz] with ω h1 h2
    have h3 : (resPhi (regPlan (k + 2) β) Pr N (escTg N tn n u) {ν | ¬ CycGood ν} ω).toReal = 0 := by
      rw [h1]; exact h2
    rcases (ENNReal.toReal_eq_zero_iff _).1 h3 with h | h
    · exact h
    · exact absurd h (ne_top_of_le_ne_top ENNReal.one_ne_top (resPhi_le_one S _ _ ω))
  filter_upwards [hgood, hres0] with ω hω h0
  have hTeq : escT N tn (escBlock (escJ n) u) ω = escTg N tn n u ω := by
    show _ = ((escT0 β tn n u (cycNgood N ω) : ℝ≥0) : WithTop ℝ≥0)
    rw [cycNgood_of_good hω]; rfl
  have e1 : escPi Pr N n (escJ n) tn (escBlock (escJ n) u) ω =
      resampleInt (regPlan (k + 2) β) Pr N (escTg N tn n u)
        (fun p => escY n (escJ n) tn (escBlock (escJ n) u) p.2) ω := by
    simp only [escPi, resampleInt, cycRecStop, cycRegionStop, SRW.stopReal, hTeq]
  rw [e1]
  unfold resampleInt
  unfold resPhi resampleProb at h0 ⊢
  set rm := (cycRecStop (regPlan (k + 2) β) (cycNgood N) (escTg N tn n u) ω).rm β with hrm
  set R := cycRegionStop (regPlan (k + 2) β) (cycNgood N) (escTg N tn n u) ω with hR
  have hm : Measurable fun ν : Measure (CycS ℕ (k + 2) β) => rm + ν.restrict Rᶜ :=
    measurable_add_measure.comp (measurable_const.prodMk
      (measurable_restrict_set (measurableSet_cycRegionStop (regPlan (k + 2) β)
        (N := cycNgood N) (escTg N tn n u) ω).compl))
  have hae : ∀ᵐ ν ∂(Pr.map N), CycGood (rm + ν.restrict Rᶜ) := by
    rw [ae_iff]
    simpa using h0
  have hXm := measurableSet_escYSet (β := β) tn hn u
  have hind1 := lintegral_indicator_one (μ := Pr.map N) (hm hXm)
  refine Eq.trans ?_ hind1
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with ν hν
  have := congrFun (escYg_eq_indicator (β := β) n tn u) (rm + ν.restrict Rᶜ)
  simp only [escYg, ite_eq_left hν] at this
  rw [this]
  by_cases h : rm + ν.restrict Rᶜ ∈ escYSet (β := β) tn n u
  · have h' : ν ∈ (fun ν => rm + ν.restrict Rᶜ) ⁻¹' escYSet (β := β) tn n u := h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']; rfl
  · have h' : ν ∉ (fun ν => rm + ν.restrict Rᶜ) ⁻¹' escYSet (β := β) tn n u := h
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

end ElboimSly.Paper.Escape
