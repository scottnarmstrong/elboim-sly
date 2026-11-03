/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es5IntAe
public import ElboimSly.Paper.Heavy.RegenAdapted
public import ElboimSly.Paper.Heavy.EscMeas
public import Mathlib

/-!
# `heavyEscVersion` is `π_{B'}` on `{ξ_{B'} ≤ t_n}` (steps 5b and 5c of interface with S6)

Interface with S6 (proof).

* `heavyBlock_eq_escBlock`: the blocks of §6 (`⌊x / 2^m⌋ = ι`) are those of §5 (corner `2^m ι`).
* `heavyEscVersion_ae_eq_escPi`: almost surely on `{ξ_{B'} ≤ t_n}`,
  `P(ℰ(ξ_{B'}) | ℱ_{ξ_{B'}}) = π_{B'}`.  The event `{ξ ≤ t_n}` lies in `ℱ_ξ`, and `ℱ_ξ`, `ℱ_{ξ∧t_n}`
  have the same trace on it (`condExp_min_stopping_time_ae_eq_restrict_le_const`); the indicators
  `1_{ℰ(ξ)}` and `1_{ℰ(ξ) ∩ {ξ ≤ t_n}}` give the same conditional expectation on `{ξ ≤ t_n}`
  (`condExp_indicator`); finally `resPhi_toReal_ae_eq_condExp` and `escPi_ae_eq_resPhi`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Paper.Heavy

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
  {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ (k + 2) β)}

omit [Fact (0 < β)] in
/-- The blocks of §6 are the blocks of §5 with corner `2^m ι`. -/
theorem heavyBlock_eq_escBlock (j : ℕ) (ι : Fin (k + 2) → ℤ) :
    heavyBlock j ι = escBlock j (fun c => 2 ^ j * ι c) := by
  ext x
  refine forall_congr' fun c => ?_
  have hp : (0 : ℤ) < 2 ^ j := by positivity
  constructor
  · intro h
    have h1 := Int.emod_nonneg (x c) hp.ne'
    have h2 := Int.emod_lt_of_pos (x c) hp
    have h3 := Int.mul_ediv_add_emod (x c) (2 ^ j)
    rw [h] at h3
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · have : x c / 2 ^ j < ι c + 1 := (Int.ediv_lt_iff_lt_mul hp).2 (by nlinarith)
      omega
    · exact (Int.le_ediv_iff_mul_le hp).2 (by nlinarith)

/-- A stopping-time σ-algebra depends only on the function. -/
theorem isStoppingTime_measurableSpace_congr {f : Filtration ℝ≥0 mΩ} {τ τ' : Ω → WithTop ℝ≥0}
    (h : τ = τ') (a : IsStoppingTime f τ) (b : IsStoppingTime f τ') :
    a.measurableSpace = b.measurableSpace := by
  subst h; rfl

/-- **Steps 5b/5c.**  Almost surely on `{ξ_{B'} ≤ t_n}`, the canonical version
`heavyEscVersion` of `P(ℰ(ξ_{B'}) | ℱ_{ξ_{B'}})` equals `π_{B'}`. -/
theorem heavyEscVersion_ae_eq_escPi (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (tn : ℝ)
    (hn : 0 < n) (ι : Fin (k + 2) → ℤ) :
    ∀ᵐ ω ∂Pr, heavyXi (avoidWalk (cycNgood N)) (heavyScaleJ n) ι ω ≤ ENNReal.ofReal tn →
      heavyEscVersion (avoidWalk_cycNgood_adapted S) Pr n ι ω =
        (escPi Pr N n (escJ n) tn (escBlock (escJ n) (fun c => 2 ^ escJ n * ι c)) ω).toReal := by
  classical
  have hPr := S.space.ppp.isProbabilityMeasure
  have hgood : ∀ᵐ ω ∂Pr, CycGood (N ω) := CycSchemeEnv.ae_cycGood' S.space.ppp
  set u : Fin (k + 2) → ℤ := fun c => 2 ^ escJ n * ι c with hu
  have hAd := avoidWalk_cycNgood_adapted S
  set W := avoidWalk (cycNgood N) with hW
  set j := heavyScaleJ n with hj
  have hBeq : heavyBlock j ι = escBlock (escJ n) u := heavyBlock_eq_escBlock j ι
  have hξ := hAd.isStoppingTime_entrance (heavyBlock j ι)
  set tnn : ℝ≥0 := tn.toNNReal with htnn
  set E := heavyEscSet W n j (heavyXi W j ι) with hE
  have hEm : MeasurableSet E := measurableSet_heavyEscSet hAd hξ.measurable' hn j
  set s : Set Ω := {ω | entranceTime (W ω) (heavyBlock j ι) ≤ ((tnn : ℝ≥0) : WithTop ℝ≥0)} with hs
  have hsm : MeasurableSet[hξ.measurableSpace] s := hξ.measurableSet_le' tnn
  have hsm0 : MeasurableSet s := hξ.measurableSpace_le _ hsm
  -- the tower of conditional expectations
  have hf1 : Integrable (E.indicator fun _ => (1 : ℝ)) Pr := (integrable_const 1).indicator hEm
  have c1 := condExp_indicator (μ := Pr) (m := hξ.measurableSpace) hf1 hsm
  have : IsFiniteMeasure (Pr.trim (hξ.min_const tnn).measurableSpace_le) :=
    isFiniteMeasure_trim _
  have c2 := condExp_min_stopping_time_ae_eq_restrict_le_const (μ := Pr)
    (f := s.indicator (E.indicator fun _ => (1 : ℝ))) hξ tnn
  have c2' := (ae_restrict_iff' hsm0).1 c2
  -- §5: the stopping time `T_B` and `Φ`
  have hT := isStoppingTime_escTg S tn u
  have hfin : Pr {ω | escTg N tn n u ω ≠ ⊤} = 1 := by
    have : {ω | escTg N tn n u ω ≠ ⊤} = univ := by
      ext ω; simp [escTg_ne_top]
    rw [this]; exact measure_univ
  have hCond := resPhi_toReal_ae_eq_condExp (regPlan (k + 2) β) 𝒢₀ S.space.ppp S.space.ppp'
    S.space.indep S.space.indep' hK_regPlan S.space.le hT hfin
    (measurableSet_escYSet (β := β) tn hn u)
  have hTeq : escTg N tn n u = fun ω => min (entranceTime (W ω) (heavyBlock j ι))
      ((tnn : ℝ≥0) : WithTop ℝ≥0) := by
    rw [hBeq]; exact funext (escTg_eq_min N tn n u)
  have hms := isStoppingTime_measurableSpace_congr hTeq hT (hξ.min_const tnn)
  have hCond' : (fun ω => (resPhi (regPlan (k + 2) β) Pr N (escTg N tn n u)
      (escYSet (β := β) tn n u) ω).toReal) =ᵐ[Pr]
      Pr[(N ⁻¹' escYSet (β := β) tn n u).indicator (fun _ => (1 : ℝ)) |
        (hξ.min_const tnn).measurableSpace] := by
    exact hCond.trans (Filter.EventuallyEq.of_eq (congrArg (fun m : MeasurableSpace Ω =>
      Pr[(N ⁻¹' escYSet (β := β) tn n u).indicator (fun _ => (1 : ℝ)) | m]) hms))
  have hA := escPi_ae_eq_resPhi S tn hn u
  -- the indicators agree almost surely
  have hind : (N ⁻¹' escYSet (β := β) tn n u).indicator (fun _ => (1 : ℝ)) =ᵐ[Pr]
      s.indicator (E.indicator fun _ => (1 : ℝ)) := by
    filter_upwards [hgood] with ω hω
    have hWω : W ω = escWalk (N ω) := by
      show escWalk (cycNgood N ω) = escWalk (N ω)
      rw [cycNgood_of_good hω]
    have hxi : heavyXi W j ι ω = escXi (escWalk (N ω)) (escBlock (escJ n) u) := by
      show entranceTime (W ω) (heavyBlock j ι) = _
      rw [hWω, hBeq, escXi_eq_entranceTime]
    have hiff : ω ∈ N ⁻¹' escYSet (β := β) tn n u ↔ ω ∈ s ∩ E := by
      simp only [mem_preimage, escYSet, mem_ofPred_eq, mem_inter_iff, hs, hE, heavyEscSet]
      rw [show entranceTime (W ω) (heavyBlock j ι) = heavyXi W j ι ω from rfl, hxi, hWω]
      constructor
      · rintro ⟨-, h1, h2⟩
        exact ⟨h1, ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1, h2⟩
      · rintro ⟨h1, -, h2⟩
        exact ⟨hω, h1, h2⟩
    by_cases hm : ω ∈ s ∩ E
    · rw [Set.indicator_of_mem (hiff.2 hm), Set.indicator_of_mem hm.1,
        Set.indicator_of_mem hm.2]
    · have hm' : ω ∉ N ⁻¹' escYSet (β := β) tn n u := fun h => hm (hiff.1 h)
      rw [Set.indicator_of_notMem hm']
      by_cases h1 : ω ∈ s
      · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem (fun h2 => hm ⟨h1, h2⟩)]
      · rw [Set.indicator_of_notMem h1]
  have hind' := condExp_congr_ae (m := (hξ.min_const tnn).measurableSpace) hind
  filter_upwards [c1, c2', hCond', hA, hind'] with ω e1 e2 e3 e4 e5 hωs
  have hωs' : ω ∈ s := hωs
  have h1 : heavyEscVersion hAd Pr n ι ω =
      Pr[s.indicator (E.indicator fun _ => (1 : ℝ)) | hξ.measurableSpace] ω := by
    unfold heavyEscVersion
    rw [e1, Set.indicator_of_mem hωs']
  rw [h1, ← e2 hωs', ← e5, ← e3, e4]

end ElboimSly.Paper.Escape
