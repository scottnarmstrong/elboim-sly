/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenZ
public import ElboimSly.Foundations.Cyclic.CycMultiMain
public import ElboimSly.Foundations.Cyclic.CycPlanCoupling
public import ElboimSly.Foundations.Cyclic.CycPlanCouplingFilt
public import ElboimSly.Foundations.Cyclic.CycPlanCouplingRegenLaw
public import ElboimSly.Foundations.Cyclic.CycHitFreeze
public import ElboimSly.Foundations.Cyclic.CycContRegen
public import ElboimSly.Foundations.Cyclic.CycHitNull
public import Mathlib

/-!
# ES22 Lemma 2.1 (b): the environment `M` after the stopping time

ES22 Lemma 2.1 (b), proof, "Freezing". With
`Ñ_T = N|_{S∖R_T} + N'|_{R_T}`, `Z = (k_T, W(T), L_T)` (`regZ`) and the re-indexing `Sh_z`
(`cycShift`), the environment after `T` is `M = Sh_Z Ñ_T` on `{T < ∞}` and `M = N'` on
`{T = ∞}` (`regM`). For measurability `N`, `N'` are replaced by `τ(N)`, `τ(N')` (`regYtil`).
`regW ν` is the regenerated walk of the slices of `ν`, as a total measurable function of `ν`
(`regW_eq_regenWalk` for good `ν`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The regenerated walk of the slices of `ν`, as a total function (the first piece and the later
ones through `walkMap`). -/
noncomputable def regW (ν : Measure (ℕ × RingSpace d β)) : ℝ≥0 → Fin d → ℤ :=
  contGlue β.toNNReal (walkMap (cycSlice 0 ν)) (fun k => walkMap (cycSlice (k + 1) ν))

theorem measurable_regW : Measurable (regW : Measure (ℕ × RingSpace d β) → ℝ≥0 → Fin d → ℤ) := by
  have h1 : Measurable fun ν : Measure (ℕ × RingSpace d β) => walkMap (cycSlice 0 ν) :=
    (measurable_walkMap (d := d) (β := β)).comp (measurable_cycSlice (I := ℕ) (d := d) (β := β) 0)
  have h2 : Measurable fun ν : Measure (ℕ × RingSpace d β) =>
      fun k => walkMap (cycSlice (k + 1) ν) :=
    measurable_pi_iff.2 fun k =>
      (measurable_walkMap (d := d) (β := β)).comp
        (measurable_cycSlice (I := ℕ) (d := d) (β := β) (k + 1))
  have h3 := (measurable_contGlue_pair (d := d) β.toNNReal).comp (h1.prodMk h2)
  exact h3

theorem regW_eq_regenWalk {ν : Measure (ℕ × RingSpace d β)} (hν : CycGood ν) (t : ℝ≥0) :
    regW ν t = ElboimSly.regenWalk (slices ν) (t : ℝ) :=
  (regenWalk_eq_contGlue (ν := slices ν) hν t).symm

variable {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]

/-- `Z = (k_T, W(T), L_T)` (a total function: junk on `{T = ∞}`). -/
noncomputable def regZ (N : Ω → Measure (ℕ × RingSpace d β)) (T : Ω → WithTop ℝ≥0) (ω : Ω) :
    ShiftPar d :=
  recZ ((regPlan d β).junk) (cycRecStop (regPlan d β) (cycNgood N) T ω)

/-- `τ(Ñ_T)` for `Ñ_T = N|_{S∖R_T} + N'|_{R_T}`. -/
noncomputable def regYtil (N N' : Ω → Measure (ℕ × RingSpace d β)) (T : Ω → WithTop ℝ≥0)
    (ω : Ω) : Measure (ℕ × RingSpace d β) :=
  tildeMeasure (fun ω => tau (cycIntensity ℕ d β) (N ω))
    (fun ω => tau (cycIntensity ℕ d β) (N' ω)) (cycRegionStop (regPlan d β) (cycNgood N) T) ω

open scoped Classical in
/-- The environment `M` after the stopping time. -/
noncomputable def regM (N N' : Ω → Measure (ℕ × RingSpace d β)) (T : Ω → WithTop ℝ≥0) (ω : Ω) :
    Measure (ℕ × RingSpace d β) :=
  if T ω ≠ ⊤ then cycShift (regZ N T ω) (regYtil N N' T ω) else N' ω

variable {Pr : Measure Ω}
  {N N' : Ω → Measure (ℕ × RingSpace d β)}
  (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity ℕ d β) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)

theorem hK_regPlan' : 0 < (regPlan d β).K := by
  rw [regPlan_K]; exact ENat.top_pos

/-- `{T = ∞}` is almost surely a set of `𝒢₀ ∨ σ(N)`. -/
theorem exists_ae_top_set_multi (P : CycPlan ℕ d β) (h𝒢 : 𝒢₀ ≤ mΩ)
    (hNm : Measurable N) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hNm h𝒢 Pr) T) :
    ∃ t, MeasurableSet[𝒢₀ ⊔ MeasurableSpace.comap N inferInstance] t ∧
      {ω | T ω = ⊤} =ᵐ[Pr] t := by
  have hle : ∀ s, cycMultiFilt P 𝒢₀ hNm h𝒢 Pr s ≤
      aeSigma Pr (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) := by
    intro s
    refine (cycMultiFilt_le_X P 𝒢₀ hNm h𝒢 s).trans ?_
    refine sup_le (sup_le ?_ ?_) ?_
    · intro u hu
      exact ⟨u, (le_sup_left : 𝒢₀ ≤ 𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) u hu,
        Filter.EventuallyEq.rfl⟩
    · intro u hu
      exact ⟨u, (le_sup_right : MeasurableSpace.comap N inferInstance ≤
        𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) u hu, Filter.EventuallyEq.rfl⟩
    · refine MeasurableSpace.generateFrom_le fun u hu => ?_
      exact ⟨∅, @MeasurableSet.empty _ (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance),
        ae_eq_empty.2 hu.2⟩
  have hm : MeasurableSet[aeSigma Pr (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance)]
      {ω | T ω = ⊤} := by
    have : {ω | T ω = ⊤} = (⋃ n : ℕ, {ω | T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)})ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, not_exists, not_le]
      constructor
      · intro h n; rw [h]; exact WithTop.coe_lt_top _
      · intro h
        by_contra hne
        obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hne
        obtain ⟨n, hn⟩ := exists_nat_ge a
        have := h n
        rw [← ha] at this
        exact absurd (WithTop.coe_le_coe.2 hn) (not_le.2 this)
    rw [this]
    exact (MeasurableSet.iUnion fun n : ℕ => hle n _ (hT n)).compl
  exact hm

end ElboimSly.Cyclic

end
