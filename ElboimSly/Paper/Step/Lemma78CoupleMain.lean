/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78CoupleCond
public import ElboimSly.Foundations.Cyclic.CycPlanCoupling
public import ElboimSly.Foundations.Cyclic.CycPlanCouplingRegenLaw
public import Mathlib

/-!
# `W₂` after `ζ_i`, given `ℱ⁺_{ζ_i}`

W_2 after zeta_i, given ℱ^+_zeta_i. For a stopping time `T = t'_n + ζ` of the exploration filtration of
the plan `𝔭₈` (`step78Plan`), the regenerated walk `W'` of plan-level coupling after a stopping time (d) is
independent of `ℱ_T`, and on `{ζ < ∞}`, for every `s` with `ζ + s ≤ b`, where
`b = thit^{(2)}(ζ) ∧ treg^{(2)} ∧ inf {r ≥ ζ : d(W₂(r), V) ≤ 1}`,
`W₂(ζ + s) - W₂(ζ) = W'(s)`.

Here `W₂ = W^{N}_{u,q}` is read in the good version `cycNgood N` of the environment, which is
almost surely equal to `N`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

theorem step78_envWalk_of_good {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (CycS Unit d β)}
    (h : CycGood ν) (δ : CycData Unit d) : envWalk ν δ = envFn ν δ := by
  unfold envWalk
  rw [ite_eq_left h]

theorem step78_restrict_singleton {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    (N N' : Measure S) {R : Set S} {x : S} (hx : x ∉ R) :
    (N.restrict Rᶜ + N'.restrict R) {x} = N {x} := by
  rw [Measure.add_apply, Measure.restrict_apply (measurableSet_singleton x),
    Measure.restrict_apply (measurableSet_singleton x)]
  have h1 : ({x} : Set S) ∩ Rᶜ = {x} := by
    ext y; simp only [mem_inter_iff, mem_singleton_iff, mem_compl_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hx⟩⟩
  have h2 : ({x} : Set S) ∩ R = ∅ := by
    ext y; simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false]
    exact fun h => hx (h.1 ▸ h.2)
  rw [h1, h2]; simp

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0)
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS Unit d β)} {N'' : Ω → Measure (ℕ × RingSpace d β)}
  (hN : IsPoissonPointProcess N (cycIntensity Unit d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity Unit d β) Pr)
  (hN'' : IsPoissonPointProcess N'' ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)
  (hI3 : Indep (MeasurableSpace.comap N'' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ MeasurableSpace.comap N' inferInstance ⊔
      cycNull Pr) Pr)

/-- The stopping length `T = t'_n + ζ`. -/
noncomputable def step78T (Tn : ℝ≥0) (Z : Ω → WithTop ℝ≥0) : Ω → WithTop ℝ≥0 :=
  fun ω => (Tn : WithTop ℝ≥0) + Z ω

/-- The walk datum `δ = (1, W₂(ζ), q + ζ, +1)` of w_2 after zeta_i, given ℱ^+_zeta_i. -/
noncomputable def step78Delta (N : Ω → Measure (CycS Unit d β)) (u : Fin d → ℤ) (q : ℝ)
    (Z : Ω → WithTop ℝ≥0) : Ω → CycData Unit d :=
  fun ω => step78Datum u q (cycSlice () (cycNgood N ω)) (ElboimSly.SRW.stopReal Z ω)

/-- The time `b_i` of w_2 after zeta_i, given ℱ^+_zeta_i. -/
noncomputable def step78B (N : Ω → Measure (CycS Unit d β)) (u : Fin d → ℤ) (q : ℝ)
    (Tn : ℝ≥0) (Z : Ω → WithTop ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  min (min ((step78SliceData (cycNgood N) u q Tn 0 0).thit Z ω)
    ((step78SliceData (cycNgood N) u q Tn 0 0).treg ω))
    (step78FirstGe (step78SliceData (cycNgood N) u q Tn 0 0).nearSet1 Z ω)

include hN hN' hN'' hI1 hI2 hI3 in
/-- **w_2 after zeta_i, given ℱ^+_zeta_i.** -/
theorem step78_couple (h𝒢 : 𝒢₀ ≤ mΩ) {Z : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr)
      (step78T Tn Z))
    (hδ : Measurable[hT.measurableSpace] (step78Delta N u q Z)) :
    -- `W'` is independent of `ℱ_T`, with the law of the regenerated walk
    (∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A → ∀ {Γ : Set (ℝ≥0 → Fin d → ℤ)},
      MeasurableSet Γ →
      Pr (A ∩ {ω | step78T Tn Z ω ≠ ⊤} ∩
          {ω | contGlue β.toNNReal (planFirst (step78Plan d β u q Tn) N N' (step78T Tn Z)
            (step78Delta N u q Z) ω) (contSeq N'' ω) ∈ Γ}) =
        Pr (A ∩ {ω | step78T Tn Z ω ≠ ⊤}) *
          Pr {ω | (fun t : ℝ≥0 => ElboimSly.regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ)) ∈
            Γ}) ∧
    -- on `{ζ < ∞}`, `W₂(ζ + s) - W₂(ζ) = W'(s)` as long as `ζ + s ≤ b`
    (∀ᵐ ω ∂Pr, Z ω ≠ ⊤ → ∀ s : ℝ≥0, (Z ω + (s : WithTop ℝ≥0)) ≤ step78B N u q Tn Z ω →
      cycWalk (cycSlice () (cycNgood N ω)) u q ((ElboimSly.SRW.stopReal Z ω : ℝ) + s) -
          cycWalk (cycSlice () (cycNgood N ω)) u q (ElboimSly.SRW.stopReal Z ω) =
        contGlue β.toNNReal (planFirst (step78Plan d β u q Tn) N N' (step78T Tn Z)
          (step78Delta N u q Z) ω) (contSeq N'' ω) s) := by
  have hK : 0 < (step78Plan d β u q Tn).K := by
    show (0 : ℕ∞) < 2
    norm_num
  refine ⟨fun {A} hA {Γ} hΓ => ?_, ?_⟩
  · exact cyc_plan_coupling_regen_law (step78Plan d β u q Tn) 𝒢₀ hN hN' hN'' hI1 hI2 hI3 hK h𝒢
      hT hδ hA hΓ
  · have := hN.isProbabilityMeasure
    set P := step78Plan d β u q Tn with hP
    set T := step78T Tn Z with hTdef
    obtain ⟨-, -, -, -, -, hfresh, -⟩ := cyc_multi_exploration_a P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT
    have hgoodN := CycSchemeEnv.ae_cycGood' hN
    have hgoodTilde : ∀ᵐ ω ∂Pr, T ω ≠ ⊤ →
        CycGood (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) := by
      have hFm : MeasurableSet {ν : Measure (CycS Unit d β) | ¬ CycGood ν} :=
        measurableSet_cycGood.compl
      have h0 := hfresh MeasurableSet.univ hFm
      have h1 : (Pr.map N) {ν : Measure (CycS Unit d β) | ¬ CycGood ν} = 0 := by
        rw [Measure.map_apply hN.measurable hFm]
        exact measure_eq_zero_iff_ae_notMem.2 (hgoodN.mono fun ω h hn => hn h)
      rw [h1, mul_zero] at h0
      have := measure_eq_zero_iff_ae_notMem.1 h0
      filter_upwards [this] with ω hω hTω
      by_contra hng
      exact hω ⟨⟨mem_univ _, hTω⟩, hng⟩
    filter_upwards [hgoodTilde, ae_cycNgood_eq hN] with ω hgT hNg hZ s hs
    set ζ : ℝ≥0 := ElboimSly.SRW.stopReal Z ω with hζ
    have hZζ : Z ω = (ζ : WithTop ℝ≥0) := by
      cases hz : Z ω with
      | top => exact absurd hz hZ
      | coe a =>
        have : ζ = a := by simp only [hζ, ElboimSly.SRW.stopReal, hz]; rfl
        rw [this]
    have hTω : T ω = ((Tn + ζ : ℝ≥0) : WithTop ℝ≥0) := by
      simp only [hTdef, step78T, hZζ]
      rfl
    have hTne : T ω ≠ ⊤ := by rw [hTω]; exact WithTop.coe_ne_top
    have hgT' := hgT hTne
    have hsb : ((ζ + s : ℝ≥0) : WithTop ℝ≥0) ≤ step78B N u q Tn Z ω := by
      rw [hZζ, ← WithTop.coe_add] at hs
      exact hs
    obtain ⟨h12, h3⟩ := le_min_iff.1 hsb
    obtain ⟨h1, h2⟩ := le_min_iff.1 h12
    have hnear := step78_cond_near (N := cycNgood N) (u := u) (q := q) (Tn := Tn) (n := 0)
      (ρ := 0) ω Z ζ s hZζ h3
    have hthit := step78_cond_thit (N := cycNgood N) (u := u) (q := q) (Tn := Tn) (n := 0)
      (ρ := 0) ω Z ζ s hZζ h1
    have hreg := step78_cond_treg (N := cycNgood N) (u := u) (q := q) (Tn := Tn) (n := 0)
      (ρ := 0) ω ζ s h2
    have hν : CycGood (cycNgood N ω) := cycGood_cycNgood N ω
    set ν := cycNgood N ω with hνdef
    -- the explored region
    have hRg : cycRegionStop P (cycNgood N) T ω =
        (CycRec.trunc (Tn + ζ) (P.envFinal ν)).region β := by
      simp only [cycRegionStop, hTω, cycRegionAt]
      rfl
    have hag : ∀ x : CycS Unit d β,
        x ∉ (CycRec.trunc (Tn + ζ) (P.envFinal ν)).region β →
          ν {x} =
            (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) {x} := by
      intro x hx
      rw [← hRg] at hx
      simp only [tildeMeasure]
      rw [step78_restrict_singleton _ _ hx]
      exact congrArg (fun m => m {x}) hNg
    have hdet := step78_agree_det hν hgT' P.junk u q Tn ζ s hnear hthit hag
    have hβ : 0 < β := Fact.out
    have hpf : ∀ s' : ℝ≥0, s' ≤ s → planFirst P N N' T (step78Delta N u q Z) ω s' =
        cycWalk (cycSlice () ν) u q ((ζ : ℝ) + s') - cycWalk (cycSlice () ν) u q ζ := by
      intro s' hs'
      unfold planFirst
      rw [step78_envWalk_of_good hgT']
      have := hdet s' hs'
      exact congrArg (fun y => y - cycWalk (cycSlice () ν) u q ζ) this
    have hle : (s : ℝ≥0∞) ≤ pathTreg β.toNNReal
        (planFirst P N N' T (step78Delta N u q Z) ω) := by
      refine le_iInf fun kk => ?_
      obtain ⟨k, hk1, hk0⟩ := kk
      by_contra hlt
      rw [not_le, ENNReal.coe_lt_coe] at hlt
      have hlt' : (k : ℝ) * β < s := by
        have := NNReal.coe_lt_coe.2 hlt
        simpa [Real.coe_toNNReal _ hβ.le] using this
      have h0 := hpf ((k : ℝ≥0) * β.toNNReal) hlt.le
      rw [hk0] at h0
      have h0' : cycWalk (cycSlice () ν) u q ((ζ : ℝ) + ((k : ℝ≥0) * β.toNNReal : ℝ≥0)) =
          cycWalk (cycSlice () ν) u q ζ := by
        have := h0.symm
        rw [sub_eq_zero] at this
        exact this
      push_cast at h0'
      rw [Real.coe_toNNReal _ hβ.le] at h0'
      exact step78_no_close (hν ()) u q ζ s hthit hreg hk1 hlt' h0'
    have hglue := cyc_plan_coupling_regen_agree P (N'' := N'') T (step78Delta N u q Z) ω hle
    rw [hglue, hpf s le_rfl]

end ElboimSly.Paper.Step

end
