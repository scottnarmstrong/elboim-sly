/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Driven
public import ElboimSly.Paper.Step.DrivenCausal
public import ElboimSly.Paper.Step.RegenMeas
public import ElboimSly.Foundations.Cyclic.DrivenSrwShort
public import ElboimSly.Foundations.PPP.Existence
public import ElboimSly.Foundations.SRW.KernelDef
public import ElboimSly.Foundations.Cyclic.CycHitCoupleDrivenRegenLaw
public import ElboimSly.Foundations.Cyclic.CycDrivenRegenMeas
public import Mathlib

/-!
# The driven regenerated walk: law

The driven regenerated walk (b), (c), (d).

* (b) If `Y` is an SRW all of whose paths are driving paths, then `stepReg β (Y ω)` has the law of the
  regenerated walk (`stepReg_law`).
* (c) `w = x` on `[0, β)` and `σ₁ ≥ β` (`stepReg_eq_self_of_lt`, `le_stepSigma_one`).
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.SRW

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem toNNReal_pos' : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out

/-- Laws of regular-path valued maps push forward through a map that is measurable on regular
paths. -/
theorem map_comp_of_regular {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} {Y : Ω → PathSpace d} {Z : Ω' → PathSpace d} (hY : Measurable Y)
    (hZ : Measurable Z) (hYr : ∀ ω, IsRegPath (Y ω)) (hZr : ∀ ω, IsRegPath (Z ω))
    (hlaw : P.map Y = P'.map Z) (F : (ℝ≥0 → Fin d → ℤ) → (ℝ≥0 → Fin d → ℤ))
    (hF : Measurable fun x : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x} => F x.1) :
    P.map (fun ω => F (Y ω)) = P'.map (fun ω => F (Z ω)) := by
  have hYs : Measurable fun ω => (⟨Y ω, hYr ω⟩ : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x}) :=
    hY.subtype_mk
  have hZs : Measurable fun ω => (⟨Z ω, hZr ω⟩ : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x}) :=
    hZ.subtype_mk
  have m1 : Measurable fun ω => F (Y ω) := hF.comp hYs
  have m2 : Measurable fun ω => F (Z ω) := hF.comp hZs
  ext Γ hΓ
  rw [Measure.map_apply m1 hΓ, Measure.map_apply m2 hΓ]
  obtain ⟨Γ'', hΓ'', hEq⟩ := (MeasurableSpace.measurableSet_comap).1 (hF hΓ)
  have key : ∀ y, IsRegPath y → (y ∈ Γ'' ↔ F y ∈ Γ) := fun y hy => by
    have := Set.ext_iff.1 hEq ⟨y, hy⟩
    simpa using this
  have e1 : (fun ω => F (Y ω)) ⁻¹' Γ = Y ⁻¹' Γ'' := by
    ext ω; exact (key _ (hYr ω)).symm
  have e2 : (fun ω => F (Z ω)) ⁻¹' Γ = Z ⁻¹' Γ'' := by
    ext ω; exact (key _ (hZr ω)).symm
  rw [e1, e2, ← Measure.map_apply hY hΓ'', ← Measure.map_apply hZ hΓ'', hlaw]

/-- The driven regenerated walk (b). -/
theorem stepReg_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}
    (hY : IsSRW P Y) (hYp : ∀ ω, Y ω ∈ StepPath d)
    {Ωe : Type*} [MeasurableSpace Ωe] {Pe : Measure Ωe} {N : Ωe → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe) :
    P.map (fun ω (t : ℝ≥0) => stepReg β (Y ω) t) =
      Pe.map (fun ω (t : ℝ≥0) => regenWalk (fun k => copyEnv (N ω) k) (t : ℝ)) := by
  have hb : 0 < β.toNNReal := toNNReal_pos'
  obtain ⟨Ω', _, Pd, N₀, hPd, hN₀, -⟩ := exists_isPoissonPointProcess (clockIntensity (Dir d))
  have hZ := canonical_isSRW hN₀
  have hΦ : Measurable fun x : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x} =>
      drivenRegenFrom β.toNNReal x.1 :=
    measurable_pi_iff.2 (measurable_drivenRegenFrom_subtype hb)
  have h1 := map_comp_of_regular (P := P) (P' := Pd) hY.1 hZ.1 (fun ω => (hYp ω).toIsRegPath)
    (fun ω => walkPath_isRegPath (N₀ ω)) ((SRW.IsSRW.map_eq_model hY).trans (SRW.IsSRW.map_eq_model hZ).symm)
    (drivenRegenFrom β.toNNReal) hΦ
  simp only [copyEnv_eq_cycSlice]
  exact h1.trans (law_drivenRegenFrom hN hN₀)

/-- The driven regenerated walk (c), for a coincidence-free driving path (the case used in
the proofs; the regeneration time `σ₁` is `drivenTreg`): `σ₁ ≥ β` and `w = x` on `[0, β]`.
For a coincidence-free path this includes the endpoint `β`. -/
theorem stepReg_no_interaction {x : ℝ≥0 → Fin d → ℤ} (hx : x ∈ StepCF (d := d) β) :
    ((β.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ stepSigma β x 1 ∧
      ∀ s ≤ β.toNNReal, stepReg β x s = x s := by
  have hb : 0 < β.toNNReal := toNNReal_pos'
  obtain ⟨h1, h2⟩ := drivenWalk_eq_self_of_cycCF hx hb
  refine ⟨by simpa [stepSigma, drivenSigma_one] using h1, fun s hs => ?_⟩
  have hlt : ((s : ℝ≥0) : ℝ≥0∞) ≤ drivenTreg β.toNNReal x := (ENNReal.coe_le_coe.2 hs).trans h1
  rw [stepReg, drivenRegenFrom_eq_walk_of_le hb hx.1.toIsRegPath hlt]
  exact h2 s hs

/-- The driven regenerated walk (e): for the canonical SRW and fixed `a ≥ 0`,
`θ_a X ∈ CF_β` almost surely. -/
theorem ae_stepShift_mem_stepCF {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {N₀ : Ω → Measure (Dir d × ℝ)} (hN₀ : IsPoissonPointProcess N₀ (clockIntensity (Dir d)) P)
    (a : ℝ≥0) : ∀ᵐ ω ∂P, stepShift a (canonical d N₀ ω) ∈ StepCF (d := d) β :=
  ae_shiftPath_mem_cycCF hN₀ β.toNNReal toNNReal_pos' a

end ElboimSly.Paper
