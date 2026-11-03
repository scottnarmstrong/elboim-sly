/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.Identification
public import Mathlib

/-!
# Transfer of regular events from the cyclic walk to an SRW

Identification of the regenerated walk below β (b).

* `cycPath_prob_eq_srw`: for `T ≤ β`, a regular set `Γ` of paths depending only on `[0,T]` has
  the same probability for the cyclic walk of a Poisson environment as for any SRW.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Extension of a path on `[0,b]` to a path stopped at `T ≤ b`. -/
def extStop (b T : ℝ≥0) (hT : T ≤ b) (g : Set.Iic b → Fin d → ℤ) : PathSpace d :=
  fun s => g ⟨min s T, (min_le_right _ _).trans hT⟩

theorem measurable_extStop (b T : ℝ≥0) (hT : T ≤ b) : Measurable (extStop (d := d) b T hT) :=
  measurable_pi_iff.2 fun _s => measurable_pi_apply _

theorem extStop_restrict (b T : ℝ≥0) (hT : T ≤ b) (γ : PathSpace d) :
    extStop b T hT (restrictIic b γ) = stopPath T γ := rfl

/-- **identification of the regenerated walk below β (b)**, event form. -/
theorem cycPath_prob_eq_srw {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {ν : Ω → Measure (RingSpace d β)}
    (hν : IsPoissonPointProcess ν (ringIntensity d β) P) {T : ℝ≥0} (hT : (T : ℝ) ≤ β)
    {Γ : Set (PathSpace d)} (hΓ : IsRegSet Γ) (hloc : ∀ γ, γ ∈ Γ ↔ stopPath T γ ∈ Γ)
    {Z' : Ω' → PathSpace d} (hZ' : IsSRW P' Z') :
    P {ω | cycPath (ν ω) ∈ Γ} = P' {ω | Z' ω ∈ Γ} := by
  obtain ⟨Γ', hΓ'm, hΓ'⟩ := hΓ
  obtain ⟨Ωd, mΩd, Pd, N₀, hPd, hN₀, -⟩ := exists_isPoissonPointProcess_clockIntensity (Dir d)
  have hcan := canonical_isSRW hN₀
  have hTb : T ≤ β.toNNReal := by
    rw [← NNReal.coe_le_coe]; simpa [Real.coe_toNNReal _ (Fact.out : 0 < β).le] using hT
  set b := β.toNNReal with hb
  have hgood : ∀ᵐ ω ∂P, Good (ν ω) := ae_good hν
  have hlaw := cyc_srw_short_law hν hN₀ 0 0
  have hR : Measurable fun ω => restrictIic b (cycPath (ν ω)) :=
    (measurable_restrictIic b).comp (measurable_cycPath hν.measurable)
  have hlaw' : P.map (fun ω => restrictIic b (cycPath (ν ω))) =
      Pd.map (fun ω => restrictIic b (canonical d N₀ ω)) := by
    rw [← hlaw]
    refine Measure.map_congr ?_
    filter_upwards [hgood] with ω hω
    funext s
    simp only [sub_zero]
    exact (cycWalk_eq_cycPath hω s.1).symm
  have hR' : Measurable fun ω => restrictIic b (canonical d N₀ ω) :=
    (measurable_restrictIic b).comp (measurable_canonical hN₀.measurable)
  have hE := measurable_extStop (d := d) b T hTb
  -- step 1: stopped cyclic walk
  have h1 : P {ω | cycPath (ν ω) ∈ Γ} = P {ω | stopPath T (cycPath (ν ω)) ∈ Γ'} := by
    refine measure_congr ?_
    filter_upwards [hgood] with ω hω
    have hreg : IsRegularPath (stopPath T (cycPath (ν ω))) :=
      (isRegularPath_cycPath hω).stop T
    have : (cycPath (ν ω) ∈ Γ) = (stopPath T (cycPath (ν ω)) ∈ Γ') :=
      propext (((hloc _).trans (hΓ' _ hreg)))
    simpa using congrArg (fun p : Prop => p) this
  have h2 : P {ω | stopPath T (cycPath (ν ω)) ∈ Γ'} =
      Pd {ω | stopPath T (canonical d N₀ ω) ∈ Γ'} := by
    have e1 : {ω | stopPath T (cycPath (ν ω)) ∈ Γ'} =
        (fun ω => restrictIic b (cycPath (ν ω))) ⁻¹' (extStop b T hTb ⁻¹' Γ') := rfl
    have e2 : {ω | stopPath T (canonical d N₀ ω) ∈ Γ'} =
        (fun ω => restrictIic b (canonical d N₀ ω)) ⁻¹' (extStop b T hTb ⁻¹' Γ') := rfl
    rw [e1, e2, ← Measure.map_apply hR (hE hΓ'm), ← Measure.map_apply hR' (hE hΓ'm), hlaw']
  have h3 : Pd {ω | stopPath T (canonical d N₀ ω) ∈ Γ'} = Pd {ω | canonical d N₀ ω ∈ Γ} := by
    refine measure_congr (Filter.Eventually.of_forall fun ω => ?_)
    have hreg : IsRegularPath (stopPath T (canonical d N₀ ω)) :=
      (hcan.2.1 ω).stop T
    have : (canonical d N₀ ω ∈ Γ) = (stopPath T (canonical d N₀ ω) ∈ Γ') :=
      propext (((hloc _).trans (hΓ' _ hreg)))
    simpa using (congrArg (fun p : Prop => p) this).symm
  rw [h1, h2, h3]
  exact hcan.prob_regSet_eq hZ' ⟨Γ', hΓ'm, hΓ'⟩

end ElboimSly.Paper

end
