/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.StoppedMeas
public import ElboimSly.Foundations.Brownian.Freeze
public import ElboimSly.Foundations.Brownian.Moments
public import Mathlib

/-!
# Wald's identity for bounded stopping times

Exit times of Brownian motion from symmetric intervals (c), the truncated identity.

For a stopping time `ρ ≤ K` of the natural filtration of a standard real Brownian motion,
`E β(ρ)² + E (K - ρ) = K`. We prove it from the strong Markov property (strong Markov property at stopping times of the natural filtration)
and the freezing lemma, on the canonical space `C0` of continuous paths vanishing at `0` (where
evaluation at a variable time is jointly measurable).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

/-- The canonical space of continuous paths vanishing at `0`, with the trace `σ`-algebra. -/
abbrev C0 := {w : ℝ≥0 → ℝ // IsC0 w}

/-- The coordinate process on `C0`. -/
def coordC0 : ℝ≥0 → C0 → ℝ := fun s w => w.1 s

lemma isProcess_coordC0 : IsProcess coordC0 :=
  ⟨fun w => w.2, fun s => (measurable_pi_apply s).comp measurable_subtype_coe⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {β : ℝ≥0 → Ω → ℝ}

/-- `E (z + β u)² = z² + u`, in `[0,∞]`. -/
lemma lintegral_sq_shift [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) (z : ℝ) (u : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal ((z + β u ω) ^ 2) ∂P = ENNReal.ofReal (z ^ 2 + u) := by
  have hm2 : MemLp (β u) 2 P := memLp_two_eval hβ 0 u
  have hi1 : Integrable (β u) P := hm2.integrable (by norm_num)
  have hi2 : Integrable (fun ω => β u ω ^ 2) P := hm2.integrable_sq
  have h0 : ∫ ω, β u ω ∂P = 0 := IsStandardBrownianMotion.integral_eval_eq_zero hβ 0 u
  have h2 : ∫ ω, β u ω ^ 2 ∂P = u := by
    have h := IsStandardBrownianMotion.integral_mul_eval hβ 0 0 u
    have e : ∫ ω, β u ω ^ 2 ∂P = ∫ ω, toVec1 β u ω 0 * toVec1 β u ω 0 ∂P := by
      congr 1; funext ω; rw [sq]; rfl
    rw [e, h]; simp
  have hint : Integrable (fun ω => (z + β u ω) ^ 2) P := by
    have : (fun ω => (z + β u ω) ^ 2) = fun ω => z ^ 2 + 2 * z * β u ω + β u ω ^ 2 := by
      funext ω; ring
    rw [this]
    exact ((integrable_const _).add (hi1.const_mul _)).add hi2
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
  congr 1
  have : (fun ω => (z + β u ω) ^ 2) = fun ω => z ^ 2 + 2 * z * β u ω + β u ω ^ 2 := by
    funext ω; ring
  have hA : Integrable (fun ω => z ^ 2 + 2 * z * β u ω) P :=
    (integrable_const _).add (hi1.const_mul _)
  have hB : Integrable (fun ω => 2 * z * β u ω) P := hi1.const_mul _
  have hC : Integrable (fun _ : Ω => z ^ 2) P := integrable_const _
  rw [this, integral_add hA hi2, integral_add hC hB, integral_const_mul, h0, h2]
  simp

/-- Wald's identity for a bounded stopping time. -/
theorem wald_stopped [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) {ρ : Ω → ℝ≥0∞}
    (hρ : ∀ t : ℝ≥0, MeasurableSet[realFiltration β t] {ω | ρ ω ≤ t}) {K : ℝ≥0}
    (hρK : ∀ ω, ρ ω ≤ K) :
    ∫⁻ ω, ENNReal.ofReal ((β (ρ ω).toNNReal ω) ^ 2) ∂P +
      ∫⁻ ω, ENNReal.ofReal ((K : ℝ) - (ρ ω).toReal) ∂P = ENNReal.ofReal K := by
  have hproc : IsProcess β := isProcess_of_realBM hβ
  have hF : ∀ t, realFiltration β t ≤ mΩ := realFiltration_le hproc.2
  have hρm : Measurable ρ := measurable_of_stopping hproc.2 hρ
  have hlt : ∀ ω, ρ ω < ⊤ := fun ω => lt_of_le_of_lt (hρK ω) ENNReal.coe_lt_top
  have hfin : ∀ᵐ ω ∂P, ρ ω < ⊤ := Filter.Eventually.of_forall hlt
  have hβ' : IsStandardRealBM (procShift ρ β) P := isStandardRealBM_procShift hβ hρ hfin
  have hsh : IsProcess (procShift ρ β) := hproc.shift hρm
  -- the frozen variables
  set Y : Ω → C0 := fun ω => ⟨fun t => procShift ρ β t ω, hsh.1 ω⟩ with hY
  set X : Ω → ℝ × ℝ≥0 := fun ω => (β (ρ ω).toNNReal ω, (ρ ω).toNNReal) with hX
  have hXm : Measurable[stoppedSigma (realFiltration β) ρ hρ] X :=
    (measurable_value_stopped hproc hρ).prodMk (measurable_toNNReal_stopped hF hρ)
  have hYm : Measurable Y :=
    Measurable.subtype_mk (measurable_pi_iff.2 fun t => hsh.2 t)
  have hind := indep_stopped_procShift hβ hρ hfin
  have hXmeas : Measurable X :=
    hXm.mono stoppedSigma_le le_rfl
  have hindep : IndepFun X Y P := by
    show Indep (MeasurableSpace.comap X inferInstance) (MeasurableSpace.comap Y inferInstance) P
    refine indep_of_indep_of_le_left (indep_of_indep_of_le_right hind ?_) hXm.comap_le
    have : MeasurableSpace.comap Y inferInstance =
        MeasurableSpace.comap (fun ω s => procShift ρ β s ω) inferInstance := by
      exact MeasurableSpace.comap_comp (f := Subtype.val) (g := Y)
    exact this.le
  set φ : ℝ × ℝ≥0 → C0 → ℝ≥0∞ := fun x y => ENNReal.ofReal ((x.1 + y.1 (K - x.2)) ^ 2) with hφ
  have hφm : Measurable (Function.uncurry φ) := by
    have h1 : Measurable fun p : (ℝ × ℝ≥0) × C0 => coordC0 (K - p.1.2) p.2 :=
      isProcess_coordC0.measurable_uncurry.comp
        ((measurable_const.sub (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
    exact ENNReal.measurable_ofReal.comp
      (((measurable_fst.comp measurable_fst).add h1).pow_const 2)
  have hfr := lintegral_freeze hXmeas hYm hindep hφm
  -- left side
  have hL : ∫⁻ ω, φ (X ω) (Y ω) ∂P = ENNReal.ofReal K := by
    have : ∀ ω, φ (X ω) (Y ω) = ENNReal.ofReal ((0 + β K ω) ^ 2) := by
      intro ω
      have hne : ρ ω ≠ ⊤ := (hlt ω).ne
      have hle : (ρ ω).toNNReal ≤ K := by
        have := ENNReal.toNNReal_mono (by simp) (hρK ω)
        simpa using this
      simp only [hφ, hX, hY, procShift, shiftAt_apply, ite_eq_right hne, zero_add]
      congr 2
      rw [add_tsub_cancel_of_le hle]
      ring
    simp_rw [this]
    rw [lintegral_sq_shift hβ 0 K]
    simp
  -- right side
  have hR : ∀ ω, ∫⁻ y, φ (X ω) y ∂(P.map Y) =
      ENNReal.ofReal ((β (ρ ω).toNNReal ω) ^ 2) + ENNReal.ofReal ((K : ℝ) - (ρ ω).toReal) := by
    intro ω
    have hle : (ρ ω).toNNReal ≤ K := by
      have := ENNReal.toNNReal_mono (by simp) (hρK ω)
      simpa using this
    have hφy : Measurable (φ (X ω)) := by
      have := hφm.comp (measurable_const.prodMk measurable_id : Measurable fun y : C0 => (X ω, y))
      exact this
    rw [lintegral_map hφy hYm]
    have : ∀ ω', φ (X ω) (Y ω') =
        ENNReal.ofReal ((β (ρ ω).toNNReal ω + procShift ρ β (K - (ρ ω).toNNReal) ω') ^ 2) :=
      fun ω' => rfl
    simp_rw [this]
    rw [lintegral_sq_shift hβ' _ _]
    rw [← ENNReal.ofReal_add (sq_nonneg _) (by
      have : ((ρ ω).toNNReal : ℝ) ≤ K := by exact_mod_cast hle
      rw [ENNReal.coe_toNNReal_eq_toReal] at this
      linarith [this])]
    congr 1
    rw [NNReal.coe_sub hle, ENNReal.coe_toNNReal_eq_toReal]
  have hrhs : ∫⁻ ω, ∫⁻ y, φ (X ω) y ∂(P.map Y) ∂P =
      ∫⁻ ω, ENNReal.ofReal ((β (ρ ω).toNNReal ω) ^ 2) ∂P +
        ∫⁻ ω, ENNReal.ofReal ((K : ℝ) - (ρ ω).toReal) ∂P := by
    simp_rw [hR]
    rw [lintegral_add_left]
    exact ENNReal.measurable_ofReal.comp
      ((hproc.measurable_uncurry.comp (hρm.ennreal_toNNReal.prodMk measurable_id)).pow_const 2)
  rw [← hrhs, ← hfr, hL]

end ElboimSly.StrongApprox
