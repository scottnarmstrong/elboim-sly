/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.FixedBound
public import Mathlib

/-!
# Path space, laws and SRWs; the local upper bound

Path space, laws, SRWs, admissible filtrations (a)-(c), local upper bound without constant, (H2) at the base.

Processes are indexed by `ℝ≥0`.  A process `Z` is an SRW if it is measurable for the product
`σ`-algebra, all its paths are regular, and its law on path space equals the law of the canonical
walk built from some Poisson point process (on some probability space).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

/-- The path space `(ℤ^d)^{[0,∞)}` with the product `σ`-algebra. -/
abbrev PathSpace (d : ℕ) : Type := ℝ≥0 → Fin d → ℤ

/-- A regular path: locally constant on the right. -/
def IsRegularPath {d : ℕ} (γ : PathSpace d) : Prop :=
  ∀ t : ℝ≥0, ∃ δ : ℝ≥0, 0 < δ ∧ ∀ s : ℝ≥0, t ≤ s → s < t + δ → γ s = γ t

/-- The canonical walk built from a point process, as a path-space valued map. -/
noncomputable def canonical {Ω : Type*} (d : ℕ) (N : Ω → Measure (Dir d × ℝ)) (ω : Ω) :
    PathSpace d :=
  fun s => walk d (N ω) (s : ℝ)

theorem measurable_walk (d : ℕ) (t : ℝ) : Measurable fun ν : Measure (Dir d × ℝ) => walk d ν t := by
  classical
  unfold walk
  refine Measurable.ite (measurableSet_goodSet d) ?_ measurable_const
  refine Finset.measurable_fun_sum _ fun v _ => ?_
  have h : Measurable fun ν : Measure (Dir d × ℝ) => (⌊(cnt ν v t).toReal⌋₊ : ℕ) :=
    measurable_natOf.comp (measurable_cnt v t)
  exact (Measurable.of_discrete (f := fun n : ℕ => ((n : ℤ) • v.vec))).comp h

theorem measurable_canonical {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {N : Ω → Measure (Dir d × ℝ)} (hN : Measurable N) : Measurable (canonical d N) :=
  measurable_pi_iff.2 fun s => (measurable_walk d s).comp hN

/-- Law of a process equals the law of a canonical walk (Path space, laws, SRWs, admissible filtrations (b), (c)). -/
def HasSRWLaw {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) (Z : Ω → PathSpace d) :
    Prop :=
  ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (N' : Ω' → Measure (Dir d × ℝ)),
    IsPoissonPointProcess N' (clockIntensity (Dir d)) P' ∧ P.map Z = P'.map (canonical d N')

/-- Path space, laws, SRWs, admissible filtrations (c): `Z` is an SRW started at `0`. -/
def IsSRW {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) (Z : Ω → PathSpace d) : Prop :=
  Measurable Z ∧ (∀ ω, IsRegularPath (Z ω)) ∧ HasSRWLaw P Z

theorem Real_inv_sqrt_pow (d : ℕ) {x : ℝ} (hx : 0 < x) :
    (1 / √x) ^ d = x ^ (-(d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hx.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hx.le]
  congr 1
  ring

/-- Local upper bound without constant: for every SRW and every real `t ≥ 1`,
`P(X(t) = u) ≤ (π t)^{-d/2}`. -/
theorem IsSRW.prob_eq_le {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {Z : Ω → PathSpace d} (hZ : IsSRW P Z) {t : ℝ≥0} (ht : 1 ≤ (t : ℝ)) (u : Fin d → ℤ) :
    P {ω | Z ω t = u} ≤ ENNReal.ofReal ((π * t) ^ (-(d : ℝ) / 2)) := by
  obtain ⟨hmeas, _, Ω', _, P', N', hN', hlaw⟩ := hZ
  have hev : Measurable fun γ : PathSpace d => γ t := measurable_pi_apply t
  have hset : MeasurableSet {γ : PathSpace d | γ t = u} := hev (measurableSet_singleton u)
  have h1 : P {ω | Z ω t = u} = P.map Z {γ | γ t = u} := by
    rw [Measure.map_apply hmeas hset]; rfl
  rw [h1, hlaw, Measure.map_apply (measurable_canonical hN'.measurable) hset]
  have := prob_walk_eq_le hN' ht u
  have hpt : 0 < π * (t : ℝ) := by positivity
  rw [← Real_inv_sqrt_pow d hpt]
  exact this

/-- (H2) at the base: `P(X(t) = u) ≤ t^{-d/2} ≤ t^{-d/2 + 0.1}` for real `t ≥ 1`. -/
theorem IsSRW.prob_eq_le_H2 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {Z : Ω → PathSpace d} (hZ : IsSRW P Z) {t : ℝ≥0} (ht : 1 ≤ (t : ℝ)) (u : Fin d → ℤ) :
    P {ω | Z ω t = u} ≤ ENNReal.ofReal ((t : ℝ) ^ (-(d : ℝ) / 2)) ∧
      ENNReal.ofReal ((t : ℝ) ^ (-(d : ℝ) / 2)) ≤
        ENNReal.ofReal ((t : ℝ) ^ (-(d : ℝ) / 2 + 1 / 10)) := by
  have ht0 : (0 : ℝ) < t := by linarith
  refine ⟨(hZ.prob_eq_le ht u).trans (ENNReal.ofReal_le_ofReal ?_),
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le ht (by linarith))⟩
  refine Real.rpow_le_rpow_of_nonpos ht0 ?_ (by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith)
  nlinarith [Real.pi_gt_three]

end SRW
end ElboimSly
