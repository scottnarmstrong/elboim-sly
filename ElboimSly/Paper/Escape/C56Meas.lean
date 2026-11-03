/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Stop
public import ElboimSly.Paper.Escape.C56MeasGen
public import Mathlib

/-!
# The events `ℬ₀`, `ℬ_i`, `G_i` of ES22 Claim 5.6 are stopped events

Phases, radii and events of Claim 5.6 ("`G_i ∈ ℱ_{ζ_i}`").  The event `ℬ_i` depends on the walk only through
its stopped path `W(· ∧ ζ_i)` and the times `ζ_{i-1}`, `ζ_i`, so it lies in `ℱ_{ζ_i}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ}

/-- `W_v = v + W` as a path on `ℝ`. -/
noncomputable def escYv {β : ℝ} [Fact (0 < β)] {Ω : Type} [MeasurableSpace Ω]
    (N : Ω → Measure (CycS ℕ (k + 2) β)) (v : Fin (k + 2) → ℤ) (ω : Ω) :
    ℝ → Fin (k + 2) → ℤ := fun r => v + escY N ω r

theorem escZeta_add_const (β : ℝ) (v : Fin (k + 2) → ℤ) (y : ℝ → Fin (k + 2) → ℤ) (t : ℝ)
    (m i : ℕ) : escZeta β (fun r => v + y r) t m i = escZeta β y t m i := by
  unfold escZeta
  induction i with
  | zero => simp only [escZetaAux, escZetaStep_add_const]
  | succ i ih => simp only [escZetaAux, escZetaStep_add_const, ih]

theorem continuous_es56F {t : ℝ} (ht : t ≠ 0) (v w q : Fin (k + 2) → ℝ) :
    Continuous (es56F t v w q) := by
  unfold es56F
  refine Continuous.if_le (f := fun s => s) (g := fun _ => t / 2) ?_ ?_ continuous_id
    continuous_const ?_
  · fun_prop
  · fun_prop
  · intro s hs
    have h1 : 2 * s / t = 1 := by rw [hs]; field_simp
    have h2 : 2 * (t - s) / t = 1 := by rw [hs]; field_simp; ring
    simp [h1, h2]

/-- Stopped paths read the same values before the stopping level. -/
theorem stop_fn_toNNReal {V : Type*} (p : CPath V) (b : ℝ≥0) {s : ℝ} (_h0 : 0 ≤ s)
    (hs : s ≤ (b : ℝ)) : (p.stop b).fn s.toNNReal = p.fn s.toNNReal := by
  rw [CPath.stop_fn, min_eq_left]
  exact Real.toNNReal_le_iff_le_coe.2 hs

section Sets

variable (β : ℝ) (j : ℕ) (u v z : Fin (k + 2) → ℤ) (t : ℝ)

/-- The pathwise form of `ℬ₀`, on triples `(p, 0, ζ₀)`. -/
def setB0 : Set (CPath (Fin (k + 2) → ℤ) × ℝ × ℝ) :=
  {w | w.2.2 < es56B t (escPhaseM β t) 0} ∩
  forallBetween (fun x _ => v + x ∈ escBlockMinus j u ∧
    ‖escCast (v + x) - escCast v‖ ≤ β ^ (0.3 : ℝ)) ∩
  {w | ‖escCast (v + w.1.fn w.2.2.toNNReal) - escCurve j u v z t w.2.2‖ ≤
    es56Rho t (escPhaseM β t) 0}

/-- The pathwise form of `ℬ_i`, on triples `(p, ζ_{i-1}, ζ_i)`. -/
def setBi (i : ℕ) : Set (CPath (Fin (k + 2) → ℤ) × ℝ × ℝ) :=
  {w | w.2.2 < es56B t (escPhaseM β t) i} ∩
  forallBetween (fun x s => ‖escCast (v + x) - escCurve j u v z t s‖ ≤
    escR t (escPhaseM β t) i) ∩
  {w | ‖escCast (v + w.1.fn w.2.2.toNNReal) - escCurve j u v z t w.2.2‖ ≤
    (24 / 100) * escR t (escPhaseM β t) i}

theorem continuous_escCurve (ht : t ≠ 0) : Continuous (escCurve j u v z t) :=
  continuous_es56F ht _ _ _

theorem isClosed_curve_le (ht : t ≠ 0) (x : Fin (k + 2) → ℤ) (R : ℝ) :
    IsClosed {s : ℝ | ‖escCast (v + x) - escCurve j u v z t s‖ ≤ R} :=
  isClosed_le (by have := continuous_escCurve j u v z t ht; fun_prop) continuous_const

theorem measurableSet_setB0 (ht : t ≠ 0) : MeasurableSet (setB0 β j u v z t) := by
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
  · exact measurableSet_lt (measurable_snd.comp measurable_snd) measurable_const
  · refine measurableSet_forallBetween _ fun x => ?_
    by_cases h : v + x ∈ escBlockMinus j u ∧ ‖escCast (v + x) - escCast v‖ ≤ β ^ (0.3 : ℝ)
    · simp only [h, and_self, ofPred_true]; exact isClosed_univ
    · simp only [h, ofPred_false]; exact isClosed_empty
  · exact measurableSet_endpoint
      (fun x s => ‖escCast (v + x) - escCurve j u v z t s‖ ≤ es56Rho t (escPhaseM β t) 0)
      fun x => (isClosed_curve_le j u v z t ht x _).measurableSet

theorem measurableSet_setBi (ht : t ≠ 0) (i : ℕ) : MeasurableSet (setBi β j u v z t i) := by
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
  · exact measurableSet_lt (measurable_snd.comp measurable_snd) measurable_const
  · exact measurableSet_forallBetween _ fun x => isClosed_curve_le j u v z t ht x _
  · exact measurableSet_endpoint
      (fun x s => ‖escCast (v + x) - escCurve j u v z t s‖ ≤
        (24 / 100) * escR t (escPhaseM β t) i)
      fun x => (isClosed_curve_le j u v z t ht x _).measurableSet

end Sets

end ElboimSly.Paper.Escape

end
