/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Shift
public import Mathlib

/-!
# The shifted walk is the walk of the shifted process

Independent stationary increments; Markov property at fixed times (a), Markov property for every SRW; admissible filtrations (a).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {N : Ω → Measure (Dir d × ℝ)} {P : Measure Ω}

/-- The shifted increment process `(θ_a γ)(s) = γ(a+s) - γ(a)`. -/
def theta (a : ℝ≥0) (γ : PathSpace d) : PathSpace d := fun s => γ (a + s) - γ a

theorem measurable_theta (a : ℝ≥0) : Measurable (theta (d := d) a) :=
  measurable_pi_iff.2 fun s => (measurable_pi_apply (a + s)).sub (measurable_pi_apply a)

theorem shift_ppp (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) {a : ℝ}
    (ha : 0 ≤ a) : IsPoissonPointProcess (fun ω => shiftMeasure d a (N ω))
      (clockIntensity (Dir d)) P := by
  have h := (hN.restrict ((MeasurableSet.univ (α := Dir d)).prod (measurableSet_Ioi (a := a)))).map_measure
    (measurable_shiftMap d a)
  rw [clock_shift ha] at h
  exact h

theorem cnt_shift (a : ℝ) (ν : Measure (Dir d × ℝ)) (v : Dir d) (s : ℝ) :
    cnt (shiftMeasure d a ν) v s = ν (({v} : Set (Dir d)) ×ˢ Ioc a (a + s)) := by
  unfold cnt shiftMeasure
  rw [Measure.map_apply (measurable_shiftMap d a) (measurableSet_rect v _ measurableSet_Ioc),
    Measure.restrict_apply ((measurable_shiftMap d a) (measurableSet_rect v _ measurableSet_Ioc))]
  congr 1
  ext ⟨x, y⟩
  simp only [shiftMap, Prod.map_apply, id_eq, mem_inter_iff, mem_preimage, mem_prod,
    mem_singleton_iff, mem_Ioc, mem_univ, mem_Ioi, true_and]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, _⟩; exact ⟨h1, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by linarith, by linarith⟩, h2⟩

theorem walk_shift_ae (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) {a : ℝ}
    (ha : 0 ≤ a) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s →
      walk d (shiftMeasure d a (N ω)) s = walk d (N ω) (a + s) - walk d (N ω) a := by
  filter_upwards [ae_good hN, ae_good (shift_ppp hN ha)] with ω h1 h2 s hs
  rw [walk_sub_eq h1 ha (by linarith), walk_of_good h2]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [cnt_shift]

theorem theta_canonical_ae (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (a : ℝ≥0) :
    ∀ᵐ ω ∂P, theta a (canonical d N ω) = canonical d (fun ω => shiftMeasure d a (N ω)) ω := by
  filter_upwards [walk_shift_ae hN a.2] with ω hω
  funext s
  have := hω s s.2
  simp only [theta, canonical, NNReal.coe_add]
  exact this.symm

/-- Independent stationary increments; Markov property at fixed times (a), stationarity: the shifted canonical walk has the law of the
canonical walk. -/
theorem map_theta_canonical (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (a : ℝ≥0) :
    P.map (fun ω => theta a (canonical d N ω)) = P.map (canonical d N) := by
  have hm1 : Measurable (canonical d N) := measurable_canonical hN.measurable
  have hS := shift_ppp hN a.2
  have hm2 : Measurable (canonical d fun ω => shiftMeasure d a (N ω)) :=
    measurable_canonical hS.measurable
  have h1 : P.map (fun ω => theta a (canonical d N ω)) =
      P.map (canonical d fun ω => shiftMeasure d a (N ω)) :=
    Measure.map_congr (theta_canonical_ae hN a)
  have h2 : P.map (fun ω => shiftMeasure d a (N ω)) = P.map N := (hS.map_eq_map hN).symm
  have hc : canonical d (fun ω => shiftMeasure d a (N ω)) =
      (fun ν => fun s : ℝ≥0 => walk d ν (s : ℝ)) ∘ fun ω => shiftMeasure d a (N ω) := rfl
  have hc' : canonical d N = (fun ν => fun s : ℝ≥0 => walk d ν (s : ℝ)) ∘ N := rfl
  have hG : Measurable fun ν : Measure (Dir d × ℝ) => fun s : ℝ≥0 => walk d ν (s : ℝ) :=
    measurable_pi_iff.2 fun s => measurable_walk d s
  have e1 := Measure.map_map (μ := P) hG hS.measurable
  have e2 := Measure.map_map (μ := P) hG hN.measurable
  rw [h1, hc, hc']
  exact e1.symm.trans ((congrArg (Measure.map _) h2).trans e2)

end SRW
end ElboimSly
