/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.PairLemmaAux
public import ElboimSly.Paper.Base.OneLapA
public import ElboimSly.Paper.Base.Constants
public import ElboimSly.Foundations.SRW.Lemma82BModel
public import Mathlib

/-!
# Far starting points

ES22 Lemma 8.2, "Far starting points".

For `c ∈ ℤ^d` and `r ∈ ℝ`, `farGood ν c r n T` says that the walks from points at distance `≥ 4ⁿ`
of `c` stay at distance `> 1.9ⁿ` of the walk from `c`, during `[0, T]`.  Its complement has
probability at most `C_𝒜(d) e^{-4ⁿ/12}` (`far_prob`), by `lemma82_b_model` and cyclic walks within one lap (a).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper.Base

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The far-point event `𝒜(c, r)`, in the form of `lemma82_b_model`. -/
def farGood (ν : Measure (RingSpace d β)) (c : Fin d → ℤ) (r : ℝ) (n : ℕ) (T : ℝ≥0) : Prop :=
  ∀ v : Fin d → ℤ, (4 : ℝ) ^ n ≤ ‖v‖ → ∀ s₁ s₂ : ℝ≥0, s₁ ≤ T → s₂ ≤ T →
    (1.9 : ℝ) ^ n < ‖trajProc ν (c + v) r s₂ - trajProc ν c r s₁‖

theorem isStepPath_trajProc' (ν : Measure (RingSpace d β)) (x : Fin d → ℤ) (a : ℝ) :
    IsStepPath (trajProc ν x a) := by
  by_cases hg : Good ν
  · exact isStepPath_trajProc hg x a
  · have : trajProc ν x a = fun _ => x := by simp [trajProc, hg]
    rw [this]
    exact isStepPath_const x

theorem isRegularPath_trajProc_stop (ν : Measure (RingSpace d β)) (x : Fin d → ℤ) (a : ℝ)
    (T : ℝ≥0) (y : Fin d → ℤ) : IsRegularPath fun s => trajProc ν x a (min s T) - y := by
  have hs := isStepPath_stop (isStepPath_trajProc' ν x a) T
  refine isRegularPath_of_isStepPath ⟨fun s => ?_, fun S => ?_⟩
  · filter_upwards [hs.rc s] with u hu; simp only [hu]
  · exact (hs.fin S).subset fun r hr =>
      ⟨⟨hr.1.1, fun hc => hr.1.2 (hc.mono fun u hu => by simp only [hu])⟩, hr.2⟩

theorem far_prob {Ω : Type} [MeasurableSpace Ω] {Pe : Measure Ω} {ν : Ω → Measure (RingSpace d β)}
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe) [NeZero d] {n : ℕ} (hn : 4 ≤ n)
    {t₀ : ℝ} (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hTβ : lem82T n t₀ ≤ β) (c : Fin d → ℤ) (r : ℝ) :
    Pe {ω | ¬ farGood (ν ω) c r n (lem82T n t₀).toNNReal} ≤
      ENNReal.ofReal (es8CA d * Real.exp (-((4 : ℝ) ^ n / 12))) := by
  have := hν.isProbabilityMeasure
  have hTpos : 0 < lem82T n t₀ := lem82T_pos hn ht1
  have hT : (((lem82T n t₀).toNNReal : ℝ≥0) : ℝ) ≤ β := by
    rw [Real.coe_toNNReal _ hTpos.le]; exact hTβ
  set T' : ℝ≥0 := (lem82T n t₀).toNNReal with hT'
  set Y : (Fin d → ℤ) → Ω → PathSpace d := fun v ω s => trajProc (ν ω) (c + v) r s - c with hY
  have hYm : ∀ v, Measurable fun ω s => Y v ω (min s T') - v := fun v => by
    refine measurable_pi_iff.2 fun s => ?_
    exact (measurable_of_countable (fun x : Fin d → ℤ => x - c - v)).comp
      ((measurable_pi_apply (min s T')).comp ((measurable_trajProc (c + v) r).comp hν.measurable))
  have hYr : ∀ v ω, IsRegularPath fun s => Y v ω (min s T') - v := fun v ω => by
    have := isRegularPath_trajProc_stop (ν ω) (c + v) r T' (c + v)
    convert this using 2 with s
    simp only [hY, sub_sub, add_comm c v]
  have hlaw : ∀ v, Pe.map (fun ω s => Y v ω (min s T') - v) =
      (srwP d).map (fun ω s => srwZ d ω (min s T')) := fun v => by
    rw [← one_lap_a_model hν (c + v) r hT]
    congr 1
    funext ω s
    simp only [hY, sub_sub, add_comm c v]
  have key := lemma82_b_model (P := Pe) hn ht1 ht4 Y hYm hYr hlaw
  refine le_trans (measure_mono ?_) (key.trans ?_)
  · intro ω hω hcon
    apply hω
    intro v hv s₁ s₂ h1 h2
    have := hcon v hv s₁ s₂ h1 h2
    simpa [hY, sub_sub_sub_cancel_right] using this
  · refine le_of_eq ?_
    unfold es8CA
    rfl

end ElboimSly.Paper

end
