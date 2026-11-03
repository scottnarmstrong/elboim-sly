/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Order
public import ElboimSly.Paper.Step.Lemma78Setting2
public import ElboimSly.Paper.Heavy.BlockProbShift
public import Mathlib

/-!
# Connecting `Step78Data` to the path-level statements

Setting of Lemma 7.8 (ES22 §7). `step78DataOf` is the data of Lemma 7.8 for the
walks `W₁ = W^{N(ω)}_{0,0}` and `W₂ = W^{N(ω)}_{u,q}`: the relaxed times `𝒯₂` of `D` are the
relaxed times of `w₂ = W₂ - u`, the path of `D` is `W₂` on `[0, ∞)`, and
`V = W₁([0, T])`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Heavy

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*}

/-- The data of Lemma 7.8: second walk `W₂ = W_{u,q}`, `V = W₁([0,T])`, `ρ_k = 1.9^k/2`. -/
noncomputable def step78DataOf (d : ℕ) (β : ℝ) [Fact (0 < β)] (n : ℕ) (T : ℝ)
    (u : Fin d → ℤ) (q : ℝ) (N : Ω → Measure (RingSpace d β)) : Step78Data d Ω where
  β := β
  T := T.toNNReal
  n := n
  ρ := (1.9 : ℝ) ^ heavyLevel d n / 2
  u := u
  w s ω := cycWalk (N ω) u q (s : ℝ)
  V ω := (fun s : ℝ => cycWalk (N ω) 0 0 s) '' Icc 0 T

variable {n : ℕ} {T q : ℝ} {u : Fin d → ℤ} {N : Ω → Measure (RingSpace d β)}

theorem step78DataOf_path {ω : Ω} {r : ℝ} (hr : 0 ≤ r) :
    (step78DataOf d β n T u q N).path ω r = cycWalk (N ω) u q r := by
  simp [Step78Data.path, stepExt, step78DataOf, Real.coe_toNNReal _ hr]

theorem step78DataOf_V (hT : 0 ≤ T) (ω : Ω) :
    (step78DataOf d β n T u q N).V ω =
      (fun s : ℝ => cycWalk (N ω) 0 0 s) '' Icc 0 (((step78DataOf d β n T u q N).T : ℝ≥0) : ℝ) := by
  simp [step78DataOf, Real.coe_toNNReal _ hT]

theorem step78DataOf_T (hT : 0 ≤ T) :
    (((step78DataOf d β n T u q N).T : ℝ≥0) : ℝ) = T := by
  simp [step78DataOf, Real.coe_toNNReal _ hT]

theorem step78DataOf_n : (step78DataOf d β n T u q N).n = n := rfl

/-- `𝒯₂ = relaxedTimes β (W₂ - u)`. -/
theorem step78DataOf_relaxed (ω : Ω) :
    (step78DataOf d β n T u q N).relaxed ω =
      relaxedTimes β (fun s : ℝ => cycWalk (N ω) u q s - u) := by
  have hβ : 0 < β := Fact.out
  ext t
  simp only [Step78Data.relaxed, stepRelaxedSetOf, stepRelaxedSet, relaxedTimes,
    mem_ofPred_eq, NNReal.coe_zero]
  constructor
  · rintro ⟨ht, h⟩
    refine ⟨ht, ?_⟩
    rw [isRelaxedTimeWrt_sub_const]
    exact (isRelaxedTimeWrt_congr_le hβ (w' := fun s : ℝ => cycWalk (N ω) u q s)
      (fun s hs _ => by simp [step78DataOf, stepExt, Real.coe_toNNReal _ hs]) le_rfl ht).1 h
  · rintro ⟨ht, h⟩
    refine ⟨ht, ?_⟩
    rw [isRelaxedTimeWrt_sub_const] at h
    exact (isRelaxedTimeWrt_congr_le hβ (w' := fun s : ℝ => cycWalk (N ω) u q s)
      (fun s hs _ => by simp [step78DataOf, stepExt, Real.coe_toNNReal _ hs]) le_rfl ht).2 h

/-- The conclusion of ES22 Lemma 6.8 gives a point of `D.farSet`. -/
theorem step78DataOf_mem_farSet (_hT : 0 ≤ T) {ω : Ω} {s : ℝ}
    (hs : s ∈ relaxedTimes β (fun s : ℝ => cycWalk (N ω) u q s - u))
    (hfar : ∀ v ∈ (fun s : ℝ => cycWalk (N ω) 0 0 s) '' Icc 0 T,
      (1.9 : ℝ) ^ heavyLevel d n / 2 ≤ ‖cycWalk (N ω) u q s - v‖) :
    s ∈ (step78DataOf d β n T u q N).farSet ω := by
  refine ⟨by rw [step78DataOf_relaxed]; exact hs, fun v hv => ?_⟩
  rw [step78DataOf_path hs.1]
  exact hfar v hv

end ElboimSly.Paper.Step

end
