/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.BlockSym
public import ElboimSly.Paper.Step.TravelLaw
public import Mathlib

/-!
# The driving segments of Lemma 7.6

ES22 Lemma 7.6, Step 1; a driving path from independent segments.

`RegSeg d` is the space `E` of the written proof: regular paths, with the subspace `σ`-algebra.
`winSeg X t T` is the window `u ↦ (θ_t X)(u ∧ T)` of a driving path as an element of `E`; for an SRW
the windows `winSeg X (iT) T` (`i < ℓ`) are independent with a common law `ν` (`iIndepFun_winSeg`,
`map_winSeg`). `segY` is the block functional `Y` on `E` and `map_segY` identifies the law of
`Y` under `ν` with that of `blockY` under `ppLaw`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

/-- Laws on a subtype are determined by the laws of the underlying maps. -/
theorem map_subtype_congr {α Ω Ω' : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {p : α → Prop} {P : Measure Ω} {P' : Measure Ω'} {f : Ω → Subtype p}
    {g : Ω' → Subtype p} (hf : Measurable f) (hg : Measurable g)
    (h : P.map (fun ω => (f ω).1) = P'.map (fun ω => (g ω).1)) : P.map f = P'.map g := by
  ext A hA
  obtain ⟨A', hA', rfl⟩ := hA
  rw [Measure.map_apply hf ⟨A', hA', rfl⟩, Measure.map_apply hg ⟨A', hA', rfl⟩]
  have h1 := congrArg (fun μ => μ A') h
  have e1 := Measure.map_apply (μ := P) (measurable_subtype_coe.comp hf) hA'
  have e2 := Measure.map_apply (μ := P') (measurable_subtype_coe.comp hg) hA'
  simp only [Function.comp_def] at e1 e2
  rw [e1, e2] at h1
  exact h1

/-- The space `E` of driving segments: regular paths. -/
abbrev RegSeg (d : ℕ) : Type := {y : ℝ≥0 → Fin d → ℤ // IsRegPath y}

section Windows

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → PathSpace d}

/-- The window `u ↦ (θ_t X)(u ∧ T)` as a driving segment. -/
def winSeg (hX : ∀ ω, X ω ∈ StepPath d) (t T : ℝ≥0) (ω : Ω) : RegSeg d :=
  ⟨stepWin t T (X ω), (isDrivingPath_stepWin (hX ω) t T).toIsRegPath⟩

theorem measurable_winSeg (hX : IsSRW P X) (hXp : ∀ ω, X ω ∈ StepPath d) (t T : ℝ≥0) :
    Measurable (winSeg hXp t T) :=
  ((measurable_stepWin t T).comp hX.1).subtype_mk

theorem iIndepFun_winSeg (hX : IsSRW P X) (hXp : ∀ ω, X ω ∈ StepPath d) (T : ℝ≥0) (ℓ : ℕ) :
    iIndepFun (fun (i : Fin ℓ) => winSeg hXp ((i : ℕ) * T) T) P := by
  have h0 := iIndepFun_stepWin hX (fun j : ℕ => (j : ℝ≥0) * T) (fun _ => T) (fun j => by
    push_cast; rw [add_mul, one_mul])
  have h1 := iIndepFun_subtype_lift (p := IsRegPath)
    (fun (j : ℕ) ω => stepWin ((j : ℝ≥0) * T) T (X ω))
    (fun j ω => (isDrivingPath_stepWin (hXp ω) _ _).toIsRegPath) h0
  exact h1.precomp (g := fun i : Fin ℓ => (i : ℕ)) Fin.val_injective

theorem map_winSeg (hX : IsSRW P X) (hXp : ∀ ω, X ω ∈ StepPath d) (t T : ℝ≥0) :
    P.map (winSeg hXp t T) = P.map (winSeg hXp 0 T) := by
  refine map_subtype_congr (measurable_winSeg hX hXp t T) (measurable_winSeg hX hXp 0 T) ?_
  exact (map_stepWin hX t T).trans (map_stepWin hX 0 T).symm

end Windows

variable {β : ℝ} [Fact (0 < β)]

/-- The block functional `Y` on driving segments: `T^{-1/2} 𝟙{sup_{s ≤ T} ‖W(s)‖ < K} W(T)` for the
regenerated walk `W` driven by the segment. -/
noncomputable def segY (β : ℝ) (T : ℝ≥0) (K : ℝ) (y : RegSeg d) : Fin d → ℝ :=
  blockY T K (stepReg β y.1)

theorem measurable_segY (T : ℝ≥0) (K : ℝ) : Measurable (segY (d := d) β T K) := by
  have hΦ : Measurable fun x : RegSeg d => stepReg β x.1 :=
    measurable_pi_iff.2 (measurable_drivenRegenFrom_subtype toNNReal_pos')
  exact (measurable_blockY T K).comp hΦ

omit [Fact (0 < β)] in
theorem segY_eq (T : ℝ≥0) (K : ℝ) (y : RegSeg d) :
    segY β T K y = blockY T K (stepRegStopped β T y.1) := by
  unfold segY blockY
  have : truncEnd T K (stepRegStopped β T y.1) = truncEnd T K (stepReg β y.1) :=
    truncEnd_stop T K (stepReg β y.1)
  rw [this]

section Law

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → PathSpace d}
  {Ωe : Type} [MeasurableSpace Ωe] {Pe : Measure Ωe} {N : Ωe → Measure (ℕ × RingSpace d β)}

/-- The law of the block functional of a window is that of `blockY` under `ppLaw`. -/
theorem map_segY (hX : IsSRW P X) (hXp : ∀ ω, X ω ∈ StepPath d)
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (T : ℝ≥0) (K : ℝ) (t : ℝ≥0) :
    (P.map (winSeg hXp t T)).map (segY β T K) = (ppLaw Pe N T).map (blockY T K) := by
  rw [Measure.map_map (measurable_segY T K) (measurable_winSeg hX hXp t T)]
  have e : (segY β T K ∘ winSeg hXp t T) =
      blockY T K ∘ fun ω => stepWj β t (fun _ => T) (X ω) 0 := by
    funext ω
    simp only [Function.comp_apply, segY_eq]
    congr 1
    have h := stepWj_eq (β := β) (hXp ω) t (fun _ => T) 0
    have hP : stepPartial (fun _ : ℕ => T) 0 = 0 := by simp [stepPartial]
    rw [hP, add_zero] at h
    exact h.symm
  rw [e, ← Measure.map_map (measurable_blockY T K)
    (measurable_stepWj (β := β) hX hXp t (fun _ => T) 0),
    map_stepWj_ppLaw (β := β) hX hXp hN t (fun _ => T) 0]

end Law

end ElboimSly.Paper.Step
