/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.Hitting
public import Mathlib

/-!
# Iterated hitting times with gaps

Proximity times of an independent walk (the stopping times `ζ_i`), hitting times of adapted step processes.

`hitSeq Y K h i` is the sequence `ζ_0 = 0`, `ζ_{i+1} = inf {t ≥ ζ_i + h : Y(t) ∈ K}`.  Each `ζ_i`
is a stopping time, and a time `s` with `Y(s) ∈ K` lies in some `[ζ_i, ζ_i + h)` with `i < N` as
soon as `ζ_N = ∞` (the covering step of the written proof proof).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Paper.Base ElboimSly.SRW

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {k : ℕ}

/-- Proximity times of an independent walk: `ζ_0 = 0` and `ζ_{i+1} = inf {t ≥ ζ_i + h : Y(t) ∈ K}`. -/
noncomputable def hitSeq (Y : Ω → ℝ≥0 → Fin k → ℤ) (K : Ω → Set (Fin k → ℤ)) (h : ℝ≥0) :
    ℕ → Ω → WithTop ℝ≥0
  | 0 => fun _ => 0
  | i + 1 => hitAfter Y K (hitSeq Y K h i) h

variable {Y : Ω → ℝ≥0 → Fin k → ℤ} {K : Ω → Set (Fin k → ℤ)} {h : ℝ≥0}

theorem hitSeq_zero (ω : Ω) : hitSeq Y K h 0 ω = 0 := rfl

theorem hitSeq_isStoppingTime (f : Filtration ℝ≥0 mΩ) (hY : ∀ t, Measurable[f t] fun ω => Y ω t)
    (hstep : ∀ ω, IsStepPath (Y ω)) (hK : ∀ z, MeasurableSet[f 0] {ω | z ∈ K ω}) :
    ∀ i, IsStoppingTime f (hitSeq Y K h i)
  | 0 => isStoppingTime_const f (0 : ℝ≥0)
  | i + 1 => hitAfter_isStoppingTime f (hitSeq_isStoppingTime f hY hstep hK i) hY hstep hK

/-- Covering step: if `Y(s) ∈ K(ω)` and `ζ_N(ω) = ∞`, then `s ∈ [ζ_i, ζ_i + h)` for some
`i < N` with `ζ_i < ∞`. -/
theorem exists_mem_hitSeq_Ico {ω : Ω} {N : ℕ}
    (hN : hitSeq Y K h N ω = ⊤) {s : ℝ≥0} (hs : Y ω s ∈ K ω) :
    ∃ i < N, hitSeq Y K h i ω ≠ ⊤ ∧ stopReal (hitSeq Y K h i) ω ≤ s ∧
      s < stopReal (hitSeq Y K h i) ω + h := by
  by_contra hcon
  push Not at hcon
  have key : ∀ i ≤ N, hitSeq Y K h i ω ≠ ⊤ ∧ stopReal (hitSeq Y K h i) ω ≤ s := by
    intro i
    induction i with
    | zero => intro _; exact ⟨by simp [hitSeq_zero], by simp [stopReal, hitSeq_zero]⟩
    | succ i ih =>
      intro hi
      obtain ⟨h1, h2⟩ := ih (by omega)
      have h3 := hcon i (by omega) h1 h2
      have hcell : ω ∈ hitCell Y K (hitSeq Y K h i) h s := ⟨⟨h1, h3⟩, hs⟩
      have hle := hitAfter_le_of_mem_hitCell hcell
      have hne : hitSeq Y K h (i + 1) ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle
      refine ⟨hne, ?_⟩
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hne
      have hle' : (t : WithTop ℝ≥0) ≤ s := ht ▸ hle
      have e : stopReal (hitSeq Y K h (i + 1)) ω = t := by
        simp only [stopReal, ← ht, WithTop.untopD_coe]
      rw [e]; exact WithTop.coe_le_coe.1 hle'
  exact (key N le_rfl).1 hN

end ElboimSly.Paper
