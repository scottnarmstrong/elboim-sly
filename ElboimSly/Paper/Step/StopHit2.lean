/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.StopHit
public import ElboimSly.Paper.Step.Driven
public import Mathlib

/-!
# The pathwise inclusion of ES22 Lemma 4.1

ES22 Lemma 4.1 (inclusion).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Cyclic
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

/-- **Inclusion step**: for a coincidence-free `x`, a relaxed time `t` of `W = W_reg^x`, and
`W' = W_reg^{θ_t x}`: `τ' ≥ n4` implies `thit(t) ≥ t + n4`. -/
theorem ofReal_add_le_stepThit {β : ℝ} [Fact (0 < β)] (hd : 1 ≤ d) (hβ1 : 1 < β)
    {x : ℝ≥0 → Fin d → ℤ} (hx : x ∈ StepCF (d := d) β) (t : ℝ≥0) {n4 : ℝ}
    (hrel : IsRelaxedTimeWrt β (stepExt fun s => stepReg β x s) (stepAlpha β x t : ℝ) (t : ℝ))
    (hit : ENNReal.ofReal n4 ≤ hitTime β (stepExt fun s => stepReg β x s) (stepAlpha β x t : ℝ)
      (t : ℝ) (fun r => stepExt (fun s => stepReg β x s) (t : ℝ) +
        stepReg β (stepShift t x) r.toNNReal)) :
    ENNReal.ofReal ((t : ℝ) + n4) ≤
      stepThit β (stepExt fun s => stepReg β x s) (fun r => (stepAlpha β x r.toNNReal : ℝ))
        (t : ℝ) := by
  have hβ0 : 0 < β := by linarith
  have hb0 : 0 < β.toNNReal := toNNReal_pos'
  have hβ : (β.toNNReal : ℝ) = β := Real.coe_toNNReal _ hβ0.le
  set wx : ℝ → Fin d → ℤ := stepExt fun s => stepReg β x s with hwx
  set αx : ℝ → ℝ := fun r => (stepAlpha β x r.toNNReal : ℝ) with hαx
  have hxd : IsDrivingPath x := hx.1
  have hreg : IsRegPath (stepReg β x) := isRegPath_stepReg hxd.toIsRegPath
  have hreg' : IsRegPath (stepReg β (stepShift t x)) :=
    isRegPath_stepReg (isDrivingPath_shiftPath hxd t).toIsRegPath
  have hrc : ∀ s : ℝ, ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), wx s' = wx s := fun s =>
    exists_Ico_const_stepExt hreg.rc s
  have hαt : αx (t : ℝ) = (stepAlpha β x t : ℝ) := by simp [hαx]
  have hrel' : IsRelaxedTimeWrt β wx (αx (t : ℝ)) (t : ℝ) := by simpa [hαx] using hrel
  have hgt := stepThit_gt_of_relaxed hd hβ1 (α := αx) hrc t.2 hrel'
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨h, hh⟩ : ∃ h, stepThit β wx αx (t : ℝ) = h := ⟨_, rfl⟩
  have hgt : ENNReal.ofReal t < h := by rw [← hh]; exact hgt
  have hlt : h < ENNReal.ofReal (t + n4) := by rw [← hh]; exact hlt
  have hhtop : h ≠ ⊤ := ne_top_of_lt (hlt.trans ENNReal.ofReal_lt_top)
  set hr := h.toReal with hhr
  have hhe : h = ENNReal.ofReal hr := (ENNReal.ofReal_toReal hhtop).symm
  rw [hhe] at hgt hlt
  have h1 : (t : ℝ) < hr := ((ENNReal.ofReal_lt_ofReal_iff').1 hgt).1
  have h2 : hr < (t : ℝ) + n4 := ((ENNReal.ofReal_lt_ofReal_iff').1 hlt).1
  obtain ⟨ε1, hε1, hc1⟩ := hrc hr
  obtain ⟨ε2, hε2, hc2⟩ := exists_Ico_const_stepExt hreg'.rc (hr - t)
  set η := min (min ε1 ε2) (((t : ℝ) + n4 - hr) / 2) with hη
  have hη0 : 0 < η := lt_min (lt_min hε1 hε2) (by linarith)
  have hηε1 : η ≤ ε1 := (min_le_left _ _).trans (min_le_left _ _)
  have hηε2 : η ≤ ε2 := (min_le_left _ _).trans (min_le_right _ _)
  have hηn : η ≤ ((t : ℝ) + n4 - hr) / 2 := min_le_right _ _
  have hlt2 : h < ENNReal.ofReal (hr + η) := by
    rw [hhe]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  -- a witness `s` of the infimum below `hr + η`
  have hlt3 := hlt2
  rw [← hh] at hlt3
  unfold stepThit at hlt3
  rw [iInf_lt_iff] at hlt3
  obtain ⟨s, hlt3⟩ := hlt3
  rw [iInf_lt_iff] at hlt3
  obtain ⟨hs, hslt⟩ := hlt3
  obtain ⟨hts, s', ⟨k, hk⟩, hαs, hs't, hnorm⟩ := hs
  have hs0 : 0 ≤ s := le_trans t.2 hts.le
  have hhs : h ≤ ENNReal.ofReal s := by
    rw [← hh]; exact iInf₂_le s ⟨hts, s', ⟨k, hk⟩, hαs, hs't, hnorm⟩
  have hrs : hr ≤ s := by
    rw [hhe] at hhs; exact (ENNReal.ofReal_le_ofReal_iff hs0).1 hhs
  have hsη : s < hr + η := (ENNReal.ofReal_lt_ofReal_iff' |>.1 hslt).1
  -- the coupling at `hr`
  have hcpl : wx hr = wx t + stepExt (stepReg β (stepShift t x)) (hr - t) := by
    have hle : (((t + (hr - t).toNNReal : ℝ≥0)) : ℝ≥0∞) ≤ drivenThit β.toNNReal x t := by
      have e : (((t + (hr - t).toNNReal : ℝ≥0)) : ℝ≥0∞) = ENNReal.ofReal hr := by
        rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_add, Real.coe_toNNReal _ (by linarith)]
        congr 1; ring
      rw [e, ← hhe, ← hh]
      exact stepThit_le_drivenThit (β := β) (x := x) t
    have hb := (cyc_hit_couple_driven_regen_b hb0 hx t).2.2 (hr - t).toNNReal hle
    have e2 : t + (hr - t).toNNReal = hr.toNNReal := by
      rw [← NNReal.coe_inj, NNReal.coe_add, Real.coe_toNNReal _ (by linarith),
        Real.coe_toNNReal _ (by linarith)]
      ring
    rw [e2] at hb
    have : stepReg β x hr.toNNReal = stepReg β x t + stepReg β (shiftPath x t) (hr - t).toNNReal := by
      have := hb
      simp only [sub_eq_iff_eq_add'] at this
      exact this
    simpa [hwx, stepExt, stepShift] using this
  -- the walk at `s`
  have hws : wx s = wx (t : ℝ) + stepReg β (stepShift t x) (s - t).toNNReal := by
    have e1 : wx s = wx hr := hc1 s ⟨hrs, by linarith⟩
    have e2 : stepExt (stepReg β (stepShift t x)) (s - t) =
        stepExt (stepReg β (stepShift t x)) (hr - t) :=
      hc2 (s - t) ⟨by linarith, by linarith⟩
    rw [e1, hcpl]
    exact congrArg _ e2.symm
  -- hence `τ' < n4`
  have hmem : s - t ∈ {r : ℝ | 0 < r ∧ ∃ s'' : ℝ, (∃ k : ℤ, s'' = (t : ℝ) + r + k * β) ∧
      (stepAlpha β x t : ℝ) < s'' ∧ s'' < t ∧ ‖(fun r => wx (t : ℝ) +
        stepReg β (stepShift t x) r.toNNReal) r - wx s''‖ ≤ 1} := by
    refine ⟨by linarith, s', ⟨k, by rw [hk]; ring⟩, ?_, hs't, ?_⟩
    · have := hαs; rw [hαt] at this; exact this
    · simp only
      rw [← hws]; exact hnorm
  have h3 := hit.trans (iInf₂_le (s - t) hmem)
  have h4 : n4 ≤ s - t := (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h3
  linarith

end ElboimSly.Paper.Step
