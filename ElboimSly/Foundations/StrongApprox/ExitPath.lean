/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Exit times and the iterated embedding of continuous paths

Exit times and the iterated embedding; Exit times of continuous paths (Part II).

Paths are functions `ℝ≥0 → ℝ`. The exit time `exitTime ρ w` is the first time `s` with
`ρ ≤ |w s|` (in `[0,∞]`), `shiftAt τ w` the shifted path `w(τ + ·) - w(τ)`, and
`embPath r w i`, `embTau r w i`, `embX r w i` the paths, exit times and exit positions of the
iterated embedding of the moduli `r 0, r 1, …` (indices are shifted by one with respect to the
written proof).
-/

@[expose] public section

open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

/-- A path is in `C₀` if it is continuous and vanishes at `0`. -/
def IsC0 (w : ℝ≥0 → ℝ) : Prop := Continuous w ∧ w 0 = 0

open scoped Classical in
/-- Exit times and the iterated embedding. The exit time `inf {s ≥ 0 : ρ ≤ |w s|} ∈ [0,∞]`. -/
noncomputable def exitTime (ρ : ℝ) (w : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  if _ : ∃ s, ρ ≤ |w s| then ((sInf {s : ℝ≥0 | ρ ≤ |w s|} : ℝ≥0) : ℝ≥0∞) else ⊤

/-- Exit times and the iterated embedding. The shift `sh_τ w` (equal to `w` if `τ = ∞`). -/
noncomputable def shiftAt (τ : ℝ≥0∞) (w : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  if τ = ⊤ then w else fun s => w (τ.toNNReal + s) - w τ.toNNReal

/-- The position `w(τ)` (`0` if `τ = ∞`). -/
noncomputable def endVal (τ : ℝ≥0∞) (w : ℝ≥0 → ℝ) : ℝ :=
  if τ = ⊤ then 0 else w τ.toNNReal

/-- Exit times and the iterated embedding. The iterated embedding paths `w^{(i)}`. -/
noncomputable def embPath (r : ℕ → ℝ) (w : ℝ≥0 → ℝ) : ℕ → (ℝ≥0 → ℝ)
  | 0 => w
  | i + 1 => shiftAt (exitTime (r i) (embPath r w i)) (embPath r w i)

/-- The exit times `τ_i` of the iterated embedding (0-indexed). -/
noncomputable def embTau (r : ℕ → ℝ) (w : ℝ≥0 → ℝ) (i : ℕ) : ℝ≥0∞ :=
  exitTime (r i) (embPath r w i)

/-- The exit positions `X_i` of the iterated embedding (0-indexed). -/
noncomputable def embX (r : ℕ → ℝ) (w : ℝ≥0 → ℝ) (i : ℕ) : ℝ :=
  endVal (embTau r w i) (embPath r w i)

/-- The clocks `T_j = ∑_{i<j} τ_i`. -/
noncomputable def embClock (r : ℕ → ℝ) (w : ℝ≥0 → ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range j, embTau r w i

lemma embPath_succ (r : ℕ → ℝ) (w : ℝ≥0 → ℝ) (i : ℕ) :
    embPath r w (i + 1) = shiftAt (embTau r w i) (embPath r w i) := rfl

/-! ### Exit times -/

lemma exitTime_of_exists {ρ : ℝ} {w : ℝ≥0 → ℝ} (h : ∃ s, ρ ≤ |w s|) :
    exitTime ρ w = ((sInf {s : ℝ≥0 | ρ ≤ |w s|} : ℝ≥0) : ℝ≥0∞) := dite_eq_left h

lemma exitTime_of_not_exists {ρ : ℝ} {w : ℝ≥0 → ℝ} (h : ¬ ∃ s, ρ ≤ |w s|) :
    exitTime ρ w = ⊤ := dite_eq_right h

lemma exitTime_lt_top_iff {ρ : ℝ} {w : ℝ≥0 → ℝ} :
    exitTime ρ w < ⊤ ↔ ∃ s, ρ ≤ |w s| := by
  by_cases h : ∃ s, ρ ≤ |w s|
  · simp [exitTime_of_exists h, h]
  · simp [exitTime_of_not_exists h, h]

lemma bddBelow_exitSet (ρ : ℝ) (w : ℝ≥0 → ℝ) : BddBelow {s : ℝ≥0 | ρ ≤ |w s|} :=
  ⟨0, fun _ _ => bot_le⟩

lemma isClosed_exitSet {ρ : ℝ} {w : ℝ≥0 → ℝ} (hw : Continuous w) :
    IsClosed {s : ℝ≥0 | ρ ≤ |w s|} :=
  isClosed_le continuous_const (continuous_abs.comp hw)

/-- Exit times of continuous paths (a). -/
lemma exitTime_le_iff {ρ : ℝ} {w : ℝ≥0 → ℝ} (hw : Continuous w) (t : ℝ≥0) :
    exitTime ρ w ≤ (t : ℝ≥0∞) ↔ ∃ s ≤ t, ρ ≤ |w s| := by
  constructor
  · intro h
    have hlt : exitTime ρ w < ⊤ := lt_of_le_of_lt h ENNReal.coe_lt_top
    obtain ⟨s0, hs0⟩ := exitTime_lt_top_iff.1 hlt
    have hne : {s : ℝ≥0 | ρ ≤ |w s|}.Nonempty := ⟨s0, hs0⟩
    have hmem := (isClosed_exitSet hw).csInf_mem hne (bddBelow_exitSet _ _)
    rw [exitTime_of_exists ⟨s0, hs0⟩] at h
    exact ⟨_, ENNReal.coe_le_coe.1 h, hmem⟩
  · rintro ⟨s, hst, hs⟩
    rw [exitTime_of_exists ⟨s, hs⟩]
    exact ENNReal.coe_le_coe.2 ((csInf_le (bddBelow_exitSet _ _) hs).trans hst)

lemma exitTime_spec {ρ : ℝ} {w : ℝ≥0 → ℝ} (hw : Continuous w) (h : exitTime ρ w < ⊤) :
    ρ ≤ |w (exitTime ρ w).toNNReal| := by
  obtain ⟨s0, hs0⟩ := exitTime_lt_top_iff.1 h
  rw [exitTime_of_exists ⟨s0, hs0⟩, ENNReal.toNNReal_coe]
  exact (isClosed_exitSet hw).csInf_mem ⟨s0, hs0⟩ (bddBelow_exitSet _ _)

lemma lt_of_lt_exitTime {ρ : ℝ} {w : ℝ≥0 → ℝ} {s : ℝ≥0} (h : (s : ℝ≥0∞) < exitTime ρ w) :
    |w s| < ρ := by
  by_contra hc
  push Not at hc
  have : exitTime ρ w ≤ (s : ℝ≥0∞) := by
    rw [exitTime_of_exists ⟨s, hc⟩]
    exact ENNReal.coe_le_coe.2 (csInf_le (bddBelow_exitSet _ _) hc)
  exact absurd h (not_lt.2 this)

lemma exitTime_of_nonpos {ρ : ℝ} (hρ : ρ ≤ 0) (w : ℝ≥0 → ℝ) : exitTime ρ w = 0 := by
  have hA : {s : ℝ≥0 | ρ ≤ |w s|} = Set.univ := by
    ext s; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact hρ.trans (abs_nonneg _)
  rw [exitTime_of_exists ⟨0, hρ.trans (abs_nonneg _)⟩, hA]
  simp

lemma exitTime_neg (ρ : ℝ) (w : ℝ≥0 → ℝ) : exitTime ρ (fun s => -w s) = exitTime ρ w := by
  by_cases h : ∃ s, ρ ≤ |w s|
  · have h' : ∃ s, ρ ≤ |(fun s => -w s) s| := by simpa [abs_neg] using h
    rw [exitTime_of_exists h, exitTime_of_exists h']; simp [abs_neg]
  · have h' : ¬ ∃ s, ρ ≤ |(fun s => -w s) s| := by simpa [abs_neg] using h
    rw [exitTime_of_not_exists h, exitTime_of_not_exists h']

/-- Exit times of continuous paths (b): `|w(τ)| = ρ`. -/
lemma abs_endVal_exitTime {ρ : ℝ} {w : ℝ≥0 → ℝ} (hw : IsC0 w) (hρ : 0 ≤ ρ)
    (h : exitTime ρ w < ⊤) : |endVal (exitTime ρ w) w| = ρ := by
  rw [endVal, ite_eq_right h.ne]
  set e := (exitTime ρ w).toNNReal with he
  have hge : ρ ≤ |w e| := exitTime_spec hw.1 h
  rcases hρ.eq_or_lt with h0 | hpos
  · have hτ : exitTime ρ w = 0 := exitTime_of_nonpos h0.symm.le w
    have : e = 0 := by simp [he, hτ]
    rw [this, hw.2, ← h0]; simp
  · refine le_antisymm ?_ hge
    by_contra hlt
    push Not at hlt
    have he0 : 0 < e := by
      by_contra hz
      have h1 : e = 0 := le_antisymm (not_lt.1 hz) bot_le
      have h' : ρ < |w e| := hlt
      rw [h1, hw.2] at h'
      simp at h'
      linarith
    have hopen : IsOpen {s : ℝ≥0 | ρ < |w s|} :=
      isOpen_lt continuous_const (continuous_abs.comp hw.1)
    have hmem : e ∈ {s : ℝ≥0 | ρ < |w s|} := hlt
    have hev : ∀ᶠ s in nhdsWithin e (Set.Iio e), s ∈ {s : ℝ≥0 | ρ < |w s|} :=
      nhdsWithin_le_nhds (hopen.mem_nhds hmem)
    have hne : (nhdsWithin e (Set.Iio e)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, he0⟩
    obtain ⟨s, hs, hsl⟩ := (hev.and self_mem_nhdsWithin).exists
    have hs' : (s : ℝ≥0∞) < exitTime ρ w := by
      have : (s : ℝ≥0∞) < (e : ℝ≥0∞) := ENNReal.coe_lt_coe.2 hsl
      rwa [he, ENNReal.coe_toNNReal h.ne] at this
    have := lt_of_lt_exitTime hs'
    exact absurd hs (not_lt.2 this.le)

/-! ### Shifts -/

lemma shiftAt_top (w : ℝ≥0 → ℝ) : shiftAt ⊤ w = w := by simp [shiftAt]

lemma shiftAt_coe (a : ℝ≥0) (w : ℝ≥0 → ℝ) :
    shiftAt (a : ℝ≥0∞) w = fun s => w (a + s) - w a := by
  simp [shiftAt]

lemma isC0_shiftAt {w : ℝ≥0 → ℝ} (hw : IsC0 w) (τ : ℝ≥0∞) : IsC0 (shiftAt τ w) := by
  by_cases h : τ = ⊤
  · rw [h, shiftAt_top]; exact hw
  · simp only [shiftAt, ite_eq_right h]
    refine ⟨?_, by simp⟩
    exact (hw.1.comp (continuous_const.add continuous_id)).sub continuous_const

lemma shiftAt_shiftAt (a c : ℝ≥0) (w : ℝ≥0 → ℝ) :
    shiftAt (c : ℝ≥0∞) (shiftAt (a : ℝ≥0∞) w) = shiftAt ((a + c : ℝ≥0) : ℝ≥0∞) w := by
  simp only [shiftAt_coe]
  funext s
  simp only [add_assoc]
  ring

lemma endVal_neg (τ : ℝ≥0∞) (w : ℝ≥0 → ℝ) : endVal τ (fun s => -w s) = -endVal τ w := by
  by_cases h : τ = ⊤ <;> simp [endVal, h]

/-! ### The iterated embedding -/

lemma embClock_succ (r : ℕ → ℝ) (w : ℝ≥0 → ℝ) (j : ℕ) :
    embClock r w (j + 1) = embClock r w j + embTau r w j := by
  simp [embClock, Finset.sum_range_succ]

/-- Exit times of continuous paths (d): positions, clocks and the shift. -/
theorem embClock_spec {w : ℝ≥0 → ℝ} (hw : IsC0 w) (r : ℕ → ℝ) (j : ℕ)
    (hj : embClock r w j < ⊤) :
    embPath r w j = shiftAt (embClock r w j) w ∧
      ∑ i ∈ Finset.range j, embX r w i = w (embClock r w j).toNNReal := by
  induction j with
  | zero =>
    have h0 : embClock r w 0 = 0 := by simp [embClock]
    refine ⟨?_, by simp [h0, hw.2]⟩
    rw [h0]
    have := shiftAt_coe 0 w
    simp only [ENNReal.coe_zero] at this
    rw [this]; funext s; simp [hw.2]; rfl
  | succ j ih =>
    rw [embClock_succ] at hj
    have hj1 : embClock r w j < ⊤ := lt_of_le_of_lt le_self_add hj
    have hj2 : embTau r w j < ⊤ := lt_of_le_of_lt le_add_self hj
    obtain ⟨ih1, ih2⟩ := ih hj1
    set a := (embClock r w j).toNNReal with ha
    set c := (embTau r w j).toNNReal with hc
    have ha' : embClock r w j = (a : ℝ≥0∞) := (ENNReal.coe_toNNReal hj1.ne).symm
    have hc' : embTau r w j = (c : ℝ≥0∞) := (ENNReal.coe_toNNReal hj2.ne).symm
    have hcl : embClock r w (j + 1) = ((a + c : ℝ≥0) : ℝ≥0∞) := by
      rw [embClock_succ, ha', hc']; simp
    rw [ha'] at ih1
    refine ⟨?_, ?_⟩
    · rw [embPath_succ, ih1, hc', shiftAt_shiftAt, hcl]
    · have hX : embX r w j = w (a + c) - w a := by
        rw [embX, endVal, ite_eq_right hj2.ne, ih1, shiftAt_coe]
      rw [Finset.sum_range_succ, ih2, hcl, ENNReal.toNNReal_coe, hX]
      ring

end ElboimSly.StrongApprox
