/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.X1Path
public import ElboimSly.Foundations.Brownian.Oscillation
public import Mathlib

/-!
# The error event: a deterministic inclusion

The coupling error, proof (Part II).

If all clocks are finite, no Chernoff event occurs and no oscillation event occurs, then every
partial sum `∑_{i ≤ j} (X_i - Y_i)` has sup norm less than `Λ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

variable {d ℓ : ℕ}

/-- The unit increments on the coupling space. -/
noncomputable def Yvec (ω : Ω1 d ℓ) : Fin ℓ → Fin d → ℝ := unitIncr (Bd d) ℓ ω.2

/-- The partial sums `∑_{i ≤ j} (X_i - Y_i)`. -/
noncomputable def x1Spart (ω : Ω1 d ℓ) (j : Fin ℓ) : Fin d → ℝ :=
  ∑ i ∈ Finset.univ.filter (· ≤ j), (Xvec ω i - Yvec ω i)

/-- The clock event of coordinate `k`. -/
def ClockEvent (D : ℝ) (k : Fin d) : Set (Ω1 d ℓ) :=
  {ω | ∃ j : Fin ℓ, D ≤ |∑ i ∈ Finset.univ.filter (· ≤ j), ((Tp k (Vfull ℓ ω) i).toReal - 1)|}

/-- The oscillation event. -/
def OscEvent (T h : ℝ≥0) (Λ : ℝ) : Set (Ω1 d ℓ) :=
  {ω | ∃ s s' : ℝ≥0, s ≤ T ∧ s' ≤ T ∧ dist s s' ≤ h ∧
    Λ ≤ ‖(1 : ℝ) • Bd d s ω.2 - (1 : ℝ) • Bd d s' ω.2‖}

lemma x1Spart_apply (ω : Ω1 d ℓ) (j : Fin ℓ) (k : Fin d) :
    x1Spart ω j k = ∑ i ∈ Finset.univ.filter (· ≤ j), (Vfull ℓ ω k i).1 -
      ∑ i ∈ Finset.univ.filter (· ≤ j), unitIncr (Bd d) ℓ ω.2 i k := by
  simp only [x1Spart, Finset.sum_apply, Pi.sub_apply, Finset.sum_sub_distrib]
  rfl

lemma clockK_lt_top (k : Fin d) (ω : Ω1 d ℓ) (j : Fin ℓ)
    (hfin : ∀ i : Fin ℓ, (Vfull ℓ ω k i).2 < ⊤) : clockK k ω ((j : ℕ) + 1) < ⊤ := by
  rw [clockK, embClock]
  refine ENNReal.sum_lt_top.2 fun n hn => ?_
  exact hfin ⟨n, by have := Finset.mem_range.1 hn; have := j.2; omega⟩

/-- Off the three bad events, all partial sums are small. -/
theorem x1Spart_norm_lt {D Λ : ℝ} (hD : 0 ≤ D) (hΛ : 0 < Λ) (ω : Ω1 d ℓ)
    (hG0 : ∀ k i, Tp k (Vfull ℓ ω) i < ⊤)
    (hC : ∀ k, ω ∉ ClockEvent D k)
    (hO : ω ∉ OscEvent ((ℓ : ℝ≥0) + D.toNNReal) D.toNNReal Λ) (j : Fin ℓ) :
    ‖x1Spart ω j‖ < Λ := by
  refine (pi_norm_lt_iff hΛ).2 fun k => ?_
  have hfin : ∀ i : Fin ℓ, (Vfull ℓ ω k i).2 < ⊤ := fun i => hG0 k i
  have hcl := clockK_lt_top k ω j hfin
  set T : ℝ≥0 := (clockK k ω ((j : ℕ) + 1)).toNNReal with hT
  have hTR : (T : ℝ) = (clockK k ω ((j : ℕ) + 1)).toReal := rfl
  have hCk : |(clockK k ω ((j : ℕ) + 1)).toReal - ((j : ℕ) + 1)| < D := by
    have := hC k
    simp only [ClockEvent, Set.mem_ofPred_eq, not_exists, not_le] at this
    have h2 := this j
    simpa [Tp, sum_tau_eq k ω j hfin] using h2
  have hjℓ : ((j : ℕ) : ℝ) + 1 ≤ ℓ := by exact_mod_cast j.2
  set s' : ℝ≥0 := (((j : ℕ) + 1 : ℕ) : ℝ≥0) with hs'
  have hs'R : (s' : ℝ) = (j : ℕ) + 1 := by simp [hs']
  have hDR : ((D.toNNReal : ℝ≥0) : ℝ) = D := Real.coe_toNNReal _ hD
  have hOk : ¬ (Λ ≤ ‖(1 : ℝ) • Bd d T ω.2 - (1 : ℝ) • Bd d s' ω.2‖) := by
    intro hle
    apply hO
    refine ⟨T, s', ?_, ?_, ?_, hle⟩
    · rw [← NNReal.coe_le_coe]
      push_cast
      rw [hDR, hTR]
      have := (abs_lt.1 hCk).2
      linarith
    · rw [← NNReal.coe_le_coe]
      push_cast
      rw [hDR, hs'R]
      linarith
    · rw [NNReal.dist_eq, hDR, hTR, hs'R]
      exact hCk.le
  push Not at hOk
  rw [one_smul, one_smul] at hOk
  have hk : ‖x1Spart ω j k‖ = |Bd d T ω.2 k - Bd d s' ω.2 k| := by
    rw [x1Spart_apply, sum_X_eq k ω j hcl, sum_Y_eq k ω j, Real.norm_eq_abs]
  rw [hk]
  calc |Bd d T ω.2 k - Bd d s' ω.2 k| = ‖(Bd d T ω.2 - Bd d s' ω.2) k‖ := by
        rw [Real.norm_eq_abs]; rfl
    _ ≤ ‖Bd d T ω.2 - Bd d s' ω.2‖ := norm_le_pi_norm _ k
    _ < Λ := hOk

end ElboimSly.StrongApprox
