/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycHitCoupleDrivenRegen
public import ElboimSly.Foundations.Cyclic.DrivenWd
public import ElboimSly.Foundations.Cyclic.CycDrivenRegion
public import Mathlib

/-!
# Adaptedness of the driven regenerated walk

The driven regenerated walk (a) (pathwise part).

If two driving paths agree on `[0, T]`, their regeneration times up to `T` and their regenerated
walks on `[0, T]` agree (`drivenRegenFrom_causal`). So `w|_{[0,s]}` and the regeneration times in
`[0, s]` depend only on `x|_{[0,s]}`.
-/

@[expose] public section

open Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {b : ℝ≥0} {x y : ℝ≥0 → Fin d → ℤ}

theorem isDrivingPath_drivenPieces (hx : IsDrivingPath x) (n : ℕ) :
    IsDrivingPath (drivenPieces b x n) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact isDrivingPath_shiftPath ih _

/-- Causality of the pieces and regeneration times. -/
theorem drivenPieces_causal (hb : 0 < b) (hx : IsDrivingPath x) (hy : IsDrivingPath y) {T : ℝ≥0}
    (hxy : ∀ s ≤ T, x s = y s) (n : ℕ) :
    drivenSigma b x n ≤ T → drivenSigma b y n = drivenSigma b x n ∧
      ∀ s ≤ T - (drivenSigma b x n).toNNReal, drivenPieces b x n s = drivenPieces b y n s := by
  induction n with
  | zero =>
    intro _
    refine ⟨by simp [drivenSigma_zero], fun s hs => ?_⟩
    simpa [drivenSigma_zero, drivenPieces] using hxy s (by simpa [drivenSigma_zero] using hs)
  | succ n ih =>
    intro hle
    have hn : drivenSigma b x n ≤ T :=
      (drivenSigma_mono b x (Nat.le_succ n)).trans hle
    obtain ⟨hσ, hpc⟩ := ih hn
    have hnt : drivenSigma b x n < ⊤ := lt_of_le_of_lt hn ENNReal.coe_lt_top
    set a := (drivenSigma b x n).toNNReal with ha
    have hax : drivenSigma b x n = (a : ℝ≥0∞) := (ENNReal.coe_toNNReal hnt.ne).symm
    have hax' : a ≤ T := by rw [hax] at hn; exact_mod_cast hn
    have hP := isDrivingPath_drivenPieces (b := b) hx n
    have hQ := isDrivingPath_drivenPieces (b := b) hy n
    have hwalk := drivenWalk_congr (β := b) hP.toIsRegPath hQ.toIsRegPath hb hpc
    have hle' : a + drivenTreg b (drivenPieces b x n) ≤ T := by
      rw [drivenSigma_succ, hax] at hle; exact hle
    have htreg : drivenTreg b (drivenPieces b x n) ≤ ((T - a : ℝ≥0) : ℝ≥0∞) := by
      have : ((a : ℝ≥0∞)) + drivenTreg b (drivenPieces b x n) ≤ (a : ℝ≥0∞) + ((T - a : ℝ≥0) : ℝ≥0∞) := by
        refine hle'.trans ?_
        rw [← ENNReal.coe_add, add_tsub_cancel_of_le hax']
      exact (ENNReal.add_le_add_iff_left ENNReal.coe_ne_top).1 this
    have htr : drivenTreg b (drivenPieces b y n) = drivenTreg b (drivenPieces b x n) := by
      unfold drivenTreg
      refine pathTreg_congr hb fun s hs => (hwalk s ?_).symm
      have : (s : ℝ≥0∞) ≤ ((T - a : ℝ≥0) : ℝ≥0∞) := hs.trans htreg
      exact_mod_cast this
    have htop : drivenTreg b (drivenPieces b x n) < ⊤ :=
      lt_of_le_of_lt htreg ENNReal.coe_lt_top
    set τ := (drivenTreg b (drivenPieces b x n)).toNNReal with hτ
    have hτe : drivenTreg b (drivenPieces b x n) = (τ : ℝ≥0∞) := (ENNReal.coe_toNNReal htop.ne).symm
    have hτle : τ ≤ T - a := by rw [hτe] at htreg; exact_mod_cast htreg
    have hσx : (drivenSigma b x (n + 1)).toNNReal = a + τ := by
      rw [drivenSigma_succ, hax, hτe, ← ENNReal.coe_add, ENNReal.toNNReal_coe]
    refine ⟨?_, fun s hs => ?_⟩
    · rw [drivenSigma_succ, drivenSigma_succ, hσ, htr]
    · rw [hσx] at hs
      have hs' : s ≤ T - a - τ := by rw [tsub_tsub]; exact hs
      have hτs : τ + s ≤ T - a := by
        rw [le_tsub_iff_left hτle] at hs'; exact hs'
      change shiftPath (drivenPieces b x n) (drivenTreg b (drivenPieces b x n)).toNNReal s =
        shiftPath (drivenPieces b y n) (drivenTreg b (drivenPieces b y n)).toNNReal s
      rw [htr]
      unfold shiftPath
      rw [hpc (τ + s) hτs, hpc τ hτle]

/-- Causality of the driven regenerated walk: it depends on the driving path only through its
restriction to `[0, T]`, on `[0, T]`. -/
theorem drivenRegenFrom_causal (hb : 0 < b) (hx : IsDrivingPath x) (hy : IsDrivingPath y)
    {T : ℝ≥0} (hxy : ∀ s ≤ T, x s = y s) {s : ℝ≥0} (hs : s ≤ T) :
    drivenRegenFrom b x s = drivenRegenFrom b y s := by
  obtain ⟨h1, h2⟩ := gluedCount_spec' hb x s
  set n := gluedCount (drivenSigma b x) s with hn
  have hsT : (s : ℝ≥0∞) ≤ T := by exact_mod_cast hs
  obtain ⟨hσ, hpc⟩ := drivenPieces_causal hb hx hy hxy n (h1.trans hsT)
  have hy2 : (s : ℝ≥0∞) < drivenSigma b y (n + 1) := by
    by_contra hcon
    push Not at hcon
    have := (drivenPieces_causal hb hy hx (fun u hu => (hxy u hu).symm) (n + 1)
      (hcon.trans hsT)).1
    rw [this] at h2
    exact absurd h2 (not_lt.2 hcon)
  have hcnt : gluedCount (drivenSigma b y) s = n :=
    gluedCount_eq (drivenSigma_mono b y) (by rw [hσ]; exact h1) hy2
  unfold drivenRegenFrom drivenRegenWalk gluedWalk
  change drivenWalk b (drivenPieces b x (gluedCount (drivenSigma b x) s))
      (s - (drivenSigma b x (gluedCount (drivenSigma b x) s)).toNNReal) =
    drivenWalk b (drivenPieces b y (gluedCount (drivenSigma b y) s))
      (s - (drivenSigma b y (gluedCount (drivenSigma b y) s)).toNNReal)
  rw [hcnt, hσ, ← hn]
  exact drivenWalk_congr (β := b) (isDrivingPath_drivenPieces hx n).toIsRegPath
    (isDrivingPath_drivenPieces hy n).toIsRegPath hb hpc _ (tsub_le_tsub_right hs _)

end ElboimSly.Cyclic
