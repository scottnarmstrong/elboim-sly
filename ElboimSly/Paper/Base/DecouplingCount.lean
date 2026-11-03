/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.ContactMain
public import ElboimSly.Foundations.SRW.WindowCount
public import Mathlib

/-!
# Decoupling the second particle: counting

Decoupling the second particle.

* `ncard_jumps_le_winCount`: the number of jump times of `X_j` in `(l, l+2]` is at most
  `N^j(D × (l, l+2])`.
* `prob_windows`: the event `H^c`, that some `N^j(D × (l, l+2])` with `l ∈ ℤ ∩ [0, T]` exceeds
  `n⁵`, has probability at most `2(T+1) e^{4d(e-1) - n⁵}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base ElboimSly.SRW

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}

/-- The event `H`: all window counts `N^j(D × (l, l+2])`, `l ∈ ℕ`, `l ≤ T`, are at most `n⁵`. -/
def windowsOK (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) (T : ℝ≥0) (n : ℕ) : Set Ω :=
  {ω | ∀ l : ℕ, (l : ℝ≥0) ≤ T → ∀ j : Fin 2,
    winCount (subProcess Ñ j) (l : ℝ) ((l : ℝ) + 2) ω ≤ n ^ 5}

omit [MeasurableSpace Ω] in
theorem ncard_jumps_le_winCount {ω : Ω} (hG : ω ∈ drvGood Ñ) (j : Fin 2) (l : ℕ) :
    (CDisc (drvX Ñ j ω) ∩ Ioc (l : ℝ≥0) ((l : ℝ≥0) + 2)).ncard ≤
      winCount (subProcess Ñ j) (l : ℝ) ((l : ℝ) + 2) ω := by
  have hI : Ioc (l : ℝ≥0) ((l : ℝ≥0) + 2) ⊆ Iic ((l : ℝ≥0) + 2) := Ioc_subset_Iic_self
  have h1 := drivers_ncard_jumps_le (Ñ := Ñ) j ω hI
  have himg : ((↑) : ℝ≥0 → ℝ) '' Ioc (l : ℝ≥0) ((l : ℝ≥0) + 2) = Ioc (l : ℝ) ((l : ℝ) + 2) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨x.toNNReal, ⟨?_, ?_⟩, Real.coe_toNNReal _ (by linarith [(Nat.cast_nonneg l : (0:ℝ) ≤ l)])⟩
      · exact (Real.lt_toNNReal_iff_coe_lt).2 (by simpa using hx1)
      · exact (Real.toNNReal_le_iff_le_coe).2 (by simpa using hx2)
  rw [himg] at h1
  have hgood : subProcess Ñ j ω ∈ goodSet d := by
    fin_cases j
    · exact hG.1
    · exact hG.2.1
  have h3 : ((winCount (subProcess Ñ j) (l : ℝ) ((l : ℝ) + 2) ω : ℕ) : ℝ≥0∞) =
      tot (subProcess Ñ j ω) (Ioc (l : ℝ) ((l : ℝ) + 2)) :=
    (good_tot_Ioc hgood (Nat.cast_nonneg l)).natCast_natOf
  rw [← h3] at h1
  exact_mod_cast h1

theorem prob_windows (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P)
    (T : ℝ≥0) (n : ℕ) :
    P (windowsOK Ñ T n)ᶜ ≤
      ENNReal.ofReal (2 * ((T : ℝ) + 1) * Real.exp (4 * d * (Real.exp 1 - 1) - (n : ℝ) ^ 5)) := by
  have := (drivers_isSRW h 0).isProbabilityMeasure
  set L := ⌊(T : ℝ)⌋₊ with hL
  have hsub : (windowsOK Ñ T n)ᶜ ⊆ ⋃ p : Fin (L + 1) × Fin 2,
      {ω | ((n ^ 5 : ℕ) : ℝ) ≤ (winCount (subProcess Ñ p.2) (p.1 : ℕ) ((p.1 : ℕ) + 2) ω : ℝ)} := by
    intro ω hω
    simp only [windowsOK, mem_compl_iff, mem_ofPred_eq, not_forall] at hω
    obtain ⟨l, hl, j, hj⟩ := hω
    have hlL : l ≤ L := by
      rw [hL]; exact Nat.le_floor (by exact_mod_cast hl)
    refine mem_iUnion.2 ⟨(⟨l, Nat.lt_succ_of_le hlL⟩, j), ?_⟩
    simp only [mem_ofPred_eq]
    exact_mod_cast (not_le.1 hj).le
  have hterm : ∀ p : Fin (L + 1) × Fin 2,
      P {ω | ((n ^ 5 : ℕ) : ℝ) ≤ (winCount (subProcess Ñ p.2) (p.1 : ℕ) ((p.1 : ℕ) + 2) ω : ℝ)} ≤
        ENNReal.ofReal (Real.exp (4 * d * (Real.exp 1 - 1) - (n : ℝ) ^ 5)) := by
    intro p
    have hN := subProcess_ppp h p.2
    have := winCount_tail hN (a := (p.1 : ℕ)) (b := (p.1 : ℕ) + 2) (Nat.cast_nonneg _)
      (by linarith) ((n ^ 5 : ℕ) : ℝ)
    calc P _ = ENNReal.ofReal (P.real _) := (ofReal_measureReal (measure_ne_top P _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
          refine this.trans (le_of_eq ?_)
          congr 1; push_cast; ring)
  calc P (windowsOK Ñ T n)ᶜ ≤ P (⋃ p : Fin (L + 1) × Fin 2, _) := measure_mono hsub
    _ ≤ ∑ p : Fin (L + 1) × Fin 2, P _ := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : Fin (L + 1) × Fin 2,
        ENNReal.ofReal (Real.exp (4 * d * (Real.exp 1 - 1) - (n : ℝ) ^ 5)) :=
        Finset.sum_le_sum fun p _ => hterm p
    _ = ENNReal.ofReal (2 * ((L : ℝ) + 1) * Real.exp (4 * d * (Real.exp 1 - 1) - (n : ℝ) ^ 5)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; push_cast; ring
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : (L : ℝ) ≤ T := Nat.floor_le T.2
        have hpos := Real.exp_pos (4 * d * (Real.exp 1 - 1) - (n : ℝ) ^ 5)
        nlinarith

end ElboimSly.Paper
