/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.EscapeProb
public import ElboimSly.Foundations.SRW.EscapeNum
public import ElboimSly.Foundations.SRW.KernelOneD
public import ElboimSly.Foundations.SRW.ReversalMain
public import Mathlib

/-!
# Escape from the boundary

Escape from the boundary.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

/-- The set `D_L` of integers in `[L/40, L - 1 - L/40]`. -/
noncomputable def escD (L : ℤ) : Finset ℤ := Finset.Icc ⌈(L : ℝ) / 40⌉ ⌊(L : ℝ) - 1 - L / 40⌋

theorem mem_escD {L a : ℤ} : a ∈ escD L ↔ (L : ℝ) / 40 ≤ a ∧ (a : ℝ) ≤ L - 1 - L / 40 := by
  simp only [escD, Finset.mem_Icc, Int.ceil_le, Int.le_floor]

theorem sum_kernel1_ge (J : Set ℤ) (s : ℝ≥0) (y : ℤ) (F : Finset ℤ) (T : Set (srwΩ 1))
    (hT : ∀ ω ∈ T, ∃ a ∈ F, srwZ 1 ω ∈ kerSet {v : Fin 1 → ℤ | v 0 ∈ J} s (fun _ => y)
      (fun _ => a)) :
    (srwP 1).real T ≤ ∑ a ∈ F, kernel1 J s y a := by
  have hY := srwZ_isSRW 1
  have := hY.isProbabilityMeasure
  set E : ℤ → Set (srwΩ 1) := fun a => {ω | srwZ 1 ω ∈ kerSet {v : Fin 1 → ℤ | v 0 ∈ J} s
    (fun _ => y) (fun _ => a)} with hE
  have hdisj : PairwiseDisjoint (↑F) E := by
    intro a _ b _ hab
    refine Set.disjoint_left.2 fun ω h1 h2 => hab ?_
    have := h1.1.symm.trans h2.1
    have := congrFun this 0
    simpa using this
  have hm : ∀ a ∈ F, MeasurableSet (E a) := fun a _ =>
    hY.measurableSet_event (isRegSet_kerSet _ _ _ _)
  calc (srwP 1).real T ≤ (srwP 1).real (⋃ a ∈ F, E a) := by
        refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
        obtain ⟨a, ha, h⟩ := hT ω hω
        exact mem_iUnion₂.2 ⟨a, ha, h⟩
    _ = ∑ a ∈ F, (srwP 1).real (E a) := measureReal_biUnion_finset hdisj hm
    _ = ∑ a ∈ F, kernel1 J s y a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rfl

/-- The deterministic content: a path in `Gfrom` started at `y' ≤ (L-1)/2` stays in `[0, L-1]`
and ends in `D_L`. -/
theorem escape_J {L : ℤ} (hL : 6000 ≤ L) {I : ℕ} (hlt : ell (I - 1) < (L : ℝ) / 40)
    (hI1 : 1 ≤ I) (hge : (L : ℝ) / 40 ≤ ell I) {γ : PathSpace 1} (hγ : IsRegularPath γ)
    (hG : γ ∈ Gfrom win gamV 0 (I + 1)) {y : ℤ} (hy0 : 0 ≤ y) (hy1 : 2 * y ≤ L - 1) :
    (∀ s : ℝ≥0, s ≤ tau (I + 1) → 0 ≤ y + γ s 0 ∧ y + γ s 0 ≤ L - 1) ∧
      (L : ℝ) / 40 ≤ (y : ℝ) + (γ (tau (I + 1)) 0 : ℝ) ∧
      ((y : ℝ) + (γ (tau (I + 1)) 0 : ℝ) ≤ L - 1 - L / 40) := by
  obtain ⟨h0, hW⟩ := mem_Gfrom_regular I 0 hγ hG
  have hW' : ∀ j < I, SRW.theta (tau (j + 1)) γ ∈ gamWin (rhoN j) := by
    intro j hj
    have := hW j hj
    simpa [tau, gamK] using this
  have h0' : γ ∈ gam0 := h0
  obtain ⟨ih1, ih2⟩ := escape_induction h0' hW' hy0 I le_rfl
  have hLr : (6000 : ℝ) ≤ L := by exact_mod_cast hL
  have hy1r : 2 * (y : ℝ) ≤ L - 1 := by exact_mod_cast hy1
  have hell1 : ell I = 37 / 36 * ell (I - 1) := by
    have := ell_succ (I - 1)
    rwa [show I - 1 + 1 = I by omega] at this
  have hell2 : ell I < 37 / 36 * ((L : ℝ) / 40) := by
    rw [hell1]; gcongr
  have hbound : (y : ℝ) + 18 * ell I ≤ L - 1 - L / 40 := by nlinarith
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨a, b⟩ := ih1 s hs
    refine ⟨by exact_mod_cast a, ?_⟩
    have : ((y + γ s 0 : ℤ) : ℝ) ≤ L - 1 := by push_cast; linarith
    exact_mod_cast this
  · linarith
  · obtain ⟨a, b⟩ := ih1 (tau (I + 1)) le_rfl
    linarith

theorem escape_aux {L : ℤ} (hL : 6000 ≤ L) {I : ℕ} (hlt : ell (I - 1) < (L : ℝ) / 40)
    (hI1 : 1 ≤ I) (hge : (L : ℝ) / 40 ≤ ell I) (y : ℤ) (hy : y ∈ Icc (0 : ℤ) (L - 1)) :
    ∃ T : Set (srwΩ 1), (srwP 1).real T ≤ ∑ a ∈ escD L, kernel1 (Icc 0 (L - 1)) (tau (I + 1)) y a ∧
      Real.exp (-2) / (72 : ℕ).factorial * (1 / 1100) ^ I ≤ (srwP 1).real T := by
  have hY := srwZ_isSRW 1
  rcases le_or_gt (2 * y) (L - 1) with h | h
  · refine ⟨{ω | srwZ 1 ω ∈ Gfrom win gamV 0 (I + 1)}, ?_, hY.prob_G I⟩
    refine sum_kernel1_ge _ _ _ _ _ fun ω hω => ?_
    obtain ⟨hb, hl, hu⟩ := escape_J hL hlt hI1 hge (hY.2.1 ω) hω hy.1 h
    refine ⟨y + srwZ 1 ω (tau (I + 1)) 0, mem_escD.2 ⟨by push_cast; exact hl, ?_⟩, ?_, fun s hs => ?_⟩
    · push_cast; exact hu
    · funext i; rw [Subsingleton.elim i 0]; simp
    · simp only [mem_ofPred_eq, mem_Icc]
      exact hb s hs
  · -- reflect
    have hneg := hY.map_signedPerm (negPerm 1) (negAddMonoidHom) (fun v => by
      simp [vec_negPerm])
    refine ⟨{ω | (fun s => negAddMonoidHom (srwZ 1 ω s) : PathSpace 1) ∈
      Gfrom win gamV 0 (I + 1)}, ?_, hneg.prob_G I⟩
    refine sum_kernel1_ge _ _ _ _ _ fun ω hω => ?_
    have hreg : IsRegularPath (fun s => negAddMonoidHom (srwZ 1 ω s) : PathSpace 1) :=
      hneg.2.1 ω
    obtain ⟨hb, hl, hu⟩ := escape_J hL hlt hI1 hge hreg hω (y := L - 1 - y)
      (by have := hy.2; omega) (by omega)
    simp only [negAddMonoidHom_apply, Pi.neg_apply] at hb hl hu
    refine ⟨y + srwZ 1 ω (tau (I + 1)) 0, mem_escD.2 ⟨?_, ?_⟩, ?_, fun s hs => ?_⟩
    · push_cast at hu ⊢; linarith
    · push_cast at hl ⊢; linarith
    · funext i; rw [Subsingleton.elim i 0]; simp
    · simp only [mem_ofPred_eq, mem_Icc]
      have := hb s hs
      simp only [Pi.add_apply]
      omega

/-- Escape from the boundary. -/
theorem escape {L : ℤ} (hL : 6000 ≤ L) :
    ∃ s₁ : ℝ≥0, 1 ≤ s₁ ∧ (s₁ : ℝ) ≤ (L : ℝ) ^ 2 / 20000 ∧
      ∀ y ∈ Icc (0 : ℤ) (L - 1),
        Real.exp (-2) / ((72 : ℕ).factorial * 1100) / (L : ℝ) ^ 256 ≤
          ∑ a ∈ escD L, kernel1 (Icc 0 (L - 1)) s₁ y a := by
  obtain ⟨I, hI1, hlt, hge, hs1, hs2, hpow⟩ := escape_params hL
  refine ⟨tau (I + 1), by exact_mod_cast hs2, hs1, fun y hy => ?_⟩
  obtain ⟨T, hT1, hT2⟩ := escape_aux hL hlt hI1 hge y hy
  refine le_trans ?_ (hT2.trans hT1)
  have hLr : (6000 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < (L : ℝ) ^ 256 := by positivity
  have hF : (0 : ℝ) < ((72 : ℕ).factorial : ℝ) := by positivity
  have h1 : (1 / 1100 : ℝ) ^ (I - 1) ≥ 1 / (L : ℝ) ^ 256 := by
    rw [one_div_pow, ge_iff_le]
    exact one_div_le_one_div_of_le (by positivity) hpow
  have e : (1 / 1100 : ℝ) ^ I = (1 / 1100) ^ (I - 1) * (1 / 1100) := by
    rw [← pow_succ, Nat.sub_add_cancel hI1]
  rw [e]
  have hE := Real.exp_pos (-2)
  calc Real.exp (-2) / ((72 : ℕ).factorial * 1100) / (L : ℝ) ^ 256
      = Real.exp (-2) / (72 : ℕ).factorial * (1 / (L : ℝ) ^ 256 * (1 / 1100)) := by
        field_simp
    _ ≤ Real.exp (-2) / (72 : ℕ).factorial * ((1 / 1100) ^ (I - 1) * (1 / 1100)) := by
        gcongr

end SRW
end ElboimSly
