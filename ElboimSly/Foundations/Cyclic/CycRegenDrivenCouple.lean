/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenDrivenShift
public import ElboimSly.Foundations.Cyclic.CycHitCoupleDriven
public import Mathlib

/-!
# ES22 Lemma 2.1 (a), (b): the pathwise coupling for the regenerated walk

ES22 Lemma 2.1 (b). Let `x ∈ cycCF`, `V = W^x_reg`, `t_hit = drivenThit`.
Then `t_hit(t) = ∞` if `t = α(t)`; `t_hit(t) ≤ σ_{𝔑_t + 1}` if `t > α(t)`; and
`V(t + s) - V(t) = W^{x_t}_reg(s)` for all `s ∈ [0, t_hit(t) - t]`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {b : ℝ≥0} {x : ℝ≥0 → Fin d → ℤ}

/-- The hitting time of `x` at `σ_n + t'` is `σ_n` plus the hitting time of `x^{(n+1)}` at `t'`. -/
theorem drivenThit_shift (hb : 0 < b) {n : ℕ} (hn : drivenSigma b x n < ⊤) {t' : ℝ≥0}
    (ht' : (t' : ℝ≥0∞) < drivenTreg b (drivenPieces b x n))
    (hα : drivenRegenAlpha b x ((drivenSigma b x n).toNNReal + t') =
      (drivenSigma b x n).toNNReal) :
    drivenThit b x ((drivenSigma b x n).toNNReal + t') =
      (drivenSigma b x n).toNNReal + drivenThit b (drivenPieces b x n) t' := by
  set y := drivenPieces b x n with hy
  set a := (drivenSigma b x n).toNNReal with ha
  have hαy := drivenRegenAlpha_of_lt b y ht'
  have hQ : ∀ r, drivenRegenFrom b x (a + r) = drivenRegenFrom b y r := drivenRegenFrom_shift hb hn
  apply le_antisymm
  · calc drivenThit b x (a + t') ≤ ⨅ r ∈ {r : ℝ≥0 | t' < r ∧ ∃ k : ℤ, ∃ r' : ℝ≥0,
          (r' : ℝ) = r + k * b ∧ drivenRegenAlpha b y t' < r' ∧ r' < t' ∧
          ‖drivenRegenFrom b y r - drivenRegenFrom b y r'‖ ≤ 1}, (((a + r : ℝ≥0)) : ℝ≥0∞) := by
          refine le_iInf₂ fun r hr => ?_
          obtain ⟨htr, k, r', hk, hαr, hr't, hnorm⟩ := hr
          unfold drivenThit
          refine iInf₂_le_of_le (a + r) ?_ le_rfl
          refine ⟨add_lt_add_of_le_of_lt le_rfl htr, k, a + r', ?_, ?_, add_lt_add_of_le_of_lt le_rfl hr't, ?_⟩
          · push_cast; rw [hk]; ring
          · rw [hα]
            have : (0 : ℝ≥0) < r' := by rwa [hαy] at hαr
            exact lt_add_of_pos_right a this
          · rw [hQ, hQ]; exact hnorm
      _ = a + drivenThit b y t' := by
          unfold drivenThit
          simp only [ENNReal.coe_add, ENNReal.add_iInf]
  · refine le_iInf₂ fun s hs => ?_
    obtain ⟨hts, k, s', hk, hαs, hs't, hnorm⟩ := hs
    rw [hα] at hαs
    have has : a ≤ s := (le_add_of_nonneg_right zero_le).trans hts.le
    have has' : a ≤ s' := hαs.le
    obtain ⟨r, rfl⟩ : ∃ r, s = a + r := ⟨s - a, (add_tsub_cancel_of_le has).symm⟩
    obtain ⟨r', rfl⟩ : ∃ r', s' = a + r' := ⟨s' - a, (add_tsub_cancel_of_le has').symm⟩
    have hmem : r ∈ {r : ℝ≥0 | t' < r ∧ ∃ k : ℤ, ∃ r' : ℝ≥0,
          (r' : ℝ) = r + k * b ∧ drivenRegenAlpha b y t' < r' ∧ r' < t' ∧
          ‖drivenRegenFrom b y r - drivenRegenFrom b y r'‖ ≤ 1} := by
      refine ⟨lt_of_add_lt_add_left hts, k, r', ?_, ?_, lt_of_add_lt_add_left hs't, ?_⟩
      · have : ((a + r' : ℝ≥0) : ℝ) = ((a + r : ℝ≥0) : ℝ) + k * b := hk
        push_cast at this; linarith
      · rw [hαy]; exact (lt_add_iff_pos_right a).1 hαs
      · rw [← hQ, ← hQ]; exact hnorm
    have h1 : drivenThit b y t' ≤ r := by
      unfold drivenThit; exact iInf₂_le_of_le r hmem le_rfl
    push_cast
    exact add_le_add le_rfl h1

/-- Auxiliary form of (b) at `t = σ_n + t'`, where `σ_n = α(t)`. -/
theorem regen_couple_aux (hb : 0 < b) (hx : x ∈ CycCF b) {n : ℕ} (hn : drivenSigma b x n < ⊤)
    {t' : ℝ≥0}
    (hlt : (((drivenSigma b x n).toNNReal + t' : ℝ≥0) : ℝ≥0∞) < drivenSigma b x (n + 1))
    (hα : drivenRegenAlpha b x ((drivenSigma b x n).toNNReal + t') =
      (drivenSigma b x n).toNNReal) :
    (t' = 0 → drivenThit b x ((drivenSigma b x n).toNNReal + t') = ⊤) ∧
    (0 < t' → drivenThit b x ((drivenSigma b x n).toNNReal + t') ≤ drivenSigma b x (n + 1)) ∧
    ∀ s : ℝ≥0, (((drivenSigma b x n).toNNReal + t' + s : ℝ≥0) : ℝ≥0∞) ≤
        drivenThit b x ((drivenSigma b x n).toNNReal + t') →
      drivenRegenFrom b x ((drivenSigma b x n).toNNReal + t' + s) -
          drivenRegenFrom b x ((drivenSigma b x n).toNNReal + t') =
        drivenRegenFrom b (shiftPath x ((drivenSigma b x n).toNNReal + t')) s := by
  set y := drivenPieces b x n with hy
  set a := (drivenSigma b x n).toNNReal with ha
  have hna : drivenSigma b x n = (a : ℝ≥0∞) := (ENNReal.coe_toNNReal hn.ne).symm
  have hyc : y ∈ CycCF b := drivenPieces_mem_cycCF hx n hn
  have hyr : IsRegPath y := hyc.1.toIsRegPath
  have hyeq : y = shiftPath x a := drivenPieces_eq_shift b hx.1.zero n hn
  have hQ : ∀ r, drivenRegenFrom b x (a + r) = drivenRegenFrom b y r :=
    drivenRegenFrom_shift hb hn
  have hsucc : drivenSigma b x (n + 1) = (a : ℝ≥0∞) + drivenTreg b y := by
    rw [drivenSigma_succ, hna]
  have ht'τ : (t' : ℝ≥0∞) < drivenTreg b y := by
    rw [hsucc] at hlt
    push_cast at hlt
    exact (ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top).1 hlt
  have hV0 : drivenRegenFrom b y 0 = 0 := by
    rw [drivenRegenFrom_eq_walk_of_le hb hyr (by simp), drivenWalk_zero hyr hb]
  by_cases ht0 : t' = 0
  · subst ht0
    have htop : drivenThit b x (a + 0) = ⊤ := by
      refine top_unique (le_iInf₂ fun s hs => ?_)
      obtain ⟨-, k, s', -, hαs, hs't, -⟩ := hs
      rw [hα] at hαs
      rw [add_zero] at hs't
      exact absurd (hαs.trans hs't) (lt_irrefl _)
    refine ⟨fun _ => htop, fun h => absurd h (lt_irrefl _), fun s _ => ?_⟩
    rw [add_zero, hQ, ← add_zero a, hQ, add_zero, hV0, sub_zero, ← hyeq]
  · have ht0' : 0 < t' := pos_iff_ne_zero.2 ht0
    have hyc' : y ∈ CycCF b := hyc
    have hcor := cyc_hit_couple_driven hb hyc' ht0' ht'τ
    have hthit := drivenThit_shift hb hn ht'τ hα
    refine ⟨fun h => absurd h ht0, fun _ => ?_, fun s hs => ?_⟩
    · rw [hthit, hsucc]
      exact add_le_add le_rfl hcor.1
    · rw [hthit] at hs
      have hs' : ((t' + s : ℝ≥0) : ℝ≥0∞) ≤ drivenThit b y t' := by
        push_cast at hs ⊢
        rw [add_assoc] at hs
        exact (ENNReal.add_le_add_iff_left ENNReal.coe_ne_top).1 hs
      have hts : (((t' + s : ℝ≥0)) : ℝ≥0∞) ≤ drivenTreg b y := hs'.trans hcor.1
      have hy' : shiftPath y t' = shiftPath x (a + t') := by rw [hyeq, shiftPath_add]
      have hsy' : (s : ℝ≥0∞) ≤ drivenTreg b (shiftPath y t') := by
        by_cases htop : drivenThit b y t' = ⊤
        · rw [hcor.2.1 htop]; exact le_top
        · have h1 := hcor.2.2.1 (lt_top_iff_ne_top.2 htop)
          have h2 : ((t' + s : ℝ≥0) : ℝ≥0∞) < t' + drivenTreg b (shiftPath y t') :=
            lt_of_le_of_lt hs' h1
          push_cast at h2
          exact ((ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top).1 h2).le
      have hy'c : IsRegPath (shiftPath y t') := isRegPath_shiftPath hyr t'
      have hdw := hcor.2.2.2 s hs'
      rw [add_assoc, hQ, hQ, ← hy', drivenRegenFrom_eq_walk_of_le hb hyc.1.toIsRegPath hts,
        drivenRegenFrom_eq_walk_of_le hb hyc.1.toIsRegPath ht'τ.le,
        drivenRegenFrom_eq_walk_of_le hb hy'c hsy', hdw]

end ElboimSly.Cyclic

end
