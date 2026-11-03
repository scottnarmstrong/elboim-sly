/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.SegmentsPath
public import ElboimSly.Paper.Step.DrivenSigma
public import ElboimSly.Foundations.Cyclic.CycDrivenRegenMeas
public import ElboimSly.Foundations.Cyclic.DrivenWalk
public import Mathlib

/-!
# The regenerated driven walk is a regular path

The driven regenerated walk (a) (and the last sentence of laws in the natural coupling): for a
regular path `x` the glued walk `drivenRegenFrom b x` is right-continuous with finitely many jumps
on bounded intervals; for a driving path it starts at `0`.
-/

@[expose] public section

open Filter Topology Set ElboimSly.Cyclic
open scoped NNReal ENNReal

namespace ElboimSly.Paper

variable {d : ℕ}

theorem isRegPath_drivenRegenFrom {b : ℝ≥0} (hb : 0 < b) {x : ℝ≥0 → Fin d → ℤ}
    (hx : IsRegPath x) : IsRegPath (drivenRegenFrom b x) where
  rc t := by
    obtain ⟨n, hn1, hn2⟩ := exists_gluedCount b hb x t
    set c : ℝ≥0 := (drivenSigma b x n).toNNReal with hc
    have hcσ : drivenSigma b x n = c := (ENNReal.coe_toNNReal (ne_top_of_le_ne_top
      ENNReal.coe_ne_top hn1)).symm
    have hp := drivenWalk_isRegPath (isRegPath_drivenPieces b hx n) hb
    have hct : c ≤ t := by rw [hcσ] at hn1; exact_mod_cast hn1
    have h1 := (tendsto_tsub_nhdsGE c t).eventually (hp.rc (t - c))
    have h2 : ∀ᶠ u : ℝ≥0 in 𝓝[≥] t, (u : ℝ≥0∞) < drivenSigma b x (n + 1) :=
      ((ENNReal.continuous_coe.tendsto t).eventually (gt_mem_nhds hn2)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [h1, h2, self_mem_nhdsWithin (a := t) (s := Ici t)] with u hu hu2 hut
    have hcu : (drivenSigma b x n) ≤ (u : ℝ≥0∞) := by
      rw [hcσ]; exact_mod_cast hct.trans hut
    rw [drivenRegenFrom_piece hcu hu2, drivenRegenFrom_piece hn1 hn2, ← hc, hu]
  fin T := by
    classical
    set M : ℕ := ⌈(T : ℝ≥0) / b⌉₊ + 1 with hM
    have hfin : (⋃ n ∈ Finset.range M, ({(drivenSigma b x n).toNNReal} ∪
        (fun v => (drivenSigma b x n).toNNReal + v) ''
          (CDisc (drivenWalk b (drivenPieces b x n)) ∩ Iic T) : Set ℝ≥0)).Finite := by
      refine Set.Finite.biUnion (Finset.finite_toSet _) fun n _ => ?_
      refine (Set.finite_singleton _).union ?_
      exact (((drivenWalk_isRegPath (isRegPath_drivenPieces b hx n) hb).fin T).image _)
    refine hfin.subset ?_
    rintro s ⟨⟨hs0, hs⟩, hsT⟩
    obtain ⟨n, hn1, hn2⟩ := exists_gluedCount b hb x s
    set c : ℝ≥0 := (drivenSigma b x n).toNNReal with hc
    have hcσ : drivenSigma b x n = c := (ENNReal.coe_toNNReal (ne_top_of_le_ne_top
      ENNReal.coe_ne_top hn1)).symm
    have hcs : c ≤ s := by rw [hcσ] at hn1; exact_mod_cast hn1
    have hnM : n < M := by
      have h := drivenSigma_ge b x n
      rw [hcσ] at h
      have h' : (n : ℝ≥0) * b ≤ c := by exact_mod_cast h
      have : (n : ℝ≥0) * b ≤ T := h'.trans (hcs.trans hsT)
      have h3 : (n : ℝ≥0) ≤ T / b := by rw [le_div_iff₀ hb]; exact this
      have := Nat.le_ceil ((T : ℝ≥0) / b)
      have h4 : n ≤ ⌈(T : ℝ≥0) / b⌉₊ := Nat.cast_le.1 (h3.trans this)
      omega
    simp only [mem_iUnion, mem_union, mem_singleton_iff, mem_image, mem_inter_iff, exists_prop]
    refine ⟨n, Finset.mem_range.2 hnM, ?_⟩
    rcases hcs.lt_or_eq with hlt | heq
    · right
      refine ⟨s - c, ⟨⟨tsub_pos_of_lt hlt, fun hev => hs ?_⟩, ?_⟩, ?_⟩
      · have h1 := (tendsto_tsub_nhdsLT hlt).eventually hev
        filter_upwards [h1, Ioo_mem_nhdsLT hlt] with u hu hu2
        have hu3 : (u : ℝ≥0∞) < drivenSigma b x (n + 1) :=
          lt_of_lt_of_le (by exact_mod_cast hu2.2) hn2.le
        have hcu : (drivenSigma b x n) ≤ (u : ℝ≥0∞) := by
          rw [hcσ]; exact_mod_cast hu2.1.le
        rw [drivenRegenFrom_piece hcu hu3, drivenRegenFrom_piece hn1 hn2, ← hc, hu]
      · exact le_trans (tsub_le_self (α := ℝ≥0)) hsT
      · exact add_tsub_cancel_of_le hcs
    · left
      exact heq.symm

theorem isRegPath_stepReg {β : ℝ} [Fact (0 < β)] {x : ℝ≥0 → Fin d → ℤ} (hx : IsRegPath x) :
    IsRegPath (stepReg β x) :=
  isRegPath_drivenRegenFrom toNNReal_pos' hx

end ElboimSly.Paper
