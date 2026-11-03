/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFarJumps
public import ElboimSly.Foundations.Cyclic.CycRegenLawMeas2
public import Mathlib

/-!
# ES22 Lemma 2.2, Steps 1-3 (driven regenerated walk)

ES22 Lemma 2.2. For a coincidence-free driving path `x`, the regenerated driven walk
satisfies, for every `s`, `‖W^x_reg(s)‖₁ ≤ 2 · #jumps(x, (0, s])`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {b : ℝ≥0} {x : ℝ≥0 → Fin d → ℤ}

theorem card_jumps_shiftPath_le (f : ℝ≥0 → Fin d → ℤ) (a r : ℝ≥0) (hfin : (CDisc f ∩ Iic (a + r)).Finite) :
    (CDisc (shiftPath f a) ∩ Iic r).ncard ≤ (CDisc f ∩ Iic (a + r)).ncard := by
  refine Set.ncard_le_ncard_of_injOn (fun u => a + u) (fun u hu => ?_)
    (fun u _ v _ h => add_left_cancel h) hfin
  exact ⟨mem_CDisc_of_shiftPath a hu.1, mem_Iic.2 (add_le_add le_rfl hu.2)⟩

/-- **ES22 Lemma 2.2, Steps 1-3 (driven)**: `‖W^x_reg(s)‖₁ ≤ 2 · #jumps(x, (0, s])`. -/
theorem l1n_drivenRegenFrom_le (hb : 0 < b) (hx : x ∈ CycCF b) (s : ℝ≥0) :
    l1n (drivenRegenFrom b x s) ≤ 2 * (CDisc x ∩ Iic s).ncard := by
  obtain ⟨hs1, hs2⟩ := gluedCount_spec' hb x s
  set N := gluedCount (drivenSigma b x) s with hN
  have hσlt : drivenSigma b x N < ⊤ := lt_of_le_of_lt hs1 ENNReal.coe_lt_top
  set σ := (drivenSigma b x N).toNNReal with hσ
  have hσcoe : drivenSigma b x N = (σ : ℝ≥0∞) := (ENNReal.coe_toNNReal hσlt.ne).symm
  have hσs : σ ≤ s := by rw [hσcoe] at hs1; exact_mod_cast hs1
  have hpieces : drivenPieces b x N = shiftPath x σ :=
    (cutTimes_eq_drivenSigma hx.1.zero N).2 hσlt
  have hy : drivenPieces b x N ∈ CycCF b := drivenPieces_mem_cycCF hx N hσlt
  set r := s - σ with hr
  have hsr : σ + r = s := add_tsub_cancel_of_le hσs
  have hrtreg : (r : ℝ≥0∞) ≤ drivenTreg b (drivenPieces b x N) := by
    rw [drivenSigma_succ, hσcoe] at hs2
    have : (s : ℝ≥0∞) < σ + drivenTreg b (drivenPieces b x N) := hs2
    have h2 : ((σ + r : ℝ≥0) : ℝ≥0∞) < σ + drivenTreg b (drivenPieces b x N) := by
      rw [hsr]; exact this
    push_cast at h2
    exact ((ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top).1 h2).le
  have heq : drivenRegenFrom b x s = drivenWalk b (drivenPieces b x N) r := rfl
  rw [heq]
  obtain ⟨hdr, hi, -⟩ := hy
  have hw := drivenWalk_wd_a hdr hb
  have hwreg : IsRegPath (drivenWalk b (drivenPieces b x N)) := drivenWalk_isRegPath hdr.toIsRegPath hb
  have h1 := l1n_le_card_jumps hwreg (drivenWalk_zero hdr.toIsRegPath hb) hw.2.2.2.2.1 _ r rfl
  have h2 := card_jumps_driven_le hdr hb hi hrtreg
  have h3 := card_jumps_shiftPath_le x σ r (by rw [hsr]; exact hx.1.fin s)
  rw [hsr, ← hpieces] at h3
  omega

end ElboimSly.Cyclic

end
