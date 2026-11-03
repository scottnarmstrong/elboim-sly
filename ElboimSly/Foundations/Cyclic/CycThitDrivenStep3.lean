/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycThitDrivenStep2
public import Mathlib

/-!
# ES22 Lemma 2.1: Step 3 ($W'$ does not close first)

ES22 Lemma 2.1, Step 3. If `treg^{x'} = T0` were finite with
`t + T0 ≤ t_hit(t)`, then the pair `(t + T0 - ε, t - ε)` would be a hit before `t_hit(t)`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {b : ℝ≥0} {x : ℝ≥0 → Fin d → ℤ}

theorem mem_Ioo_sub {l r ε : ℝ≥0} (hl : l < r) (h0 : 0 < ε) (hε : ε < r - l) :
    r - ε ∈ Ioo l r := by
  have h1 : ε + l < r := by rw [← lt_tsub_iff_right]; exact hε
  exact ⟨lt_tsub_iff_left.2 h1, tsub_lt_self (lt_of_le_of_lt zero_le hl) h0⟩

theorem exists_left_Ioo {f : ℝ≥0 → Fin d → ℤ} (hf : IsRegPath f) {r : ℝ≥0} (hr : 0 < r) :
    ∃ l, l < r ∧ ∀ v ∈ Ioo l r, f v = leftVal f r :=
  (mem_nhdsLT_iff_exists_Ioo_subset' hr).1 (hf.eventually_leftVal hr)

/-- **Step 3**: the walk driven by `x(t + ·) - x(t)` does not close at or before `t_hit(t)`. -/
theorem step3 (hb : 0 < b) (hx : x ∈ CycCF b) {t : ℝ≥0} (ht0 : 0 < t)
    (htτ : (t : ℝ≥0∞) < drivenTreg b x) {T0 : ℝ≥0}
    (hT0 : drivenTreg b (shiftPath x t) = T0)
    (hle : ((t + T0 : ℝ≥0) : ℝ≥0∞) ≤ drivenThit b x t) : False := by
  have hxr : IsRegPath x := hx.1.toIsRegPath
  have hW := drivenWalk_isRegPath hxr hb
  have hx'd : IsDrivingPath (shiftPath x t) := isDrivingPath_shiftPath hx.1 t
  have hW' := drivenWalk_isRegPath hx'd.toIsRegPath hb
  rcases pathTreg_top_or b (drivenWalk b (shiftPath x t)) with h | ⟨j, hj1, hj, hz⟩
  · have h' : drivenTreg b (shiftPath x t) = ⊤ := h
    rw [h'] at hT0
    exact absurd hT0 (by simp)
  have hTj : T0 = j * b := by
    have : (T0 : ℝ≥0∞) = ((j * b : ℝ≥0) : ℝ≥0∞) := by rw [← hT0]; exact hj
    exact_mod_cast this
  have hT0pos : 0 < T0 := by
    rw [hTj]; exact mul_pos (by exact_mod_cast hj1) hb
  have st2 := step2 hb hx ht0 htτ hle
  have hτ : ((t + T0 : ℝ≥0) : ℝ≥0∞) ≤ drivenTreg b x :=
    hle.trans (drivenThit_le_treg hb hx ht0 htτ)
  have hWu : drivenWalk b x (t + T0) = drivenWalk b x t := by
    have := st2 T0 le_rfl
    rw [hTj] at this ⊢
    have h0 : drivenWalk b (shiftPath x t) (j * b) = 0 := hz
    rw [h0] at this
    exact sub_eq_zero.1 this
  have hu0 : 0 < t + T0 := lt_of_le_of_lt zero_le (lt_add_of_pos_right t hT0pos)
  obtain ⟨l1, hl1, hsub1⟩ := exists_left_Ioo hW' hT0pos
  obtain ⟨l2, hl2, hsub2⟩ := exists_left_Ioo hW ht0
  obtain ⟨l3, hl3, hsub3⟩ := exists_left_Ioo hW hu0
  have hM : 0 < min (min (T0 - l1) (t - l2)) (t + T0 - l3) :=
    lt_min (lt_min (tsub_pos_of_lt hl1) (tsub_pos_of_lt hl2)) (tsub_pos_of_lt hl3)
  set M := min (min (T0 - l1) (t - l2)) (t + T0 - l3) with hMdef
  set ε : ℝ≥0 := M / 2 with hεdef
  have hε0 : 0 < ε := half_pos hM
  have hεM : ε < M := half_lt_self hM
  have hε1 : ε < T0 - l1 := hεM.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε2 : ε < t - l2 := hεM.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hε3 : ε < t + T0 - l3 := hεM.trans_le (min_le_right _ _)
  have hεT : ε ≤ T0 := (hε1.trans_le tsub_le_self).le
  have hεt : ε ≤ t := (hε2.trans_le tsub_le_self).le
  have hv := mem_Ioo_sub hl1 hε0 hε1
  have hv' := mem_Ioo_sub hl2 hε0 hε2
  have hsu := mem_Ioo_sub hl3 hε0 hε3
  have hsEq : t + T0 - ε = t + (T0 - ε) := add_tsub_assoc_of_le hεT t
  rw [hsEq] at hsu
  -- values
  have hWs : drivenWalk b x (t + (T0 - ε)) = drivenWalk b x t + leftVal (drivenWalk b (shiftPath x t)) T0 := by
    have := st2 (T0 - ε) tsub_le_self
    rw [hsub1 _ hv] at this
    rw [← this]; abel
  have hWs3 : drivenWalk b x (t + (T0 - ε)) = leftVal (drivenWalk b x) (t + T0) := hsub3 _ hsu
  have hWs' : drivenWalk b x (t - ε) = leftVal (drivenWalk b x) t := hsub2 _ hv'
  have hvpos : 0 < T0 - ε := lt_of_le_of_lt zero_le hv.1
  refine miss hb hx ht0 htτ (k := -(j : ℤ)) (s := t + (T0 - ε)) (s' := t - ε)
    (lt_add_of_pos_right t hvpos) ?_ ?_ (lt_of_le_of_lt zero_le hv'.1) hv'.2 ?_
  · refine lt_of_lt_of_le ?_ hle
    have : t + (T0 - ε) < t + T0 := by
      have : T0 - ε < T0 := hv.2
      exact add_lt_add_of_le_of_lt le_rfl this
    exact_mod_cast this
  · have hc1 : ((t - ε : ℝ≥0) : ℝ) = t - ε := NNReal.coe_sub hεt
    have hc2 : ((T0 - ε : ℝ≥0) : ℝ) = T0 - ε := NNReal.coe_sub hεT
    have hc3 : (T0 : ℝ) = j * b := by exact_mod_cast hTj
    push_cast
    rw [hc1, hc2, hc3]; ring
  · rw [hWs, hWs']
    by_cases hjump' : T0 ∈ CDisc (drivenWalk b (shiftPath x t))
    · have hunit := drivenWalk_unit hx'd hb T0 hjump'
      have hz0 : drivenWalk b (shiftPath x t) T0 = 0 := by rw [hTj]; exact hz
      rw [hz0] at hunit
      have hnorm : ‖leftVal (drivenWalk b (shiftPath x t)) T0‖ ≤ 1 := by
        have := norm_le_one_of_unit hunit
        rwa [zero_sub, norm_neg] at this
      by_cases hjt : t ∈ CDisc (drivenWalk b x)
      · -- the two jumps of W at t and t + T0 cross one edge
        have hcong : ∀ w ≤ T0, drivenWalk b (shiftPath x t) w = shiftPath (drivenWalk b x) t w :=
          fun w hw => by rw [shiftPath_apply, st2 w hw]
        have hjS : T0 ∈ CDisc (shiftPath (drivenWalk b x) t) := (mem_CDisc_congr hcong).1 hjump'
        have hju : t + T0 ∈ CDisc (drivenWalk b x) := (mem_CDisc_shiftPath hW hT0pos).1 hjS
        have hedge := (drivenSol hxr hb).edge_eq hx.2.1 hjt (k := j) (by rw [← hTj]; exact hju)
          (by rw [← hTj]; exact hτ)
        rw [← hTj] at hedge
        have hmem : leftVal (drivenWalk b x) (t + T0) ∈
            ({leftVal (drivenWalk b x) t, drivenWalk b x t} : Set (Fin d → ℤ)) := by
          rw [← hedge]; exact Or.inl rfl
        have hne : leftVal (drivenWalk b x) (t + T0) ≠ drivenWalk b x (t + T0) :=
          (hW.mem_CDisc_iff.1 hju).2
        have heqc : leftVal (drivenWalk b x) (t + T0) = leftVal (drivenWalk b x) t := by
          rcases hmem with h | h
          · exact h
          · exact absurd (h.trans hWu.symm) hne
        have hfin : drivenWalk b x t + leftVal (drivenWalk b (shiftPath x t)) T0 =
            leftVal (drivenWalk b x) t := by rw [← hWs, hWs3, heqc]
        rw [hfin]; simp
      · have hc := hW.leftVal_eq_of_not_mem ht0 hjt
        rw [hc]
        simpa using hnorm
    · have ha := hW'.leftVal_eq_of_not_mem hT0pos hjump'
      have hz0 : drivenWalk b (shiftPath x t) T0 = 0 := by rw [hTj]; exact hz
      rw [ha, hz0, add_zero]
      by_cases hjt : t ∈ CDisc (drivenWalk b x)
      · have hunit := drivenWalk_unit hx.1 hb t hjt
        exact norm_le_one_of_unit hunit
      · rw [hW.leftVal_eq_of_not_mem ht0 hjt]; simp

end ElboimSly.Cyclic

end
