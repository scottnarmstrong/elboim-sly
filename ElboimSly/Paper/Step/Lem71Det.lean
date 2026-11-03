/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.ZetaDetApply
public import ElboimSly.Paper.Step.ZetaSRW
public import Mathlib

/-!
# Lemma 7.1, pathwise

ES22 Lemma 7.1, Steps 2, 3, 5, 6.

`lem71_det`: off the bad events, `‖W(u) - W̃(u)‖ ≤ 2 (n³ + 1) n³ (h + 1)` for all `u ≤ T`.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

theorem lem71_det {β : ℝ} [Fact (0 < β)] (hd1 : 1 ≤ d) (hβ1 : 1 < β)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}
    {F : ℝ≥0 → MeasurableSpace Ω} (hF : IsAdmissible P Y F) (hYp : ∀ ω, Y ω ∈ StepPath d)
    (a s₀ Tn : ℝ≥0) (n : ℕ) (hn : 1 ≤ n) {hh : ℝ} (hhpos : 0 < hh) (hs0 : s₀ ≤ Tn) (ω : Ω)
    (hCF1 : stepShift a (Y ω) ∈ StepCF (d := d) β)
    (hCF2 : stepShift (a + s₀) (Y ω) ∈ StepCF (d := d) β)
    (hB1 : (Tn : WithTop ℝ≥0) <
      zetaN β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ (n ^ 3) ω)
    (hW1 : WinOK (Tn : ℝ) hh n (stepRelaxedSet β (stepWr β a Y ω) (stepAr β a Y ω)))
    (hW2 : WinOK (Tn : ℝ) hh n
      (stepRelaxedSet β (stepWr β (a + s₀) Y ω) (stepAr β (a + s₀) Y ω)))
    (hF1 : ENNReal.ofReal (Tn : ℝ) < pathTfast (stepWr β a Y ω) ((n : ℝ) ^ 3))
    (hF2 : ENNReal.ofReal (Tn : ℝ) < pathTfast (stepWr β (a + s₀) Y ω) ((n : ℝ) ^ 3)) :
    ∀ u : ℝ≥0, u ≤ Tn →
      ‖stepReg β (stepShift a (Y ω)) u - stepCat s₀ (stepReg β (stepShift a (Y ω)))
        (stepReg β (stepShift (a + s₀) (Y ω))) u‖ ≤
        2 * (((n ^ 3 : ℕ) : ℝ) + 1) * ((n : ℝ) ^ 3 * (hh + 1)) := by
  have hz1 := zetaProc_one (β := β) hF hYp a
  have hz2 := zetaProc_two (β := β) hF hYp a s₀
  have hxy : shiftPath (stepShift a (Y ω)) s₀ = stepShift (a + s₀) (Y ω) :=
    shiftPath_add (Y ω) a s₀
  have hL : (0 : ℝ) < (n : ℝ) ^ 3 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hW0 : stepReg β (stepShift (a + s₀) (Y ω)) 0 = 0 := stepReg_zero' (stepShift_mem (hYp ω) _)
  -- the truncated sequences
  set zn : ℕ → ℝ≥0 := fun i => trT Tn
    (zetaN β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ i ω) with hzn
  set zp : ℕ → ℝ≥0 := fun i => trT Tn
    (zetaP β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ i ω) with hzp
  have hW := (fast_disp (W := stepReg β (stepShift a (Y ω))) (L := (n : ℝ) ^ 3) hL hF1)
  have hV := (fast_disp (W := stepReg β (stepShift (a + s₀) (Y ω))) (L := (n : ℝ) ^ 3) hL hF2)
  have := det_decomp (W := stepReg β (stepShift a (Y ω)))
    (V₂ := stepReg β (stepShift (a + s₀) (Y ω))) hW0 (s₀ := s₀) (T := Tn) (h := hh)
    (L := (n : ℝ) ^ 3) (n ^ 3) zn zp ?_ ?_ ?_ ?_ ?_ ?_ ?_ hW hV hL.le hhpos.le
  · exact this
  · -- zp 0 = s₀
    show trT Tn (s₀ : WithTop ℝ≥0) = s₀
    exact trT_eq_of_le rfl hs0
  · intro i _
    exact trT_mono Tn (zetaP_le_zetaN s₀ i ω)
  · intro i _
    exact trT_mono Tn (zetaN_le_zetaP_succ hd1 hβ1 hz1 hz2 s₀ i ω)
  · show Tn ≤ trT Tn _
    rw [trT_eq_of_lt hB1]
  · intro i _
    exact trT_le _ _
  · intro i _
    refine zeta_gap_trunc hd1 hβ1 hz1 hz2 s₀ i ω hhpos hn hW1
      (window_shift a s₀ ω (hYp ω) hW2)
  · intro i hi r hr
    by_cases hbig : (Tn : WithTop ℝ≥0) <
        zetaN β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ i ω
    · have e : zn i = Tn := trT_eq_of_lt hbig
      have hle : zn i + r ≤ Tn := hr.trans (trT_le _ _)
      have hr0 : r = 0 := by
        rw [e] at hle
        exact le_antisymm ((add_le_iff_nonpos_right Tn).1 hle) zero_le
      subst hr0
      simp only [add_zero, sub_self]
    · rw [not_lt] at hbig
      have hne : zetaN β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ i ω ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top hbig
      obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.1 hne
      have hzTn : z ≤ Tn := WithTop.coe_le_coe.1 (hz ▸ hbig)
      have hzn' : zn i = z := trT_eq_of_le hz.symm hzTn
      have hzs : stopReal (zetaN β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ i) ω
          = z := by unfold stopReal; rw [← hz]; rfl
      have hs0z : s₀ ≤ z := by
        have h1 := le_zetaP hd1 hβ1 hz1 hz2 s₀ i ω
        have h2 := zetaP_le_zetaN (β := β) (w₁ := zw1 β a Y) (α₁ := za1 β a Y)
          (w₂ := zw2 β a s₀ Y) (α₂ := za2 β a s₀ Y) s₀ i ω
        have := h1.trans h2
        rw [← hz] at this
        exact WithTop.coe_le_coe.1 this
      have hmin : ((z + r : ℝ≥0) : WithTop ℝ≥0) ≤
          zetaP β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ (i + 1) ω := by
        have h3 : z + r ≤ trT Tn (zetaP β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y)
            (za2 β a s₀ Y) s₀ (i + 1) ω) := by
          have := hr
          rw [hzn'] at this
          exact this
        exact (WithTop.coe_le_coe.2 h3).trans (trT_le_self Tn _)
      have hmin' : ((z + r : ℝ≥0) : WithTop ℝ≥0) ≤ min
          (stepThitStop β (zw1 β a Y) (za1 β a Y) (zetaN β (zw1 β a Y) (za1 β a Y)
            (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ i) ω : WithTop ℝ≥0)
          (stepThitStop β (zw2 β a s₀ Y) (za2 β a s₀ Y) (zetaN β (zw1 β a Y) (za1 β a Y)
            (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ i) ω : WithTop ℝ≥0) := hmin
      obtain ⟨hm1, hm2⟩ := le_min_iff.1 hmin'
      rw [stepThitStop_of_ne hne, hzs] at hm1 hm2
      have key := incr_agree (β := β) (x := stepShift a (Y ω)) hCF1 (s₀ := s₀)
        (by rw [hxy]; exact hCF2) (t := z) hs0z (r := r) hm1 (by rw [hxy]; exact hm2)
      rw [hxy] at key
      rw [hzn']
      exact key

end ElboimSly.Paper.Step
