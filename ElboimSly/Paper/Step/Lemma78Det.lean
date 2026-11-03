/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Far
public import ElboimSly.Paper.Step.Lemma78Windows
public import ElboimSly.Paper.Step.Lemma78Omega
public import ElboimSly.Paper.Step.Lemma78Conn
public import ElboimSly.Paper.Step.Lemma78Occ
public import ElboimSly.Paper.Step.Lemma78Num3
public import ElboimSly.Paper.Heavy.Twelve
public import Mathlib

/-!
# Lemma 7.8: the pathwise part

Written proof: proof of ES22 Lemma 7.8 (ES22 §7), last paragraph. For a good environment
`N ω` on `Ω ∩ ℋ_1 ∩ {w₂ ∈ Γ_n} ∩ {τ'_bad > t'_n} ∩ {J ≤ n³}` (the last as `∃ J ≤ n³, ζ_J = t'_n`),
Short gaps (through ES22 Lemma 6.8 and the occupation bound) and covering fP_n
give `|𝔓_n| < 3.9^n`. The numerics are the hypotheses `hA` (`Step78Asym`) and `hnum1`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Heavy ElboimSly.Cyclic ElboimSly.Interchange

theorem tauHat_gt_of_gamma {d : ℕ} {β t₀ T : ℝ} {n : ℕ} {w : ℝ → Fin d → ℤ}
    (hΓ : heavyGamma d β t₀ n w) (hT1 : ENNReal.ofReal T < ENNReal.ofReal (indScale t₀ n))
    (hT2 : ENNReal.ofReal T < cycClosingTime β w) : ENNReal.ofReal T < heavyTauHat d β t₀ n w := by
  obtain ⟨-, hlt⟩ := hΓ
  unfold heavyTauHat heavyTauCheck
  refine lt_min hT1 (lt_min hT2 ?_)
  exact lt_trans (lt_min hT2 hT1) hlt

theorem indScaleReduced_lt {t₀ : ℝ} {n : ℕ} (ht1 : 1 < t₀) (hn : 2 ≤ n) :
    indScaleReduced t₀ n < indScale t₀ n := by
  unfold indScaleReduced
  have h0 : 0 < indScale t₀ n := by unfold indScale; have : 0 < t₀ := by linarith
                                    positivity
  have h2 : (1 : ℝ) < (n : ℝ) ^ 4 := one_lt_pow₀ (by exact_mod_cast (by omega : 1 < n)) (by norm_num)
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*}

/-- Written proof: end of the proof of ES22 Lemma 7.8, pathwise. -/
theorem step78_vol_lt {E : HeavyEscConsts} {n₀ n : ℕ} {t₀ q : ℝ} (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀)
    (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hβt : β < indScale t₀ n) (hT : HeavyT d n₀ E n)
    (hq0 : 0 ≤ q) (u : Fin d → ℤ) (N : Ω → Measure (RingSpace d β)) (ω : Ω) (hν : Good (N ω))
    (hnum1 : 3000 * (d : ℝ) ^ 2 * 2 ^ d ≤ 7 * n)
    (hA : Step78Asym d t₀ n β)
    (hΩ : cycOmega (N ω) 0 u 0 q (indScaleReduced t₀ n))
    (hH1 : Step78H1 d β t₀ n (indScaleReduced t₀ n) (fun s : ℝ => cycWalk (N ω) 0 0 s))
    (hΓ₂ : heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) u q s - u))
    (hτ : ENNReal.ofReal (indScaleReduced t₀ n) < step78TauBad d β t₀ n q (indScaleReduced t₀ n) u
      (fun s : ℝ => cycWalk (N ω) 0 0 s) (fun s : ℝ => cycWalk (N ω) u q s))
    (hJ : ∃ J : ℕ, 1 ≤ J ∧ J ≤ n ^ 3 ∧
      (step78DataOf d β n (indScaleReduced t₀ n) u q N).zeta J ω =
        ((indScaleReduced t₀ n).toNNReal : WithTop ℝ≥0)) :
    volume {s₂ : ℝ | s₂ ∈ Icc 0 (indScaleReduced t₀ n) ∧
        ∃ s₁ ∈ Icc 0 (indScaleReduced t₀ n),
          ‖cycWalk (N ω) 0 0 s₁ - cycWalk (N ω) u q s₂‖ ≤ (19 / 10 : ℝ) ^ n} <
      ENNReal.ofReal ((39 / 10 : ℝ) ^ n) := by
  have hβ : 0 < β := Fact.out
  have hn4 := hT.t4
  set T := indScaleReduced t₀ n with hTdef
  set tk := heavyTkPrime d t₀ n with htkdef
  set W₁ : ℝ → Fin d → ℤ := fun s => cycWalk (N ω) 0 0 s with hW₁
  set W₂ : ℝ → Fin d → ℤ := fun s => cycWalk (N ω) u q s with hW₂
  have htk0 : 0 ≤ tk := tkPrime_nonneg ht1
  have hT0 : 0 ≤ T := by
    rw [hTdef]; unfold indScaleReduced indScale
    have : 0 < t₀ := by linarith
    positivity
  have hkT : tk ≤ T := by linarith [hA.tk_le]
  obtain ⟨hnm, hc1, hc2⟩ := hΩ
  have hg2 := good_stepShiftEnv hν u (-q)
  have hw₂eq : (fun s : ℝ => W₂ s - u) = fun s : ℝ => cycWalk (stepShiftEnv u (-q) (N ω)) 0 0 s := by
    funext s; rw [cycWalk_stepShiftEnv_all hν u q]
  have hW₁c : IsCyclicPath W₁ := isCyclicPath_cycWalk hν
  have hw₂c : IsCyclicPath fun s => W₂ s - u := by rw [hw₂eq]; exact isCyclicPath_cycWalk hg2
  have hnr₂ : HasNoReturn β fun s => W₂ s - u := by rw [hw₂eq]; exact hasNoReturn_cycWalk hg2
  have hcl2 : ENNReal.ofReal T < cycClosingTime β fun s => W₂ s - u :=
    lt_cycClosingTime_of_omega₂ hν u q hc2
  have hTt : ENNReal.ofReal T < ENNReal.ofReal (indScale t₀ n) :=
    (ENNReal.ofReal_lt_ofReal_iff (by unfold indScale; have : 0 < t₀ := by linarith
                                      positivity)).2
      (indScaleReduced_lt ht1 (by omega))
  have hH₂ : ENNReal.ofReal T < heavyTauHat d β t₀ n fun s => W₂ s - u :=
    tauHat_gt_of_gamma hΓ₂ hTt hcl2
  set D := step78DataOf d β n T u q N with hD
  have hDT : (D.T : ℝ) = T := step78DataOf_T hT0
  have hnE_far : ∀ t ∈ Icc (2 * tk + 4) (D.T : ℝ), ¬ (W₂ t ∈ step78Exc d β t₀ n q T u W₁ W₂ t) →
      ∃ s ∈ Icc (t - tk) t, s ∈ D.farSet ω := by
    intro t ht hnE
    rw [hDT] at ht
    obtain ⟨s, hs, hsr, hsf⟩ := step78_far hd hn0 ht1 ht4 hβ hβt hT hq0
      (by positivity : (0 : ℝ) ≤ (1.9 : ℝ) ^ heavyLevel d n / 2) hW₁c hw₂c hnr₂ hH1.1 hH₂
      ht.1 ht.2 (by linarith [hA.tk_le]) hnE
      (fun a ha _ => not_segClosed_of_omega₁ hν hkT hc1)
      (fun b hb _ => not_segClosed_of_omega₂ hν u q hkT hc2)
      (fun a ha b hb hat hbt => not_crossMerge_of_omega u q ha.1 hb.1 hat hbt hnm)
      (far_N2 hT) (far_N3 hd hT) (far_num hd ht1 ht4 hT hnum1)
    exact ⟨s, hs, step78DataOf_mem_farSet hT0 hsr hsf⟩
  have hocc := step78_occ (β := β) (t₀ := t₀) (n := n) (q := q) (T := T) (u := u) (W₁ := W₁)
    (W₂ := W₂) hβ htk0 hw₂c hnr₂ hcl2.le hτ hT0
  have hg0 : 0 ≤ indScale t₀ n ^ (heavyEps d / 3) := by
    refine Real.rpow_nonneg ?_ _
    unfold indScale; have : 0 < t₀ := by linarith
    positivity
  have hL0 : 0 ≤ indScale t₀ n ^ heavyEps d := by
    refine Real.rpow_nonneg ?_ _
    unfold indScale; have : 0 < t₀ := by linarith
    positivity
  have hocc' : volume {t : ℝ | t ∈ Icc 0 (D.T : ℝ) ∧
      W₂ t ∈ step78Exc d β t₀ n q T u W₁ W₂ t} ≤ ENNReal.ofReal (indScale t₀ n ^ (heavyEps d / 3)) := by
    rw [hDT]
    by_cases hc : β < indScale t₀ n ^ (5 * indDelta d)
    · exact (hocc.1 hc).trans (ENNReal.ofReal_le_ofReal (hA.occ hc))
    · rw [hocc.2 hc]; exact zero_le
  have hlt := Step78Data.pn_small D ω (W1 := W₁)
    (bad := fun t => W₂ t ∈ step78Exc d β t₀ n q T u W₁ W₂ t) hg0
    (by linarith [hA.L2]) hA.L2 htk0 hL0 hocc' hnE_far
    (step78DataOf_V hT0 ω) hJ (by have h : D.n = n := step78DataOf_n; rw [h]; exact hA.pn)
  refine lt_of_le_of_lt (measure_mono ?_) hlt
  rintro s ⟨hs, s₁, hs₁, hn⟩
  rw [hDT]
  refine ⟨hs, s₁, hs₁, ?_⟩
  rw [step78DataOf_path hs.1]
  exact hn

end ElboimSly.Paper.Step

end
