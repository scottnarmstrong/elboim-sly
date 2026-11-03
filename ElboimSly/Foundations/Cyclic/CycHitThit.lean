/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycClosing
public import ElboimSly.Frozen.Defs.CycTreg
public import ElboimSly.Foundations.Interchange.TrajApi
public import Mathlib

/-!
# ES22 Lemma 2.1: the hitting time `τ̂_hit(T)` of the non-regenerated walk and (c)

ES22 Lemma 2.1, statement and Step 3.

* `cycHatThit β W T`: `τ̂_hit(T) = inf {s > T : ∃ s' ∈ s + βℤ, 0 < s' < T, ‖W(s) - W(s')‖ ≤ 1}`
  (`τ̂_hit(0) = ∞`);
* `cycHatThit_le_treg`: `τ̂_hit(T) ≤ t_reg` if `0 < T ≤ t_reg`;
* `cycHatThit_eq_of_treg_le`: `τ̂_hit(T) = T` if `t_reg ≤ T`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- `τ̂_hit(T) := inf {s > T : ∃ s' ∈ s + βℤ, 0 < s' < T, ‖W(s) - W(s')‖ ≤ 1}` for a walk
`W : ℝ → ℤᵈ`, with `τ̂_hit(0) := ∞`. ES22 Lemma 2.1. -/
noncomputable def cycHatThit (β : ℝ) (W : ℝ → Fin d → ℤ) (T : ℝ) : ℝ≥0∞ :=
  open scoped Classical in
  if T = 0 then ⊤ else
    ⨅ s ∈ {s : ℝ | T < s ∧ ∃ s' : ℝ, (∃ k : ℤ, s' = s + k * β) ∧ 0 < s' ∧ s' < T ∧
      ‖W s - W s'‖ ≤ 1}, ENNReal.ofReal s

theorem cycHatThit_le {W : ℝ → Fin d → ℤ} {T s s' : ℝ} (hT : T ≠ 0) (hTs : T < s)
    (k : ℤ) (hk : s' = s + k * β) (hs0 : 0 < s') (hsT : s' < T) (hW : ‖W s - W s'‖ ≤ 1) :
    cycHatThit β W T ≤ ENNReal.ofReal s := by
  unfold cycHatThit
  rw [ite_eq_right hT]
  exact iInf₂_le s ⟨hTs, s', ⟨k, hk⟩, hs0, hsT, hW⟩

theorem le_cycHatThit {W : ℝ → Fin d → ℤ} {T : ℝ} (hT : T ≠ 0) :
    ENNReal.ofReal T ≤ cycHatThit β W T := by
  unfold cycHatThit
  rw [ite_eq_right hT]
  exact le_iInf₂ fun s hs => ENNReal.ofReal_le_ofReal hs.1.le

variable {ν : Measure (RingSpace d β)}

/-- `W = 0` near `0`. -/
theorem cycWalk_eq_zero_near (hν : Good ν) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ s : ℝ, 0 ≤ s → s < ε₀ → ElboimSly.cycWalk ν 0 0 s = 0 := by
  have hev := (fwdTrajFn_spec hν (0 : Fin d → ℤ) 0).1.1 0
  obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
  refine ⟨u', by exact_mod_cast hu', fun s hs hsu => ?_⟩
  rw [cycWalk_of_nonneg hν 0 0 hs]
  have hmem : (0 + s - 0).toNNReal ∈ Ico (0 : ℝ≥0) u' := by
    refine ⟨bot_le, ?_⟩
    rw [zero_add, sub_zero]
    exact (Real.toNNReal_lt_iff_lt_coe hs).2 hsu
  have := hsub hmem
  simp only [mem_ofPred_eq] at this
  unfold fwdTraj fwdReal
  rw [this]
  exact (fwdTrajFn_spec hν (0 : Fin d → ℤ) 0).2

/-- ES22 Lemma 2.1 (c), first part. -/
theorem cycHatThit_le_treg (hν : Good ν) {t : ℝ} (ht0 : 0 < t)
    (htr : ENNReal.ofReal t ≤ cycTreg ν) :
    cycHatThit β (fun s => ElboimSly.cycWalk ν 0 0 s) t ≤ cycTreg ν := by
  have hβ : 0 < β := Fact.out
  by_cases hfin : cycTreg ν < ⊤
  swap
  · rw [not_lt, top_le_iff] at hfin; rw [hfin]; exact le_top
  obtain ⟨n, hn, -, he⟩ := exists_cycTreg_eq hfin
  have hτ0 : 0 ≤ (n : ℝ) * β := by positivity
  have htτ : t ≤ (n : ℝ) * β := by
    rw [he] at htr
    exact (ENNReal.ofReal_le_ofReal_iff hτ0).1 htr
  obtain ⟨ε₀, hε₀, hW0⟩ := cycWalk_eq_zero_near hν
  have hadd := cycWalk_add_treg hν hfin
  rw [he, ENNReal.toReal_ofReal hτ0] at hadd
  rw [he]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set ε' : ℝ := min (min ε₀ t) (ε : ℝ) / 2 with hε'
  have hε'0 : 0 < ε' := by
    rw [hε']; have : 0 < min (min ε₀ t) (ε : ℝ) := lt_min (lt_min hε₀ ht0) (by exact_mod_cast hε)
    positivity
  have hε'1 : ε' < ε₀ := by
    have : min (min ε₀ t) (ε : ℝ) ≤ ε₀ := (min_le_left _ _).trans (min_le_left _ _)
    rw [hε']; linarith [lt_min (lt_min hε₀ ht0) (by exact_mod_cast hε : (0 : ℝ) < ε)]
  have hε'2 : ε' < t := by
    have : min (min ε₀ t) (ε : ℝ) ≤ t := (min_le_left _ _).trans (min_le_right _ _)
    rw [hε']; linarith [lt_min (lt_min hε₀ ht0) (by exact_mod_cast hε : (0 : ℝ) < ε)]
  have hε'3 : ε' ≤ (ε : ℝ) := by
    have : min (min ε₀ t) (ε : ℝ) ≤ (ε : ℝ) := min_le_right _ _
    rw [hε']; linarith [lt_min (lt_min hε₀ ht0) (by exact_mod_cast hε : (0 : ℝ) < ε)]
  have hmain : cycHatThit β (fun s => ElboimSly.cycWalk ν 0 0 s) t ≤
      ENNReal.ofReal ((n : ℝ) * β + ε') := by
    refine cycHatThit_le (s := (n : ℝ) * β + ε') (s' := ε') ht0.ne' (by linarith) (-(n : ℤ)) ?_
      hε'0 hε'2 ?_
    · push_cast; ring
    · have h1 := hadd ε'
      rw [show (n : ℝ) * β + ε' = ε' + (n : ℝ) * β by ring, h1, sub_self]
      simp
  refine hmain.trans ?_
  rw [ENNReal.ofReal_add hτ0 hε'0.le]
  gcongr
  exact (ENNReal.ofReal_le_ofReal hε'3).trans_eq (by simp)

/-- ES22 Lemma 2.1 (c), second part. -/
theorem cycHatThit_eq_of_treg_le (hν : Good ν) {t : ℝ}
    (htr : cycTreg ν ≤ ENNReal.ofReal t) :
    cycHatThit β (fun s => ElboimSly.cycWalk ν 0 0 s) t = ENNReal.ofReal t := by
  have hβ : 0 < β := Fact.out
  have hfin : cycTreg ν < ⊤ := htr.trans_lt ENNReal.ofReal_lt_top
  obtain ⟨n, hn, -, he⟩ := exists_cycTreg_eq hfin
  have hτ0 : 0 < (n : ℝ) * β := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have htτ : (n : ℝ) * β ≤ t := by
    rw [he] at htr
    by_contra hlt
    rw [not_le] at hlt
    by_cases ht : 0 ≤ t
    · have := (ENNReal.ofReal_le_ofReal_iff ht).1 htr
      linarith
    · rw [ENNReal.ofReal_of_nonpos (not_le.1 ht).le] at htr
      exact absurd (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hτ0) htr) (lt_irrefl _)
  have ht0 : t ≠ 0 := by linarith
  have hadd := cycWalk_add_treg hν hfin
  rw [he, ENNReal.toReal_ofReal hτ0.le] at hadd
  refine le_antisymm ?_ (le_cycHatThit ht0)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set ε' : ℝ := min ((n : ℝ) * β) (ε : ℝ) / 2 with hε'
  have hm : 0 < min ((n : ℝ) * β) (ε : ℝ) := lt_min hτ0 (by exact_mod_cast hε)
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have hε'1 : ε' < (n : ℝ) * β := by
    have : min ((n : ℝ) * β) (ε : ℝ) ≤ (n : ℝ) * β := min_le_left _ _
    rw [hε']; linarith
  have hε'3 : ε' ≤ (ε : ℝ) := by
    have : min ((n : ℝ) * β) (ε : ℝ) ≤ (ε : ℝ) := min_le_right _ _
    rw [hε']; linarith
  have hmain : cycHatThit β (fun s => ElboimSly.cycWalk ν 0 0 s) t ≤ ENNReal.ofReal (t + ε') := by
    refine cycHatThit_le (s := t + ε') (s' := t + ε' - (n : ℝ) * β) ht0 (by linarith) (-(n : ℤ))
      ?_ (by linarith) (by linarith) ?_
    · push_cast; ring
    · have h1 := hadd (t + ε' - (n : ℝ) * β)
      rw [show t + ε' - (n : ℝ) * β + (n : ℝ) * β = t + ε' by ring] at h1
      rw [h1]
      simp
  refine hmain.trans ?_
  rw [ENNReal.ofReal_add (by linarith) hε'0.le]
  gcongr
  exact (ENNReal.ofReal_le_ofReal hε'3).trans_eq (by simp)

end ElboimSly.Cyclic

end
