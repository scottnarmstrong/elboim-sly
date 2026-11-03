/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenPiece
public import ElboimSly.Foundations.Cyclic.CycThit
public import ElboimSly.Foundations.Cyclic.CycHitThit
public import Mathlib

/-!
# ES22 Lemma 2.1 (d): the hitting time of the regenerated walk

ES22 Lemma 2.1 (d). For `t > α(t)`, `t_hit(t) ≤ Λ_k`, the end of the current
piece (`cycThit_le_sigma`); for `t = α(t)` the defining set is empty (`cycThit_eq_top`). Up to
the end of the current piece the regenerated hitting condition is the one of the cyclic walk of
the current piece (`le_cycHatThit_of_le_cycThit`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : ℕ → Measure (RingSpace d β)}

omit [Fact (0 < β)] in
/-- If `T = α(T)` then `t_hit(T) = ∞`. -/
theorem cycThit_eq_top {t : ℝ} (h : ElboimSly.regenStart ν t = t) : ElboimSly.cycThit ν t = ⊤ := by
  unfold ElboimSly.cycThit
  refine iInf₂_eq_top.2 fun s hs => ?_
  obtain ⟨-, s', -, h1, h2, -⟩ := hs
  rw [h] at h1
  exact absurd (h1.trans h2) (lt_irrefl _)

/-- **ES22 Lemma 2.1 (d)**: `t_hit(t) ≤ Λ_k` if `t > α(t)`. -/
theorem cycThit_le_sigma (hg : ∀ j, Good (ν j)) {t : ℝ} (ht : 0 ≤ t)
    (hL : 0 < t - ElboimSly.regenStart ν t) :
    ElboimSly.cycThit ν t ≤ ElboimSly.regenSigma ν (ElboimSly.regenCount ν t + 1) := by
  have hβ : 0 < β := Fact.out
  set k := ElboimSly.regenCount ν t with hk
  have hkfin : ElboimSly.regenSigma ν k < ⊤ := regenSigma_count_lt_top ν ht
  set a := ElboimSly.regenStart ν t with ha
  have ha' : a = (ElboimSly.regenSigma ν k).toReal := rfl
  have ha0 : 0 ≤ a := regenStart_nonneg ν t
  have hσ : ENNReal.ofReal a = ElboimSly.regenSigma ν k := ENNReal.ofReal_toReal hkfin.ne
  by_cases hfin : ElboimSly.cycTreg (ν k) < ⊤
  swap
  · rw [not_lt, top_le_iff] at hfin
    rw [regenSigma_succ, hfin, add_top]
    exact le_top
  obtain ⟨n, hn, -, he⟩ := exists_cycTreg_eq hfin
  have hnβ : 0 < (n : ℝ) * β := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hLn : t - a < (n : ℝ) * β := by
    have := ofReal_sub_regenStart_lt ν ht
    rw [← hk, he] at this
    exact (ENNReal.ofReal_lt_ofReal_iff hnβ).1 this
  have hs1 : ElboimSly.regenSigma ν (k + 1) = ENNReal.ofReal (a + (n : ℝ) * β) := by
    rw [regenSigma_succ, ← hσ, he, ENNReal.ofReal_add ha0 hnβ.le]
  have hs1fin : ElboimSly.regenSigma ν (k + 1) < ⊤ := hs1 ▸ ENNReal.ofReal_lt_top
  have hs1r : (ElboimSly.regenSigma ν (k + 1)).toReal = a + (n : ℝ) * β := by
    rw [hs1, ENNReal.toReal_ofReal (by positivity)]
  obtain ⟨ε₀, hε₀, hW0⟩ := cycWalk_eq_zero_near (hg k)
  obtain ⟨ε₁, hε₁, hW1⟩ := cycWalk_eq_zero_near (hg (k + 1))
  rw [hs1]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set m : ℝ := min (min (min ε₀ ε₁) (t - a)) (min β (ε : ℝ)) with hm
  have hm0 : 0 < m := lt_min (lt_min (lt_min hε₀ hε₁) hL) (lt_min hβ (by exact_mod_cast hε))
  set e : ℝ := m / 2 with he'
  have he0 : 0 < e := by positivity
  have hem : e < m := by rw [he']; linarith
  have hm1 : m ≤ ε₀ := ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hm2 : m ≤ ε₁ := ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hm3 : m ≤ t - a := (min_le_left _ _).trans (min_le_right _ _)
  have hm4 : m ≤ β := (min_le_right _ _).trans (min_le_left _ _)
  have hm5 : m ≤ (ε : ℝ) := (min_le_right _ _).trans (min_le_right _ _)
  have hW' : ElboimSly.regenWalk ν (a + e) = 0 := by
    have h := regenWalk_piece hg k hkfin he0.le (u := e)
      (by rw [he]; exact ENNReal.ofReal_le_ofReal (by linarith))
    rw [← ha'] at h
    rw [h]
    exact hW0 e he0.le (by linarith)
  have hW : ElboimSly.regenWalk ν (a + (n : ℝ) * β + e) = 0 := by
    have := regenWalk_piece hg (k + 1) hs1fin he0.le (u := e) (by
      refine (ENNReal.ofReal_le_ofReal (by linarith : e ≤ β)).trans ?_
      exact regPlan_tau_ge (ν (k + 1)))
    rw [hs1r] at this
    rw [this]
    exact hW1 e he0.le (by linarith)
  have hmain : ElboimSly.cycThit ν t ≤ ENNReal.ofReal (a + (n : ℝ) * β + e) := by
    unfold ElboimSly.cycThit
    refine iInf₂_le (a + (n : ℝ) * β + e) ⟨by linarith, a + e, ⟨-(n : ℤ), by push_cast; ring⟩,
      by linarith, by linarith, ?_⟩
    rw [hW, hW']
    simp
  refine hmain.trans ?_
  rw [ENNReal.ofReal_add (by positivity) he0.le]
  gcongr
  exact (ENNReal.ofReal_le_ofReal (by linarith : e ≤ (ε : ℝ))).trans_eq (by simp)

/-- Before the hitting time, `t + s` is still inside the current piece: `(t - α) + s ≤ t_reg^{(k+1)}`. -/
theorem ofReal_add_le_treg (hg : ∀ j, Good (ν j)) {t : ℝ} (ht : 0 ≤ t)
    (hL : 0 < t - ElboimSly.regenStart ν t) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ENNReal.ofReal (t + s) ≤ ElboimSly.cycThit ν t) :
    ENNReal.ofReal ((t - ElboimSly.regenStart ν t) + s) ≤
      ElboimSly.cycTreg (ν (ElboimSly.regenCount ν t)) := by
  set k := ElboimSly.regenCount ν t with hk
  have hkfin : ElboimSly.regenSigma ν k < ⊤ := regenSigma_count_lt_top ν ht
  set a := ElboimSly.regenStart ν t with ha
  have ha0 : 0 ≤ a := regenStart_nonneg ν t
  have hσ : ENNReal.ofReal a = ElboimSly.regenSigma ν k := ENNReal.ofReal_toReal hkfin.ne
  set L := t - a with hLdef
  have h1 := hs.trans (cycThit_le_sigma hg ht hL)
  rw [← hk, regenSigma_succ] at h1
  have h2 : ENNReal.ofReal (t + s) = ElboimSly.regenSigma ν k + ENNReal.ofReal (L + s) := by
    rw [← hσ, ← ENNReal.ofReal_add ha0 (by linarith)]
    congr 1; rw [hLdef]; ring
  rw [h2] at h1
  exact (ENNReal.add_le_add_iff_left hkfin.ne).1 h1

/-- Up to the end of the current piece, the hitting condition of the regenerated walk is the one of
the cyclic walk of the current piece: `t + s ≤ t_hit(t)` implies `(t - α) + s ≤ τ̂_hit(t - α)`. -/
theorem le_cycHatThit_of_le_cycThit (hg : ∀ j, Good (ν j)) {t : ℝ} (ht : 0 ≤ t)
    (hL : 0 < t - ElboimSly.regenStart ν t) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : ENNReal.ofReal (t + s) ≤ ElboimSly.cycThit ν t) :
    ENNReal.ofReal ((t - ElboimSly.regenStart ν t) + s) ≤
      cycHatThit β (fun r => ElboimSly.cycWalk (ν (ElboimSly.regenCount ν t)) 0 0 r)
        (t - ElboimSly.regenStart ν t) := by
  set k := ElboimSly.regenCount ν t with hk
  have hkfin : ElboimSly.regenSigma ν k < ⊤ := regenSigma_count_lt_top ν ht
  set a := ElboimSly.regenStart ν t with ha
  have ha' : a = (ElboimSly.regenSigma ν k).toReal := rfl
  have ha0 : 0 ≤ a := regenStart_nonneg ν t
  have hσ : ENNReal.ofReal a = ElboimSly.regenSigma ν k := ENNReal.ofReal_toReal hkfin.ne
  set L := t - a with hLdef
  have htL : t = a + L := by rw [hLdef]; ring
  have hLs : ENNReal.ofReal (L + s) ≤ ElboimSly.cycTreg (ν k) :=
    ofReal_add_le_treg hg ht hL hs0 hs
  have hLℓ : ENNReal.ofReal L ≤ ElboimSly.cycTreg (ν k) :=
    (ofReal_sub_regenStart_lt ν ht).le
  unfold cycHatThit
  rw [ite_eq_right hL.ne']
  refine le_iInf₂ fun u hu => ?_
  obtain ⟨hLu, s'', ⟨kk, hkk⟩, hs0'', hsL, hW⟩ := hu
  by_contra hlt
  rw [not_le, ENNReal.ofReal_lt_ofReal_iff (by linarith)] at hlt
  have hu0 : 0 ≤ u := by linarith
  have huℓ : ENNReal.ofReal u ≤ ElboimSly.cycTreg (ν k) :=
    (ENNReal.ofReal_le_ofReal hlt.le).trans hLs
  have hs''ℓ : ENNReal.ofReal s'' ≤ ElboimSly.cycTreg (ν k) :=
    (ENNReal.ofReal_le_ofReal hsL.le).trans hLℓ
  have e1 : ElboimSly.regenWalk ν (a + u) = ElboimSly.cycWalk (ν k) 0 0 u := by
    have := regenWalk_piece hg k hkfin hu0 huℓ
    rwa [← ha'] at this
  have e2 : ElboimSly.regenWalk ν (a + s'') = ElboimSly.cycWalk (ν k) 0 0 s'' := by
    have := regenWalk_piece hg k hkfin hs0''.le hs''ℓ
    rwa [← ha'] at this
  have hth : ElboimSly.cycThit ν t ≤ ENNReal.ofReal (a + u) := by
    unfold ElboimSly.cycThit
    refine iInf₂_le (a + u) ⟨by linarith, a + s'', ⟨kk, by linarith⟩, by linarith, by linarith, ?_⟩
    rw [e1, e2]; exact hW
  have hlt2 : ENNReal.ofReal (a + u) < ENNReal.ofReal (t + s) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  exact absurd (hth.trans_lt hlt2) (not_lt.2 hs)

end ElboimSly.Cyclic

end
