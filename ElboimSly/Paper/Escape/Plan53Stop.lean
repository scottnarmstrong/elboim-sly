/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan5
public import ElboimSly.Paper.Escape.Plan5Stop
public import Mathlib

/-!
# `τ_i = 4^n` if none of the conditions (1)-(7) holds before `4^n`

ES22 Lemma 5.3 ("on `𝒥`, `τ_i = 4^n`").  `Plan5Stop` shows that a condition at `t` forces
the stopping length to be `≤ t`.  Here the converse: if no condition holds (for the walk cut at
`t`) at any `t < 4^n`, then the stopping length is `≥ 4^n`; together with condition (7) at `4^n`
this gives `= 4^n` (`stopLen_eq_of_no_cond`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
theorem le_stopLen_of_no_cond {P : CycPlan ℕ (k + 2) β} {D : EscRP k} {m ℓ : ℕ}
    (hR : RuleAt P D m ℓ) (hlog : 1 < Real.log D.β) (ρ : CycRecN ℕ (k + 2) m)
    (p : CycPath (k + 2))
    (hno : ∀ t : ℝ≥0, (t : ℝ) < 4 ^ D.n →
      ¬ D.Cany ℓ (CycRec.snoc ρ (P.start m ρ, p.cut (t : ℝ≥0∞)))) :
    (4 : ℝ≥0∞) ^ D.n ≤ P.stopLen m ρ p := by
  classical
  set δ := P.start m ρ with hδ
  have h4 : ∀ ς : ℝ≥0, D.Cany ℓ (CycRec.snoc ρ (δ, p.cut (ς : ℝ≥0∞))) →
      (4 : ℝ≥0∞) ^ D.n ≤ ς := by
    intro ς hc
    by_contra h
    rw [not_le] at h
    have h' : (ς : ℝ≥0∞) < (((4 : ℝ≥0) ^ D.n : ℝ≥0) : ℝ≥0∞) := by simpa using h
    have h'' : (ς : ℝ) < 4 ^ D.n := by exact_mod_cast ENNReal.coe_lt_coe.1 h'
    exact hno ς h'' hc
  unfold CycPlan.stopLen
  refine le_sInf ?_
  rintro e (⟨a, ha1, hja, hst, rfl⟩ | ⟨a, hja, rfl, hlt⟩)
  all_goals
    set ς : ℝ≥0 := (p.1.jt a).toNNReal with hς
    have hςeq : (ς : ℝ≥0∞) = p.1.jt a := ENNReal.coe_toNNReal hja.ne
    have hhat : P.hatRec m ρ p a = CycRec.snoc ρ (δ, p.cut (ς : ℝ≥0∞)) := by
      unfold CycPlan.hatRec; rw [hςeq]
  · rw [hR.st, hhat] at hst
    unfold EscRP.escSt at hst
    have hC : D.Cany ℓ (CycRec.snoc ρ (δ, p.cut (ς : ℝ≥0∞))) := by simpa using hst
    rw [← hςeq]; exact h4 ς hC
  · rw [hR.dl, hhat]
    rw [hR.dl, hhat] at hlt
    unfold EscRP.escDl
    unfold EscRP.escDl at hlt
    by_cases hA : D.Cany ℓ (CycRec.snoc ρ (δ, p.cut (ς : ℝ≥0∞)))
    · rw [ite_eq_left hA, add_zero, ← hςeq]; exact h4 ς hA
    · rw [ite_eq_right hA]
      rw [ite_eq_right hA] at hlt
      simp only [snoc_last']
      simp only [snoc_last'] at hlt
      have hlen : CycEntry.len ((δ, p.cut (ς : ℝ≥0∞)) : CycEntry ℕ (k + 2)) = ς := by
        unfold CycEntry.len CycPath.cut
        simp only [CPath.cut_len]
      rw [hlen, ← hςeq]
      rw [hlen, ← hςeq] at hlt
      by_contra hcon
      rw [not_le] at hcon
      rcases le_total (escT2 (D.P ℓ) (entEnd ((δ, p.cut (ς : ℝ≥0∞)) : CycEntry ℕ (k + 2)))
          (max (escTm ((δ, p.cut (ς : ℝ≥0∞)) : CycEntry ℕ (k + 2))) (Real.log D.β)) - (ς : ℝ≥0∞))
          (ENNReal.ofReal ((4 : ℝ) ^ D.n) - (ς : ℝ≥0∞)) with hle | hle
      · -- the minimum is the `T₂`-part
        rw [min_eq_left hle] at hcon hlt
        set T2 := escT2 (D.P ℓ) (entEnd ((δ, p.cut (ς : ℝ≥0∞)) : CycEntry ℕ (k + 2)))
          (max (escTm ((δ, p.cut (ς : ℝ≥0∞)) : CycEntry ℕ (k + 2))) (Real.log D.β)) with hT2
        have hT2le : T2 ≤ (ς : ℝ≥0∞) + (T2 - ς) := le_add_tsub
        have hlt1 : T2 < (4 : ℝ≥0∞) ^ D.n := lt_of_le_of_lt hT2le hcon
        have hlt2 : T2 < p.1.jt (a + 1) := lt_of_le_of_lt hT2le hlt
        obtain ⟨s, hs, hslt⟩ := sInf_lt_iff.1
          (show sInf _ < min ((4 : ℝ≥0∞) ^ D.n) (p.1.jt (a + 1)) from
            lt_min hlt1 hlt2)
        obtain ⟨r, rfl, hMr, hnorm⟩ := hs
        have hlog0 : 0 < Real.log D.β := by linarith
        have hr0 : 0 ≤ r := by
          have := le_max_right (escTm ((δ, p.cut (ς : ℝ≥0∞)) : CycEntry ℕ (k + 2))) (Real.log D.β)
          linarith
        have hςr : (ς : ℝ) ≤ r := by
          have := le_max_left (escTm ((δ, p.cut (ς : ℝ≥0∞)) : CycEntry ℕ (k + 2))) (Real.log D.β)
          rw [tm_cut] at this hMr
          exact this.trans hMr
        have hr4 : r < 4 ^ D.n := by
          have := (lt_min_iff.1 hslt).1
          have h5 : ENNReal.ofReal r < ENNReal.ofReal ((4 : ℝ) ^ D.n) := by
            simpa [ENNReal.ofReal_pow] using this
          exact (ENNReal.ofReal_lt_ofReal_iff'.1 h5).1
        have hrj : ENNReal.ofReal r < p.1.jt (a + 1) := (lt_min_iff.1 hslt).2
        set t : ℝ≥0 := r.toNNReal with ht
        have htr : (t : ℝ) = r := Real.coe_toNNReal r hr0
        have hςt : ς ≤ t := by
          rw [← NNReal.coe_le_coe, htr]; exact hςr
        have htj : (t : ℝ≥0∞) < p.1.jt (a + 1) := by
          rw [ht]; exact hrj
        have hconst : ∀ x : ℝ≥0, ς ≤ x → x ≤ t → p.1.fn x = p.1.fn ς := by
          intro x hx1 hx2
          have h1 : a ≤ p.1.cnt x := by
            rw [← p.1.jt_le_iff a x, ← hςeq]; exact_mod_cast hx1
          have h2 : p.1.cnt x ≤ a := by
            by_contra hh
            rw [not_le] at hh
            have := (p.1.jt_le_iff (a + 1) x).2 hh
            exact absurd (this.trans_lt (lt_of_le_of_lt (by exact_mod_cast hx2) htj))
              (lt_irrefl _)
          have : p.1.cnt x = a := le_antisymm h2 h1
          rw [CPath.fn_eq_jv p.1 x, this]; rfl
        have hC2 : D.C2 ℓ ((δ, p.cut (t : ℝ≥0∞)) : CycEntry ℕ (k + 2)) := by
          unfold EscRP.C2
          rw [tm_cut, entEnd_cut, htr, hconst t hςt le_rfl]
          rw [tm_cut] at hMr
          refine ⟨(le_max_right _ _).trans hMr, ?_⟩
          have := hnorm
          rwa [entEnd_cut] at this
        have hC : D.Cany ℓ (CycRec.snoc ρ (δ, p.cut (t : ℝ≥0∞))) := by
          unfold EscRP.Cany
          right; left
          simpa [snoc_last'] using hC2
        exact hno t (by rw [htr]; exact hr4) hC
      · rw [min_eq_right hle] at hcon
        have : (4 : ℝ≥0∞) ^ D.n ≤ (ς : ℝ≥0∞) + (ENNReal.ofReal ((4 : ℝ) ^ D.n) - ς) := by
          have h := le_add_tsub (a := ENNReal.ofReal ((4 : ℝ) ^ D.n)) (b := (ς : ℝ≥0∞))
          simpa [ENNReal.ofReal_pow] using h
        exact absurd hcon (not_lt.2 this)

omit [Fact (0 < β)] in
theorem stopLen_le_pow {P : CycPlan ℕ (k + 2) β} {D : EscRP k} {m ℓ : ℕ}
    (hR : RuleAt P D m ℓ) (hlog : 1 < Real.log D.β) (ρ : CycRecN ℕ (k + 2) m)
    (p : CycPath (k + 2)) : P.stopLen m ρ p ≤ (4 : ℝ≥0∞) ^ D.n := by
  have hc : D.Cany ℓ (CycRec.snoc ρ (P.start m ρ, p.cut (((4 : ℝ≥0) ^ D.n : ℝ≥0) : ℝ≥0∞))) := by
    unfold EscRP.Cany
    right; right; right
    simp only [snoc_last']
    unfold EscRP.C7
    rw [tm_cut]; simp
  have := stopLen_le_of_cond hR hlog ρ p ((4 : ℝ≥0) ^ D.n) hc
  simpa using this

omit [Fact (0 < β)] in
theorem stopLen_eq_of_no_cond {P : CycPlan ℕ (k + 2) β} {D : EscRP k} {m ℓ : ℕ}
    (hR : RuleAt P D m ℓ) (hlog : 1 < Real.log D.β) (ρ : CycRecN ℕ (k + 2) m)
    (p : CycPath (k + 2))
    (hno : ∀ t : ℝ≥0, (t : ℝ) < 4 ^ D.n →
      ¬ D.Cany ℓ (CycRec.snoc ρ (P.start m ρ, p.cut (t : ℝ≥0∞)))) :
    P.stopLen m ρ p = (4 : ℝ≥0∞) ^ D.n :=
  le_antisymm (stopLen_le_pow hR hlog ρ p) (le_stopLen_of_no_cond hR hlog ρ p hno)

end ElboimSly.Paper.Escape
