/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55Step1
public import ElboimSly.Paper.Escape.Es53NumA
public import ElboimSly.Paper.Step.RegenMeas
public import ElboimSly.Foundations.Cyclic.CycRegenRecordPiece
public import ElboimSly.Foundations.Cyclic.CycClosingStopLen
public import ElboimSly.Foundations.Cyclic.CycRegenPiece
public import Mathlib

/-!
# `Es55DetAll`, part A: the first walk of `𝒫₅`

ES22 Lemma 5.5, Step 1.  On `𝒦(β')` the first entry of the final record of `𝒫₅` has length
`ξ_B` and ends at `W(ξ_B) ∈ B⁻`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ)
  (hlog : 1 < Real.log β) (ν : Measure (CycS ℕ (k + 2) β))

theorem dat5_zero :
    dat (plan5 n β tn u β' i hlog) ν 0 = regionData (k + 2) (0 : ℕ) := by
  simp [dat, plan5, plan5Start, regionData]

theorem pth5_zero_fn (hν : CycGood ν) (r : ℝ≥0) :
    (pth5 n tn u β' i hlog ν 0).1.fn r = ElboimSly.cycWalk (copyEnv ν 0) 0 0 (r : ℝ) := by
  unfold pth5 pth
  rw [dat5_zero, envPath_fn_regionData hν 0 r, copyEnv_eq_cycSlice]

theorem cut_end_eq (δ : CycData ℕ (k + 2)) (p : CycPath (k + 2)) {σ : ℝ≥0∞} (hσ : σ < ⊤) :
    entEnd ((δ, p.cut σ) : CycEntry ℕ (k + 2)) = p.1.fn σ.toNNReal := by
  have := entEnd_cut δ p σ.toNNReal
  rwa [ENNReal.coe_toNNReal hσ.ne] at this

theorem st0_iff (ρ : CycRecN ℕ (k + 2) 0) (p : CycPath (k + 2)) (a : ℕ)
    (hσ : p.1.jt a < ⊤) :
    (plan5 n β tn u β' i hlog).st 0 ((plan5 n β tn u β' i hlog).hatRec 0 ρ p a) = true ↔
      closeSt β (p.cut (p.1.jt a)) = true ∨ p.1.fn (p.1.jt a).toNNReal ∈ escBlock (escJ n) u := by
  classical
  unfold CycPlan.hatRec
  simp only [plan5, ite_true]
  unfold plan5St0
  simp only [snoc_last', Bool.or_eq_true, decide_eq_true_eq]
  rw [cut_end_eq _ p hσ]

open Classical in
theorem dl0_eq (ρ : CycRecN ℕ (k + 2) 0) (p : CycPath (k + 2)) (a : ℕ)
    (hσ : p.1.jt a < ⊤) :
    (plan5 n β tn u β' i hlog).dl 0 ((plan5 n β tn u β' i hlog).hatRec 0 ρ p a) =
      if p.1.fn (p.1.jt a).toNNReal ∈ escBlock (escJ n) u then 0
      else min (closeDl β (p.cut (p.1.jt a))) (ENNReal.ofReal tn - p.1.jt a) := by
  classical
  unfold CycPlan.hatRec
  simp only [plan5, ite_true]
  unfold plan5Dl0
  simp only [snoc_last']
  rw [cut_end_eq _ p hσ]
  have : ((p.cut (p.1.jt a)).1.len) = p.1.jt a := CPath.cut_len _ _
  simp only [CycEntry.len, this]

theorem pth5_zero_eq_escWalk (hν : CycGood ν) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) ≤ ElboimSly.cycTreg (copyEnv ν 0)) :
    (pth5 n tn u β' i hlog ν 0).1.fn r = escWalk ν (r : ℝ) := by
  have hg : ∀ j, Good (copyEnv ν j) := fun j => by
    rw [copyEnv_eq_cycSlice]; exact hν j
  have := regenWalk_piece (ν := fun k => copyEnv ν k) hg 0 (by simp [regenSigma_zero])
    (u := (r : ℝ)) r.2 (by simpa using hr)
  rw [pth5_zero_fn n tn u β' i hlog ν hν]
  unfold escWalk
  simpa [regenSigma_zero] using this.symm

theorem ent5_zero_len (hν : CycGood ν)
    (hle : escXi (escWalk ν) (escBlock (escJ n) u) ≤ ENNReal.ofReal tn)
    (hlt : escXi (escWalk ν) (escBlock (escJ n) u) < ElboimSly.cycTreg (copyEnv ν 0))
    (hB : escWalk ν (escXi (escWalk ν) (escBlock (escJ n) u)).toReal ∈ escBlock (escJ n) u) :
    (ent5 n tn u β' i hlog ν 0).len = escXi (escWalk ν) (escBlock (escJ n) u) := by
  classical
  set ξ := escXi (escWalk ν) (escBlock (escJ n) u) with hξ
  have hξtop : ξ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  set x := ξ.toNNReal with hx
  have hxξ : (x : ℝ≥0∞) = ξ := ENNReal.coe_toNNReal hξtop
  have hxR : (x : ℝ) = ξ.toReal := rfl
  set p := pth5 n tn u β' i hlog ν 0 with hp
  have hF1 : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ ElboimSly.cycTreg (copyEnv ν 0) →
      p.1.fn r = escWalk ν (r : ℝ) := fun r hr => pth5_zero_eq_escWalk n tn u β' i hlog ν hν r hr
  have hF2 : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ξ → escWalk ν (s : ℝ) ∉ escBlock (escJ n) u := by
    intro s hs hsB
    have : ξ ≤ (s : ℝ≥0∞) := iInf₂_le s hsB
    exact absurd hs (not_lt.2 this)
  have hxB : p.1.fn x ∈ escBlock (escJ n) u := by
    rw [hF1 x (by rw [hxξ]; exact hlt.le), hxR]; exact hB
  -- upper bound
  have hup := stopLen_plan5_zero_le n tn u β' i hlog
    ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) 0) p x hxB
  rw [← ent5_len n tn u β' i hlog ν 0, hxξ] at hup
  refine le_antisymm hup ?_
  rw [ent5_len n tn u β' i hlog ν 0, stopLen_eq_sInf_stopSet]
  refine le_sInf ?_
  -- every candidate is `≥ ξ`
  have hpos : ∀ σ : ℝ≥0∞, σ < ξ → p.1.fn σ.toNNReal ∉ escBlock (escJ n) u := by
    intro σ hσ hin
    have hσtop : σ < ⊤ := lt_trans hσ (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
    rw [hF1 _ (by rw [ENNReal.coe_toNNReal hσtop.ne]; exact (hσ.trans hlt).le)] at hin
    exact hF2 _ (by rw [ENNReal.coe_toNNReal hσtop.ne]; exact hσ) hin
  have hzero : ∀ σ : ℝ≥0∞, σ < ⊤ → p.1.fn σ.toNNReal = 0 →
      ∀ m : ℕ, 1 ≤ m → σ = ENNReal.ofReal (m * β) → ElboimSly.cycTreg (copyEnv ν 0) ≤ σ := by
    intro σ hσ h0 m hm hσm
    have hc : (σ.toNNReal : ℝ) = m * β := by
      have hβ : 0 < β := Fact.out
      rw [hσm, ENNReal.ofReal, ENNReal.toNNReal_coe, Real.coe_toNNReal _ (by positivity)]
    rw [hσm]
    refine cycTreg_le hm ?_
    rw [pth5_zero_fn n tn u β' i hlog ν hν, hc] at h0
    exact h0
  have hβ : 0 < β := Fact.out
  intro t ht
  by_contra hcon
  rw [not_le] at hcon
  rcases ht with ⟨a, ha1, hσ, hst, rfl⟩ | ⟨a, hσ, rfl, hlt2⟩
  · have hσξ := hcon
    rw [st0_iff n tn u β' i hlog _ p a hσ] at hst
    rcases hst with hc | hbB
    · obtain ⟨m, hm, hσm, h0⟩ := (closeSt_cut_iff p hσ).1 hc
      exact absurd (lt_of_lt_of_le (hcon.trans hlt) (hzero _ hσ h0 m hm hσm)) (lt_irrefl _)
    · exact hpos _ hσξ hbB
  · set σ := p.1.jt a with hσdef
    have hσle : σ ≤ σ + (plan5 n β tn u β' i hlog).dl 0
        ((plan5 n β tn u β' i hlog).hatRec 0
          ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) 0) p a) :=
      le_self_add
    have hσξ : σ < ξ := lt_of_le_of_lt hσle hcon
    rw [dl0_eq n tn u β' i hlog _ p a hσ] at hcon
    rw [dl0_eq n tn u β' i hlog _ p a hσ] at hlt2
    split_ifs at hcon hlt2 with hin
    · exact hpos _ hσξ hin
    · by_cases hd : closeDl β (p.cut σ) ≤ ENNReal.ofReal tn - σ
      · rw [min_eq_left hd] at hcon hlt2
        rw [closeDl_cut p hσ] at hcon hlt2
        by_cases hf : p.1.fn σ.toNNReal = 0
        · rw [ite_eq_left hf] at hcon hlt2
          obtain ⟨hn1, hn2, -⟩ := dl_facts (β := β) σ.toReal ENNReal.toReal_nonneg
          have hX : σ ≤ ENNReal.ofReal (β * (⌈max σ.toReal β / β⌉₊ : ℕ)) := by
            rw [← ENNReal.ofReal_toReal hσ.ne, mul_comm]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]; exact hn2
          rw [add_tsub_cancel_of_le hX] at hcon hlt2
          set T := ENNReal.ofReal (β * (⌈max σ.toReal β / β⌉₊ : ℕ)) with hT
          have hTtop : T < ⊤ := ENNReal.ofReal_lt_top
          have hfT : p.1.fn T.toNNReal = 0 := by
            have hle : p.1.jt a ≤ (T.toNNReal : ℝ≥0∞) := by
              rw [ENNReal.coe_toNNReal hTtop.ne]; exact hX
            have hlt3 : (T.toNNReal : ℝ≥0∞) < p.1.jt (a + 1) := by
              rw [ENNReal.coe_toNNReal hTtop.ne]; exact hlt2
            rw [fn_eq_of_jt p.1 hle hlt3, hf]
          have hTm : T = ENNReal.ofReal (((⌈max σ.toReal β / β⌉₊ : ℕ) : ℝ) * β) := by
            rw [hT, mul_comm]
          exact absurd (lt_of_lt_of_le (hcon.trans hlt)
            (hzero T hTtop hfT _ hn1 hTm)) (lt_irrefl _)
        · rw [ite_eq_right hf] at hcon
          simp at hcon
      · rw [not_le] at hd
        rw [min_eq_right hd.le] at hcon
        exact absurd (lt_of_le_of_lt (le_add_tsub (a := ENNReal.ofReal tn) (b := σ)) hcon)
          (not_lt.2 hle)

end ElboimSly.Paper.Escape
