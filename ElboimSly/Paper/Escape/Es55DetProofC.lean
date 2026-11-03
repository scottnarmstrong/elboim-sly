/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55DetProofB
public import ElboimSly.Paper.Escape.C57Env
public import ElboimSly.Paper.Escape.C57Jump
public import ElboimSly.Paper.Escape.StopLenCut
public import Mathlib

/-!
# `Es55DetAll`, part C: the backward walk exits `𝒬` through `F_B`

ES22 Lemma 5.5, Step 1.  On the exit set the last entry of the final record of `𝒫₅` is the
backward walk cut at its first exit time `jt a ≤ 4^{j-1}`, so `D55Exit` holds for it.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ)
  (hlog : 1 < Real.log β) (ν : Measure (CycS ℕ (k + 2) β))

theorem stB_iff (ρ : CycRecN ℕ (k + 2) (escIstar n (escJ n) + 1)) (p : CycPath (k + 2)) (a : ℕ)
    (hσ : p.1.jt a < ⊤) :
    (plan5 n β tn u β' i hlog).st (escIstar n (escJ n) + 1)
      ((plan5 n β tn u β' i hlog).hatRec (escIstar n (escJ n) + 1) ρ p a) = true ↔
      p.1.jv a ∉ escQ (escJ n) u := by
  classical
  unfold CycPlan.hatRec
  have h0 : escIstar n (escJ n) + 1 ≠ 0 := Nat.succ_ne_zero _
  have h1 : ¬ (escIstar n (escJ n) + 1 ≤ escIstar n (escJ n)) := by omega
  simp only [plan5, h0, h1, ite_false, ite_true]
  unfold plan5StB
  simp only [snoc_last', decide_eq_true_eq]
  rw [cut_end_eq _ p hσ]
  rfl

theorem dlB_eq (ρ : CycRecN ℕ (k + 2) (escIstar n (escJ n) + 1)) (p : CycPath (k + 2)) (a : ℕ)
    (_hσ : p.1.jt a < ⊤) :
    (plan5 n β tn u β' i hlog).dl (escIstar n (escJ n) + 1)
      ((plan5 n β tn u β' i hlog).hatRec (escIstar n (escJ n) + 1) ρ p a) =
      ENNReal.ofReal ((4 : ℝ) ^ (escJ n - 1)) - p.1.jt a := by
  unfold CycPlan.hatRec
  have h0 : escIstar n (escJ n) + 1 ≠ 0 := Nat.succ_ne_zero _
  have h1 : ¬ (escIstar n (escJ n) + 1 ≤ escIstar n (escJ n)) := by omega
  simp only [plan5, h0, h1, ite_false, ite_true]
  unfold plan5DlB
  simp only [snoc_last']
  have : ((p.cut (p.1.jt a)).1.len) = p.1.jt a := CPath.cut_len _ _
  simp only [CycEntry.len, this]

/-- The stopping length of the backward walk is at least the exit jump time. -/
theorem le_stopLen_back (p : CycPath (k + 2)) (ρ : CycRecN ℕ (k + 2) (escIstar n (escJ n) + 1))
    {a : ℕ} (hS : p.1.jt a ≤ ENNReal.ofReal ((4 : ℝ) ^ (escJ n - 1)))
    (hQ : ∀ b < a, p.1.jv b ∈ escQ (escJ n) u) :
    p.1.jt a ≤ (plan5 n β tn u β' i hlog).stopLen (escIstar n (escJ n) + 1) ρ p := by
  rw [stopLen_eq_sInf_stopSet]
  refine le_sInf ?_
  rintro t (⟨b, hb1, hσ, hst, rfl⟩ | ⟨b, hσ, rfl, -⟩)
  · rw [stB_iff n tn u β' i hlog ρ p b hσ] at hst
    by_cases hba : a ≤ b
    · exact jt_mono_le p.1 hba
    · exact absurd (hQ b (by omega)) hst
  · rw [dlB_eq n tn u β' i hlog ρ p b hσ]
    by_cases hba : a ≤ b
    · exact (jt_mono_le p.1 hba).trans le_self_add
    · exact hS.trans le_add_tsub

theorem two_pow_sq_div_four {j : ℕ} (hj : 1 ≤ j) : ((2 : ℝ) ^ j) ^ 2 / 4 = (4 : ℝ) ^ (j - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4, ← pow_mul, ← pow_mul]
  ring

theorem ent5_back_exit (hν : CycGood ν) (hj : 1 ≤ escJ n)
    (hx : ν ∈ es55Exit β n u β' i) :
    ∃ a : ℕ, D55Exit (escJ n) u (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)) a ∧
      (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).path.jt a ≤
        ENNReal.ofReal ((4 : ℝ) ^ (escJ n - 1)) := by
  have hdat : dat (plan5 n β tn u β' i hlog) ν (escIstar n (escJ n) + 1) =
      (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2)) := by
    have := ent5_data_back n tn u β' i hlog ν
    rw [ent5_eq] at this
    exact this
  have hng : cycNgood (fun ν : Measure (CycS ℕ (k + 2) β) => ν) ν = ν := by
    unfold cycNgood; rw [ite_eq_left hν]
  have hpth : (pth5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).1 =
      (exitPath (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2)) ν).1 := by
    unfold exitPath pth5 pth
    rw [hng, hdat]
  obtain ⟨a, ha1, haS, haF, haQ⟩ := hx
  have hSe : (((Real.toNNReal (((2 : ℝ) ^ escJ n) ^ 2 / 4) : ℝ≥0)) : ℝ≥0∞) =
      ENNReal.ofReal ((4 : ℝ) ^ (escJ n - 1)) := by
    rw [two_pow_sq_div_four hj]; rfl
  rw [hSe, ← hpth] at haS
  rw [← hpth] at haF haQ
  set p := pth5 n tn u β' i hlog ν (escIstar n (escJ n) + 1) with hp
  set L := (plan5 n β tn u β' i hlog).stopLen (escIstar n (escJ n) + 1)
    ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν)
      (escIstar n (escJ n) + 1)) p with hL
  have hLa : p.1.jt a ≤ L := le_stopLen_back n tn u β' i hlog p _ haS haQ
  have hpath : (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)).path = p.1.cut L := by
    rw [ent5_eq]; rfl
  have hjt : ∀ b ≤ a, (p.1.cut L).jt b = p.1.jt b := fun b hb => by
    rw [CPath.jt_cut, ite_eq_left ((jt_mono_le p.1 hb).trans hLa)]
  have hjv : ∀ b ≤ a, (p.1.cut L).jv b = p.1.jv b := fun b hb =>
    CPath.jv_cut p.1 L b ((jt_mono_le p.1 hb).trans hLa)
  refine ⟨a, ⟨ha1, ?_, ?_⟩, ?_⟩
  · rw [hpath, hjv a le_rfl]; exact haF
  · intro b hb; rw [hpath, hjv b hb.le]; exact haQ b hb
  · rw [hpath, hjt a le_rfl]; exact haS

end ElboimSly.Paper.Escape
