/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55MeasProofEntry0
public import ElboimSly.Paper.Escape.Plan5Env
public import ElboimSly.Paper.Heavy.TwoTransfer
public import ElboimSly.Paper.Step.RegenMeas
public import Mathlib

/-!
# `𝒦(β')` is a function of the first walk of `𝒫₅`

t' and escK(β'); The connecting plan.

For a good environment `ν`, the event `ν ∈ 𝒦(β')` is a property `EscG0` of entry `0` of the final
record of `plan5` (`mem_escKSet_iff`): the first walk stops at `ξ` (the first entrance into `B`)
when `ξ ≤ t_n` and `ξ < t_reg`, and then does not close.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

theorem escBlockMinus_subset_meas (j : ℕ) (u : EscV k) : escBlockMinus j u ⊆ escBlock j u := by
  intro x hx c
  by_cases hc : c = 0
  · subst hc
    refine ⟨hx.1.1, lt_of_lt_of_le hx.1.2 ?_⟩
    have : (2 : ℤ) ^ (j - 1) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    linarith
  · exact hx.2 c hc

/-- Entrance times agree when the paths agree up to a bound that exceeds one of them. -/
theorem xi_eq_of_lt {V : Type*} (B : Set V) (W : ℝ → V) (f : ℝ≥0 → V) (T : ℝ≥0∞)
    (hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → W (t : ℝ) = f t)
    (h : (⨅ (t : ℝ≥0) (_ : W t ∈ B), (t : ℝ≥0∞)) < T ∨
      (⨅ (t : ℝ≥0) (_ : f t ∈ B), (t : ℝ≥0∞)) < T) :
    (⨅ (t : ℝ≥0) (_ : W t ∈ B), (t : ℝ≥0∞)) = ⨅ (t : ℝ≥0) (_ : f t ∈ B), (t : ℝ≥0∞) := by
  have key : ∀ (g g' : ℝ≥0 → V), (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → g t = g' t) →
      (⨅ (t : ℝ≥0) (_ : g t ∈ B), (t : ℝ≥0∞)) < T →
      (⨅ (t : ℝ≥0) (_ : g' t ∈ B), (t : ℝ≥0∞)) ≤ ⨅ (t : ℝ≥0) (_ : g t ∈ B), (t : ℝ≥0∞) := by
    intro g g' hgg h
    obtain ⟨t0, ht0⟩ := iInf_lt_iff.1 h
    obtain ⟨hB0, ht0'⟩ := iInf_lt_iff.1 ht0
    have hA' : (⨅ (t : ℝ≥0) (_ : g' t ∈ B), (t : ℝ≥0∞)) ≤ t0 :=
      iInf₂_le_of_le t0 (by rw [← hgg t0 ht0'.le]; exact hB0) le_rfl
    refine le_iInf fun t => le_iInf fun hB => ?_
    by_cases ht : (t : ℝ≥0∞) ≤ T
    · exact iInf₂_le_of_le t (by rw [← hgg t ht]; exact hB) le_rfl
    · exact hA'.trans (ht0'.le.trans (not_le.1 ht).le)
  set Wn : ℝ≥0 → V := fun t => W (t : ℝ) with hWn
  rcases h with h | h
  · have h1 := key Wn f hag h
    exact le_antisymm (key f Wn (fun t ht => (hag t ht).symm) (lt_of_le_of_lt h1 h)) h1
  · have h1 := key f Wn (fun t ht => (hag t ht).symm) h
    exact le_antisymm h1 (key Wn f hag (lt_of_le_of_lt h1 h))

section entry

variable (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
  (ν : Measure (CycS ℕ (k + 2) β))

theorem dat5_zero_ent :
    dat (plan5 n β tn u β' i hlog) ν 0 = (((0 : ℕ), (0 : EscV k), (0 : ℝ), true) : CycData ℕ (k + 2)) := by
  show plan5Start (escRP n β u 1 : EscRP k) i β' 0 = _
  simp [plan5Start]

/-- The first walk of `𝒫₅` is the cyclic walk of the slice `0`. -/
theorem pth5_zero_fn_meas (hν : CycGood ν) (s : ℝ≥0) :
    (pth5 n tn u β' i hlog ν 0).1.fn s = ElboimSly.cycWalk (copyEnv ν 0) 0 0 (s : ℝ) := by
  have hd := dat5_zero_ent n tn u β' i hlog ν
  have hp : pth5 n tn u β' i hlog ν 0 =
      envPath ν (((0 : ℕ), (0 : EscV k), (0 : ℝ), true) : CycData ℕ (k + 2)) := by
    unfold pth5 pth
    rw [hd]
  rw [hp, (envPath_len (δ := (((0 : ℕ), (0 : EscV k), (0 : ℝ), true) : CycData ℕ (k + 2)))
    (hν 0)).2, envFn_fwd' ν _ rfl s]
  rw [copyEnv_eq_cycSlice]
  rfl

theorem pathTreg_pth5_zero (hν : CycGood ν) :
    pathTreg β.toNNReal (pth5 n tn u β' i hlog ν 0).1.fn = cycTreg (copyEnv ν 0) := by
  have hf : (pth5 n tn u β' i hlog ν 0).1.fn =
      fun s : ℝ≥0 => ElboimSly.cycWalk (copyEnv ν 0) 0 0 (s : ℝ) :=
    funext (pth5_zero_fn_meas n tn u β' i hlog ν hν)
  rw [hf]
  exact pathTreg_cycWalk _

theorem escWalk_eq_pth5_zero (hν : CycGood ν) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤ cycTreg (copyEnv ν 0)) :
    escWalk ν (t : ℝ) = (pth5 n tn u β' i hlog ν 0).1.fn t := by
  have hg : ∀ m, Good (copyEnv ν m) := fun m => by rw [copyEnv_eq_cycSlice]; exact hν m
  rw [pth5_zero_fn_meas n tn u β' i hlog ν hν]
  have := Heavy.regenWalk_eq_piece0 (ν := fun m => copyEnv ν m) hg (T := (t : ℝ))
    (by rw [ENNReal.ofReal_coe_nnreal]; exact ht) (t : ℝ) ⟨t.2, le_rfl⟩
  exact this

/-- The event on the first walk of `𝒫₅` that describes `𝒦(β')`. -/
def EscG0 (β tn : ℝ) (j : ℕ) (Bm : Set (EscV k)) (β' : ℕ) (e : CycEntry ℕ (k + 2)) : Prop :=
  e.len ≤ ENNReal.ofReal tn ∧ entEnd e ∈ Bm ∧ closeSt β e.2 = false ∧
    cycIntPhase β (cycFloor β (e.len.toReal + 4 ^ j)) = (β' : ℝ)

theorem pathTreg_le_of_close (p : CycPath (k + 2)) {L : ℝ≥0∞} (j : ℕ) (hj : 1 ≤ j)
    (h1 : L = ENNReal.ofReal (j * β)) (h2 : p.1.fn L.toNNReal = 0) :
    pathTreg β.toNNReal p.1.fn ≤ L := by
  have h3 : L.toNNReal = (j : ℝ≥0) * β.toNNReal := by
    rw [h1, ofReal_nat_mul, ENNReal.toNNReal_coe]
  have h4 : (((j : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ≥0∞) = L := by rw [h1, ofReal_nat_mul]
  exact iInf_le_of_le ⟨j, hj, (congrArg p.1.fn h3).symm.trans h2⟩ (le_of_eq h4)

/-- **`𝒦(β')` is a function of the first walk of `𝒫₅`.** -/
theorem escK_iff_G0 (hν : CycGood ν) :
    EscK β tn (escJ n) (escBlockMinus (escJ n) u) (escWalk ν)
        (escXi (escWalk ν) (escBlock (escJ n) u)) (cycTreg (copyEnv ν 0)) β' ↔
      EscG0 β tn (escJ n) (escBlockMinus (escJ n) u) β' (ent5 n tn u β' i hlog ν 0) := by
  classical
  set p := pth5 n tn u β' i hlog ν 0 with hp
  set Ls := (plan5 n β tn u β' i hlog).stopLen 0
    ((plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) 0) p with hLs
  set B := escBlock (escJ n) u with hB
  set Bm := escBlockMinus (escJ n) u with hBm
  set treg := cycTreg (copyEnv ν 0) with htreg
  have he : ent5 n tn u β' i hlog ν 0 =
      (dat (plan5 n β tn u β' i hlog) ν 0, p.cut Ls) := ent5_eq n tn u β' i hlog ν 0
  have hTreg : pathTreg β.toNNReal p.1.fn = treg := pathTreg_pth5_zero n tn u β' i hlog ν hν
  have hLform : Ls = min (min (pathXi0 B p.1) treg) (ENNReal.ofReal tn) := by
    rw [hLs, stopLen0_eq n tn u β' i hlog, hTreg]
  have hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ treg → escWalk ν (t : ℝ) = p.1.fn t :=
    fun t ht => escWalk_eq_pth5_zero n tn u β' i hlog ν hν t ht
  have hlen : CycEntry.len (ent5 n tn u β' i hlog ν 0) = Ls := by rw [he]; exact len_cut' _ p Ls
  have hpath : (ent5 n tn u β' i hlog ν 0).2 = p.cut Ls := by rw [he]
  unfold EscK EscG0
  rw [hlen, hpath]
  constructor
  · rintro ⟨hξtn, hξT, hW, hphase⟩
    have hξeq : escXi (escWalk ν) B = pathXi0 B p.1 :=
      xi_eq_of_lt B (escWalk ν) p.1.fn treg hag (Or.inl hξT)
    have hξT' : pathXi0 B p.1 < treg := hξeq ▸ hξT
    have hξtn' : pathXi0 B p.1 ≤ ENNReal.ofReal tn := hξeq ▸ hξtn
    have hLξ : Ls = escXi (escWalk ν) B := by
      rw [hLform, hξeq, min_eq_left hξT'.le, min_eq_left hξtn']
    have hLtop : Ls < ⊤ := hLξ ▸ lt_of_le_of_lt hξtn ENNReal.ofReal_lt_top
    have hξL : escXi (escWalk ν) B = Ls := hLξ.symm
    refine ⟨hξL ▸ hξtn, ?_, ?_, ?_⟩
    · rw [he, entEnd_cut' _ p hLtop]
      have h1 := hag Ls.toNNReal (ENNReal.coe_toNNReal_le_self.trans (hξL ▸ hξT).le)
      have h2 : ((Ls.toNNReal : ℝ≥0) : ℝ) = (escXi (escWalk ν) B).toReal := by
        rw [hξL]; rfl
      rw [h2] at h1
      rw [← h1]; exact hW
    · by_contra hcl
      have hcl' : closeSt β (p.cut Ls) = true := by simpa using hcl
      rw [closeSt_cut_iff p hLtop] at hcl'
      obtain ⟨j, hj, h1, h2⟩ := hcl'
      have : treg ≤ Ls := hTreg ▸ pathTreg_le_of_close p j hj h1 h2
      exact absurd (hξL ▸ hξT) (not_lt.2 this)
    · rw [← hξL]; exact hphase
  · rintro ⟨hLtn, hend, hcl, hphase⟩
    have hLtop : Ls < ⊤ := lt_of_le_of_lt hLtn ENNReal.ofReal_lt_top
    rw [he, entEnd_cut' _ p hLtop] at hend
    have hξ'le : pathXi0 B p.1 ≤ Ls :=
      iInf₂_le_of_le Ls.toNNReal (escBlockMinus_subset_meas _ _ hend)
        (by rw [ENNReal.coe_toNNReal hLtop.ne])
    have hLle : Ls ≤ pathXi0 B p.1 := by
      rw [hLform]; exact (min_le_left _ _).trans (min_le_left _ _)
    have hξ' : pathXi0 B p.1 = Ls := le_antisymm hξ'le hLle
    have hLT : Ls ≤ treg := by
      rw [hLform]; exact (min_le_left _ _).trans (min_le_right _ _)
    have hlt : Ls < treg := by
      by_contra hnl
      have hteq : treg = Ls := le_antisymm (not_lt.1 hnl) hLT
      have hfin : pathTreg β.toNNReal p.1.fn < ⊤ := by rw [hTreg, hteq]; exact hLtop
      obtain ⟨j, hj, h1, h2⟩ := pathTreg_exists hfin
      have hcl' : closeSt β (p.cut Ls) = true := by
        rw [closeSt_cut_iff p hLtop]
        have h5 : Ls = (((j : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ≥0∞) := by rw [← hteq, ← hTreg, h1]
        refine ⟨j, hj, ?_, ?_⟩
        · rw [h5, ofReal_nat_mul]
        · rw [h5, ENNReal.toNNReal_coe]; exact h2
      rw [hcl] at hcl'
      exact absurd hcl' (by simp)
    have hξeq : escXi (escWalk ν) B = pathXi0 B p.1 :=
      xi_eq_of_lt B (escWalk ν) p.1.fn treg hag (Or.inr (by show pathXi0 B p.1 < treg; rw [hξ']; exact hlt))
    have hξL : escXi (escWalk ν) B = Ls := hξeq.trans hξ'
    refine ⟨hξL ▸ hLtn, hξL ▸ hlt, ?_, ?_⟩
    · have h1 := hag Ls.toNNReal (ENNReal.coe_toNNReal_le_self.trans hLT)
      have h2 : ((Ls.toNNReal : ℝ≥0) : ℝ) = (escXi (escWalk ν) B).toReal := by
        rw [hξL]; rfl
      rw [h2] at h1
      rw [h1]; exact hend
    · rw [hξL]; exact hphase

end entry

end ElboimSly.Paper.Escape
