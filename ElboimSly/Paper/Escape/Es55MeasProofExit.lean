/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55MeasProofEntry
public import ElboimSly.Paper.Escape.C57Jump
public import Mathlib

/-!
# The exit event is a function of the backward walk of `𝒫₅`

The connecting plan (entry `I + 1`, the backward walk stopped at the first exit from `𝒬`
or at length `4^{j-1}`), ES22 Claim 5.7 (`r_i ≤ 4^{j-1}`, `W_i^←(r_i) ∈ F_B`).

For a good environment `ν`, `ν ∈ es55Exit` is a property `EscH` of entry `I + 1` of the final record
of `plan5` (`mem_es55Exit_iff`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

theorem escFace_disjoint_escQ {j : ℕ} (hj : 1 ≤ j) (u : EscV k) :
    Disjoint (escFace j u) (escQ j u) := by
  rw [Set.disjoint_left]
  intro x hx hq
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have h1 := hx.1
  have h2 := hq.1.1
  have h3 : (2 : ℤ) ^ (j' + 1) / 2 = 2 ^ j' := by
    rw [pow_succ]; omega
  simp only [Nat.add_sub_cancel] at h1
  rw [h3] at h2
  omega

theorem toNNReal_four_pow {j : ℕ} (hj : 1 ≤ j) :
    ENNReal.ofReal ((4 : ℝ) ^ (j - 1)) =
      ((Real.toNNReal (((2 : ℝ) ^ j) ^ 2 / 4) : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have : ((2 : ℝ) ^ (j' + 1)) ^ 2 / 4 = 4 ^ (j' + 1 - 1) := by
    rw [Nat.add_sub_cancel, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    ring
  rw [this]; rfl

section back

variable (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
  (ρ : CycRecN ℕ (k + 2) (escIstar n (escJ n) + 1)) (p : CycPath (k + 2))

theorem plan5_hatB (a : ℕ) :
    (plan5 n β tn u β' i hlog).hatRec (escIstar n (escJ n) + 1) ρ p a
        (Fin.last (escIstar n (escJ n) + 1)) =
      ((plan5 n β tn u β' i hlog).start (escIstar n (escJ n) + 1) ρ, p.cut (p.1.jt a)) := by
  unfold CycPlan.hatRec
  exact snoc_last' _ _

theorem plan5_st_back (ρ' : CycRecN ℕ (k + 2) (escIstar n (escJ n) + 1 + 1)) :
    (plan5 n β tn u β' i hlog).st (escIstar n (escJ n) + 1) ρ' = plan5StB (escJ n) u ρ' := by
  simp [plan5]

theorem plan5_dl_back (ρ' : CycRecN ℕ (k + 2) (escIstar n (escJ n) + 1 + 1)) :
    (plan5 n β tn u β' i hlog).dl (escIstar n (escJ n) + 1) ρ' = plan5DlB (escJ n) ρ' := by
  simp [plan5]

theorem plan5_stB_iff (a : ℕ) (ha : p.1.jt a < ⊤) :
    (plan5 n β tn u β' i hlog).st (escIstar n (escJ n) + 1)
        ((plan5 n β tn u β' i hlog).hatRec (escIstar n (escJ n) + 1) ρ p a) = true ↔
      p.1.fn (p.1.jt a).toNNReal ∉ escQ (escJ n) u := by
  classical
  rw [plan5_st_back]
  unfold plan5StB
  rw [plan5_hatB n tn u β' i hlog ρ p a, entEnd_cut' _ p ha]
  simp

theorem plan5_dlB_eq (a : ℕ) :
    (plan5 n β tn u β' i hlog).dl (escIstar n (escJ n) + 1)
        ((plan5 n β tn u β' i hlog).hatRec (escIstar n (escJ n) + 1) ρ p a) =
      ENNReal.ofReal ((4 : ℝ) ^ (escJ n - 1)) - p.1.jt a := by
  rw [plan5_dl_back]
  unfold plan5DlB
  rw [plan5_hatB n tn u β' i hlog ρ p a, len_cut']

/-- The backward walk stops at its first exit from `𝒬`. -/
theorem stopLenB_le (a : ℕ) (ha1 : 1 ≤ a) (ha : p.1.jt a < ⊤)
    (hQ : p.1.jv a ∉ escQ (escJ n) u) :
    (plan5 n β tn u β' i hlog).stopLen (escIstar n (escJ n) + 1) ρ p ≤ p.1.jt a := by
  refine sInf_le (Or.inl ⟨a, ha1, ha, ?_, rfl⟩)
  rw [plan5_stB_iff n tn u β' i hlog ρ p a ha]
  exact hQ

theorem le_stopLenB {c : ℝ≥0∞}
    (h1 : ∀ a : ℕ, 1 ≤ a → p.1.jt a < ⊤ → p.1.jv a ∉ escQ (escJ n) u → c ≤ p.1.jt a)
    (h2 : c ≤ ENNReal.ofReal ((4 : ℝ) ^ (escJ n - 1))) :
    c ≤ (plan5 n β tn u β' i hlog).stopLen (escIstar n (escJ n) + 1) ρ p := by
  unfold CycPlan.stopLen
  refine le_sInf ?_
  rintro t (⟨a, ha1, ha, hst, rfl⟩ | ⟨a, ha, rfl, -⟩)
  · rw [plan5_stB_iff n tn u β' i hlog ρ p a ha] at hst
    exact h1 a ha1 ha hst
  · rw [plan5_dlB_eq n tn u β' i hlog ρ p a]
    exact h2.trans le_add_tsub

theorem stopLenB_le_pow :
    (plan5 n β tn u β' i hlog).stopLen (escIstar n (escJ n) + 1) ρ p ≤
      ENNReal.ofReal ((4 : ℝ) ^ (escJ n - 1)) := by
  set r : ℝ≥0 := ((4 : ℝ) ^ (escJ n - 1)).toNNReal with hr
  have hrt : ((r : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((4 : ℝ) ^ (escJ n - 1)) := rfl
  set a := p.1.cnt r with ha
  have hja : p.1.jt a ≤ r := (p.1.jt_le_iff a r).2 le_rfl
  have hjb : (r : ℝ≥0∞) < p.1.jt (a + 1) := by
    by_contra h
    rw [not_lt] at h
    have := (p.1.jt_le_iff (a + 1) r).1 h
    omega
  have hlt : p.1.jt a < ⊤ := lt_of_le_of_lt hja ENNReal.coe_lt_top
  have hc' : p.1.jt a + (plan5 n β tn u β' i hlog).dl (escIstar n (escJ n) + 1)
      ((plan5 n β tn u β' i hlog).hatRec (escIstar n (escJ n) + 1) ρ p a) =
      ENNReal.ofReal ((4 : ℝ) ^ (escJ n - 1)) := by
    rw [plan5_dlB_eq n tn u β' i hlog ρ p a, add_tsub_cancel_of_le (by rw [← hrt]; exact hja)]
  have hlt2 : p.1.jt a + (plan5 n β tn u β' i hlog).dl (escIstar n (escJ n) + 1)
      ((plan5 n β tn u β' i hlog).hatRec (escIstar n (escJ n) + 1) ρ p a) < p.1.jt (a + 1) := by
    rw [hc', ← hrt]; exact hjb
  exact le_trans (sInf_le (a := p.1.jt a + (plan5 n β tn u β' i hlog).dl
    (escIstar n (escJ n) + 1)
    ((plan5 n β tn u β' i hlog).hatRec (escIstar n (escJ n) + 1) ρ p a))
    (Or.inr ⟨a, hlt, rfl, hlt2⟩)) hc'.le

end back

/-- The event on the backward walk of `𝒫₅` that describes the exit event. -/
def EscH (j : ℕ) (u : EscV k) (S : ℝ≥0) (e : CycEntry ℕ (k + 2)) : Prop :=
  e.path.fn 0 ∈ escQ j u ∧ e.len ≤ (S : ℝ≥0∞) ∧ entEnd e ∈ escFace j u

section exit

variable (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
  (ν : Measure (CycS ℕ (k + 2) β))

theorem dat5_back :
    dat (plan5 n β tn u β' i hlog) ν (escIstar n (escJ n) + 1) =
      (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2)) := by
  show plan5Start (escRP n β u 1 : EscRP k) i β' (escIstar n (escJ n) + 1) = _
  simp [plan5Start, escRP]

theorem exitPath_of_good (hν : CycGood ν) (δ : CycData ℕ (k + 2)) :
    exitPath δ ν = envPath ν δ := by
  unfold exitPath
  have : cycNgood (fun ν : Measure (CycS ℕ (k + 2) β) => ν) ν = ν := by simp [cycNgood, hν]
  rw [this]

/-- **The exit event is a function of the backward walk of `𝒫₅`.** -/
theorem mem_es55Exit_iff (hν : CycGood ν) (hj : 1 ≤ escJ n) :
    ν ∈ es55Exit β n u β' i ↔
      EscH (escJ n) u (Real.toNNReal (((2 : ℝ) ^ escJ n) ^ 2 / 4))
        (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)) := by
  classical
  set m := escIstar n (escJ n) + 1 with hm
  set p := pth5 n tn u β' i hlog ν m with hp
  set ρ0 := (plan5 n β tn u β' i hlog).ideal (rule (plan5 n β tn u β' i hlog) ν) m with hρ0
  set Ls := (plan5 n β tn u β' i hlog).stopLen m ρ0 p with hLs
  set Q := escQ (escJ n) u with hQdef
  set F := escFace (escJ n) u with hFdef
  set S : ℝ≥0 := Real.toNNReal (((2 : ℝ) ^ escJ n) ^ 2 / 4) with hSdef
  have hS : ENNReal.ofReal ((4 : ℝ) ^ (escJ n - 1)) = (S : ℝ≥0∞) := toNNReal_four_pow hj
  have hdis : Disjoint F Q := escFace_disjoint_escQ hj u
  have he : ent5 n tn u β' i hlog ν m =
      (dat (plan5 n β tn u β' i hlog) ν m, p.cut Ls) := ent5_eq n tn u β' i hlog ν m
  have hLtop : Ls < ⊤ := lt_of_le_of_lt (stopLenB_le_pow n tn u β' i hlog ρ0 p) (by
    rw [hS]; exact ENNReal.coe_lt_top)
  have hp' : p = envPath ν (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) :
      CycData ℕ (k + 2)) := by
    rw [hp]; unfold pth5 pth; rw [hm, dat5_back]
  have hjv0 : p.1.fn 0 = p.1.jv 0 := by
    rw [CPath.fn_eq_jv, cnt_zero']
  have hExit : ν ∈ es55Exit β n u β' i ↔ ExitJ Q F (S : ℝ≥0∞) p.1 := by
    unfold es55Exit exitSet
    rw [mem_ofPred_eq, exitPath_of_good ν hν, ← hp']
  rw [hExit]
  have hlen : CycEntry.len (ent5 n tn u β' i hlog ν m) = Ls := by rw [he]; exact len_cut' _ p Ls
  have hend : entEnd (ent5 n tn u β' i hlog ν m) = p.1.fn Ls.toNNReal := by
    rw [he]; exact entEnd_cut' _ p hLtop
  have hstart : (ent5 n tn u β' i hlog ν m).path.fn 0 = p.1.fn 0 := by
    rw [he]
    have := cut_fn_apply (dat (plan5 n β tn u β' i hlog) ν m) p Ls.toNNReal 0
    rw [ENNReal.coe_toNNReal hLtop.ne] at this
    rw [this]; simp
  unfold EscH
  rw [hlen, hend, hstart]
  constructor
  · rintro ⟨a, ha1, hjt, hFa, hQa⟩
    have hjtop : p.1.jt a < ⊤ := lt_of_le_of_lt hjt ENNReal.coe_lt_top
    have hnotQ : p.1.jv a ∉ Q := fun h => Set.disjoint_left.1 hdis hFa h
    have hLle : Ls ≤ p.1.jt a := stopLenB_le n tn u β' i hlog ρ0 p a ha1 hjtop hnotQ
    have hLge : p.1.jt a ≤ Ls := by
      refine le_stopLenB n tn u β' i hlog ρ0 p ?_ (by rw [hS]; exact hjt)
      intro a'' ha1'' hjt'' hnQ
      by_contra hcon
      rw [not_le] at hcon
      have : a'' < a := by
        by_contra hge
        exact absurd (jt_mono_le p.1 (not_lt.1 hge)) (not_le.2 hcon)
      exact hnQ (hQa a'' this)
    have hL : Ls = p.1.jt a := le_antisymm hLle hLge
    refine ⟨?_, ?_, ?_⟩
    · rw [hjv0]; exact hQa 0 (by omega)
    · rw [hL]; exact hjt
    · rw [hL]; exact hFa
  · rintro ⟨hst, hl, hF'⟩
    set r : ℝ≥0 := Ls.toNNReal with hr
    have hrL : (r : ℝ≥0∞) = Ls := ENNReal.coe_toNNReal hLtop.ne
    set a := p.1.cnt r with ha
    have hja : p.1.jt a ≤ r := (p.1.jt_le_iff a r).2 le_rfl
    have hjtop : p.1.jt a < ⊤ := lt_of_le_of_lt hja ENNReal.coe_lt_top
    have hend' : p.1.fn r = p.1.jv a := CPath.fn_eq_jv p.1 r
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, ← hjv0] at hend'
      exact Set.disjoint_left.1 hdis hF' (by rw [hend']; exact hst)
    have hFa : p.1.jv a ∈ F := by rw [← hend']; exact hF'
    have hnotQ : p.1.jv a ∉ Q := fun h => Set.disjoint_left.1 hdis hFa h
    have hLle : Ls ≤ p.1.jt a := stopLenB_le n tn u β' i hlog ρ0 p a (by omega) hjtop hnotQ
    have hL : p.1.jt a = Ls := le_antisymm (hrL ▸ hja) hLle
    refine ⟨a, by omega, hL ▸ hl, hFa, ?_⟩
    intro b hb
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · rw [hb0, ← hjv0]; exact hst
    · by_contra hbQ
      have hlt : p.1.jt b < p.1.jt a := jt_lt_of_lt p.1 hb hjtop
      have := stopLenB_le n tn u β' i hlog ρ0 p b hb0 (lt_trans hlt hjtop) hbQ
      rw [hL] at hlt
      exact absurd hlt (not_lt.2 this)

end exit

end ElboimSly.Paper.Escape
