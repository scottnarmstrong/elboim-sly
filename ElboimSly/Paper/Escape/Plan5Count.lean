/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan5Shift
public import ElboimSly.Paper.Escape.ReadDisjoint
public import ElboimSly.Paper.Escape.DensityG
public import ElboimSly.Paper.Escape.VisitsG
public import ElboimSly.Paper.Escape.DensityAux
public import Mathlib

/-!
# The avoided set `A₇` is sparse

ES22 Claim 5.7 (the bound `|A₇ ∩ (p_i + [-r, r]^d)| ≤ r^{8/3}`, via vertices visited by an explored walk (b)
and density of the explored walks around p_i).

`count_avoid`: for every good environment `ν`, every `r ≥ L₇`, the number of points of
`A₇ = avoidSet p_i L₇ (ent5 ν) I` in `p_i + [-r, r]^d` is at most `r^{8/3}`, provided
`3^d C_vis (r+1)² (ln (r+1))^{2d+2} ≤ r^{8/3}/2` for `r ≥ L₇` (this is the choice of `r_7(d)`)
and `n ≥ n_D`.  The proof transfers the entries of `𝒫₅` to those of `𝒫_𝒜` (`ent5_succ_eq_escEntry`)
and applies `escVisitsG_b` and `escDensityG` with `escBefore_planA`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The vertices visited by walk `m` of `𝒫₅` are those visited by `W_m` before `τ_m`. -/
theorem entVisited_subset (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
    {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ escIstar n (escJ n)) :
    entVisited (ent5 n tn u β' i hlog ν m) ⊆
      {x | ∃ s : ℝ, 0 ≤ s ∧ s ≤ escTauE n u β' hlog ν m ∧ escWalkE n u β' ν m s = x} := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [ent5_succ_eq_escEntry n tn u β' i hlog ν m' hm]
  rintro x ⟨a, ha, rfl⟩
  have hfin : (escEntry n u β' hlog ν m').len ≠ ⊤ := escEntry_len_ne_top m'
  have hjtfin : (escEntry n u β' hlog ν m').path.jt a ≠ ⊤ := ne_top_of_le_ne_top hfin ha
  set t : ℝ≥0 := ((escEntry n u β' hlog ν m').path.jt a).toNNReal with ht
  have hte : (t : ℝ≥0∞) = (escEntry n u β' hlog ν m').path.jt a := ENNReal.coe_toNNReal hjtfin
  have htle : (t : ℝ≥0∞) ≤ (escEntry n u β' hlog ν m').len := hte ▸ ha
  refine ⟨(t : ℝ), t.2, ?_, ?_⟩
  · have hτ : escTauE n u β' hlog ν (m' + 1) = (escEntry n u β' hlog ν m').len.toReal := by
      unfold escTauE; rw [ite_eq_left ⟨by omega, hm⟩]; simp
    rw [hτ]
    have := ENNReal.toReal_mono hfin htle
    simpa using this
  · rw [escWalkE_eq_envPath hν, Real.toNNReal_coe]
    show _ = (escEntry n u β' hlog ν m').path.fn t
    rw [escEntry_fn, min_eq_left htle]
    simp

theorem count_avoid (k : ℕ) : ∃ nD : ℕ, 4 ≤ nD ∧ ∀ {β : ℝ} [Fact (0 < β)] {n : ℕ} (tn : ℝ)
    (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β) {ν : Measure (CycS ℕ (k + 2) β)},
    CycGood ν → nD ≤ n → Real.exp 2 ≤ Real.log β → Real.log β ≤ (n : ℝ) ^ 17 / 7 →
    (n : ℝ) ^ 20 ≤ 2 ^ escJ n → (2 : ℝ) ^ escJ n < 2 * n ^ 20 → escIstar n (escJ n) ≤ n ^ 3 →
    16 * (escIstar n (escJ n) * escLambda n) ≤ 3 * 2 ^ escJ n → 1 ≤ i →
    i ≤ escIstar n (escJ n) → ∀ {L7 : ℝ}, max (Real.log β) 10 ≤ L7 + 1 →
    (∀ r : ℝ, L7 ≤ r → 3 ^ (k + 2) * (6 * 33 ^ (k + 2) * (r + 1) ^ 2 *
      Real.log (r + 1) ^ (2 * (k + 2) + 2)) ≤ r ^ (8 / 3 : ℝ) / 2) →
    ∀ r : ℝ, L7 ≤ r →
      (({y | y ∈ avoidSet (escPoint n (escJ n) u i) L7 (ent5 n tn u β' i hlog ν)
          (escIstar n (escJ n)) ∧ ‖y - escPoint n (escJ n) u i‖ ≤ r} : Set (EscV k)).ncard : ℝ)
        ≤ r ^ (8 / 3 : ℝ) := by
  classical
  obtain ⟨nD, hnD, H⟩ := escDensityG k
  refine ⟨nD, hnD, ?_⟩
  intro β _ n tn u β' i hlog ν hν hnD' hβe hlb hj1 hj2 hI hIlam hi1 hiI L7 hL7 hvis r hr
  set I := escIstar n (escJ n) with hIdef
  set j := escJ n with hjdef
  set p := escPoint n j u i with hp
  have hτ := escBefore_planA (n := n) (u := u) (b := β') (hlog := hlog) (ν := ν) hν
  obtain ⟨hinc, hcnt⟩ := H hτ hnD' hβe hlb hj1 hj2 hI hIlam hi1 hiI (escWalkE_zero hν)
    (escWalkE_nn hν)
  have hr0 : 0 ≤ r := by
    have h10 : (10 : ℝ) ≤ L7 + 1 := le_trans (le_max_right _ _) hL7
    linarith
  have hR : max (Real.log β) 10 ≤ r + 1 := le_trans hL7 (by linarith)
  set X : Set (EscV k) := {x | ∃ s : ℝ, 0 ≤ s ∧ s ≤ escTauE n u β' hlog ν i ∧
      escWalkE n u β' ν i s = x} ∩ {x | ‖x - escPoint n j u i‖ ≤ r + 1} with hX
  set Y : Set (EscV k) := escVneG n j β I u (escWalkE n u β' ν) (escBlockMinus j u)
    (escTauE n u β' hlog ν) i ∩ {y | ‖y - p‖ ≤ r} with hY
  have hXfin : X.Finite :=
    (ballFin p ⌊r + 1⌋₊).finite_toSet.subset fun x hx => mem_ballFin (by linarith) hx.2
  have hYfin : Y.Finite :=
    (ballFin p ⌊r⌋₊).finite_toSet.subset fun x hx => mem_ballFin hr0 hx.2
  have hsub : {y | y ∈ avoidSet p L7 (ent5 n tn u β' i hlog ν) I ∧ ‖y - p‖ ≤ r} ⊆
      {y | ∃ x ∈ X, ‖y - x‖ ≤ 1} ∪ Y := by
    rintro y ⟨⟨hy1, m, hm1, hmI, v, hv, hyv⟩, hyr⟩
    have hvW := entVisited_subset n tn u β' i hlog hν hm1 hmI hv
    by_cases hmi : m = i
    · subst hmi
      left
      refine ⟨v, ⟨hvW, ?_⟩, hyv⟩
      have := norm_sub_le_norm_sub_add_norm_sub v y p
      rw [norm_sub_rev v y] at this
      show ‖v - p‖ ≤ r + 1
      linarith
    · right
      refine ⟨⟨m, hm1, hmI, hmi, ?_⟩, hyr⟩
      obtain ⟨s, hs0, hsτ, hsW⟩ := hvW
      exact ⟨s, hs0, hsτ, by rw [hsW]; exact hyv⟩
  have hfinU : ({y | ∃ x ∈ X, ‖y - x‖ ≤ 1} ∪ Y).Finite :=
    (nbhd_finite X hXfin).union hYfin
  have h1 := Set.ncard_le_ncard hsub hfinU
  have h2 := (Set.ncard_union_le {y | ∃ x ∈ X, ‖y - x‖ ≤ 1} Y)
  have h3 := ncard_nbhd_le X hXfin
  have hXc : (X.ncard : ℝ) ≤ 6 * 33 ^ (k + 2) * (r + 1) ^ 2 *
      Real.log (r + 1) ^ (2 * (k + 2) + 2) :=
    escVisitsG_b hτ i hβe hR
  have hYc : (Y.ncard : ℝ) ≤ r ^ (8 / 3 : ℝ) / 2 := by
    by_cases hrn : (n : ℝ) ^ 17 / 7 ≤ r
    · exact hcnt r hrn
    · have hn4 : (4 : ℝ) ≤ n := by
        have : (4 : ℕ) ≤ n := le_trans hnD hnD'
        exact_mod_cast this
      have h17 : (84 : ℝ) ≤ (n : ℝ) ^ 17 := by
        have : (4 : ℝ) ^ 17 ≤ (n : ℝ) ^ 17 := pow_le_pow_left₀ (by norm_num) hn4 17
        have h2 : (4 : ℝ) ^ 17 = 17179869184 := by norm_num
        linarith
      have hYe : Y = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun y hy => ?_
        have h1' := hinc hy.1
        have h2' := hy.2
        simp only [mem_ofPred_eq] at h1' h2'
        push Not at hrn
        linarith
      rw [hYe]
      simp only [Set.ncard_empty, Nat.cast_zero]
      positivity
  have hA : ((({y | y ∈ avoidSet p L7 (ent5 n tn u β' i hlog ν) I ∧ ‖y - p‖ ≤ r} : Set (EscV k)).ncard
      : ℕ) : ℝ) ≤ 3 ^ (k + 2) * (X.ncard : ℝ) + (Y.ncard : ℝ) := by
    have := h1.trans (h2.trans (Nat.add_le_add_right h3 _))
    exact_mod_cast this
  have hv := hvis r hr
  calc _ ≤ 3 ^ (k + 2) * (X.ncard : ℝ) + (Y.ncard : ℝ) := hA
    _ ≤ 3 ^ (k + 2) * (6 * 33 ^ (k + 2) * (r + 1) ^ 2 * Real.log (r + 1) ^ (2 * (k + 2) + 2)) +
        r ^ (8 / 3 : ℝ) / 2 := by
        gcongr
    _ ≤ r ^ (8 / 3 : ℝ) / 2 + r ^ (8 / 3 : ℝ) / 2 := by linarith
    _ = r ^ (8 / 3 : ℝ) := by ring

end ElboimSly.Paper.Escape
