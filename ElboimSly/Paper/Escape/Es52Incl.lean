/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55Stmt
public import ElboimSly.Paper.Escape.Plan5Env
public import ElboimSly.Paper.Escape.Plan5Stop
public import ElboimSly.Paper.Escape.PointGeom
public import ElboimSly.Paper.Escape.Es53NumA
public import ElboimSly.Paper.Heavy.RegenCyclic
public import ElboimSly.Paper.Step.RegenMeas
public import Mathlib

/-!
# Prop 5.2, Step 1: the inclusion `𝒦(β') ∩ 𝒜_i ∩ Con_i ⊆ {Y_B = 1}`

The inclusion at ES22 §5 applied to the sets of `Es55Stmt`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The escape event of `Y_B` as a set of environments (with `CycGood`). -/
def escYSet (tn : ℝ) (n : ℕ) (u : Fin (k + 2) → ℤ) : Set (Measure (CycS ℕ (k + 2) β)) :=
  {ν | CycGood ν ∧ escXi (escWalk ν) (escBlock (escJ n) u) ≤ ENNReal.ofReal tn ∧
    EscEvent n (escJ n) (escWalk ν) (escXi (escWalk ν) (escBlock (escJ n) u)).toReal}

/-- On `[0, treg]` the regenerated walk is the first piece. -/
theorem escWalk_eq_first {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) {x : ℝ} (hx : 0 ≤ x)
    (hle : ENNReal.ofReal x ≤ cycTreg (copyEnv ν 0)) :
    escWalk ν x = cycWalk (cycSlice 0 ν) 0 0 x := by
  have hg : ∀ j, Good (copyEnv ν j) := fun j => by
    rw [copyEnv_eq_cycSlice]; exact hν j
  have h := Heavy.regenWalk_eq_piece (ν := fun i => copyEnv ν i) hg (j := 0)
    (by simp [regenSigma]) (x := x) (by simp [regenSigma]; exact hx)
    (by
      have : regenSigma (fun i => copyEnv ν i) 1 = cycTreg (copyEnv ν 0) := by
        simp [regenSigma]
      rw [this]; exact hle)
  unfold escWalk
  rw [h]
  simp [regenSigma, copyEnv_eq_cycSlice]


theorem escBlockMinus_subset_block {j : ℕ} {u x : Fin (k + 2) → ℤ} (h : x ∈ escBlockMinus j u) :
    x ∈ escBlock j u := by
  intro c
  by_cases hc : c = 0
  · subst hc
    have h0 := h.1
    have : (2 : ℤ) ^ (j - 1) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    exact ⟨h0.1, by omega⟩
  · exact h.2 c hc

theorem norm_sub_le_of_mem_block {j : ℕ} {u x y : Fin (k + 2) → ℤ} (hx : x ∈ escBlock j u)
    (hy : y ∈ escBlock j u) : ‖x - y‖ ≤ 2 ^ j := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro c
  rw [Int.norm_eq_abs]
  have h1 := hx c
  have h2 := hy c
  have : |x c - y c| ≤ 2 ^ j := by
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  simp only [Pi.sub_apply]
  exact_mod_cast this

/-- **the inclusion at ES22 §5 for the sets of `Es55Stmt`**: `𝒦(β') ∩ 𝒜_i ∩ Con_i ⊆ {Y_B = 1}`. -/
theorem escX_subset_Y {tn : ℝ} {n : ℕ} {u : Fin (k + 2) → ℤ} {β' i : ℕ}
    (hlog : 1 < Real.log β) (hn : 2000 ≤ n) (hlb : Real.log β ≤ (n : ℝ) ^ 40)
    (hi1 : 1 ≤ i) (hiI : i ≤ escIstar n (escJ n)) {ν : Measure (CycS ℕ (k + 2) β)}
    (hK : ν ∈ escKSet β tn n β' u) (hA : ν ∈ escASet n u β' hlog i)
    (hC : ν ∈ escConSet β n u i) : ν ∈ escYSet (β := β) tn n u := by
  obtain ⟨hν, hξle, hξtr, hWξ, hphase⟩ := hK
  obtain ⟨-, hAlen⟩ := hA
  obtain ⟨-, hξtop, hlt, hcon⟩ := hC
  refine ⟨hν, hξle, ?_⟩
  have hβ : 0 < β := Fact.out
  set ξ := escXi (escWalk ν) (escBlock (escJ n) u) with hξ
  set t' := cycFloor β (ξ.toReal + 4 ^ escJ n) with ht'
  have hnR : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  have hj1' : (n : ℝ) ^ 20 ≤ 2 ^ escJ n := by exact_mod_cast le_two_pow_escJ n
  have hj2 : (2 : ℝ) ^ escJ n < 2 * n ^ 20 := by
    have := two_pow_escJ_lt (n := n) (by omega)
    exact_mod_cast this
  have hj2' : 2 ≤ escJ n := by
    by_contra h
    push Not at h
    have : (2 : ℝ) ^ escJ n ≤ 2 := by
      interval_cases (escJ n) <;> norm_num
    have h20 : (2000 : ℝ) ^ 20 ≤ (n : ℝ) ^ 20 := by gcongr
    nlinarith [show (2 : ℝ) ≤ 2000 ^ 20 by norm_num]
  have hξ0 : 0 ≤ ξ.toReal := ENNReal.toReal_nonneg
  have hξne : ξ ≠ ⊤ := hξtop
  have ht'0 : 0 ≤ t' := (cycFloor_mem hβ (by positivity)).1
  have hξt' : ξ.toReal ≤ t' := by
    have := lt_cycFloor_add_one (β := β) (x := ξ.toReal + 4 ^ escJ n) hβ
    have h1 : (1 : ℝ) ≤ 4 ^ escJ n := one_le_pow₀ (by norm_num)
    linarith
  have hWξ' : cycWalk (cycSlice 0 ν) 0 0 ξ.toReal ∈ escBlockMinus (escJ n) u := by
    rw [← escWalk_eq_first hν hξ0 (by rw [ENNReal.ofReal_toReal hξne]; exact hξtr.le)]
    exact hWξ
  have hcon' : cycWalk (cycSlice 0 ν) 0 0 t' = escPoint n (escJ n) u i := by
    rw [← escWalk_eq_first hν ht'0 hlt.le]; exact hcon
  have hlen : (planA n β u β' hlog).stopLen (i - 1)
      ((planA n β u β' hlog).ideal (envRuleA n u β' hlog ν) (i - 1))
      (envPath ν (0, escPoint n (escJ n) u i, (β' : ℝ), true)) = (4 : ℝ≥0∞) ^ n := by
    have := escEntry_len (n := n) (u := u) (b := β') (hlog := hlog) (ν := ν) (i - 1)
    rw [Nat.sub_add_cancel hi1] at this
    rw [← this]; exact hAlen
  have hR := planA_ruleAt (k := k) n u β' hlog (i - 1)
  have hlen' : (planA n β u β' hlog).stopLen (i - 1)
      ((planA n β u β' hlog).ideal (envRuleA n u β' hlog ν) (i - 1))
      (envPath ν (0, escPoint n (escJ n) u (i - 1 + 1), (β' : ℝ), true)) =
        (4 : ℝ≥0∞) ^ (escRP n β u 0).n := by
    rw [Nat.sub_add_cancel hi1]; exact hlen
  obtain ⟨H1, H2, H6⟩ := inclusion_hyps_of_stopLen hR hlog _ _ hlen'
  have hfn : (envPath ν (0, escPoint n (escJ n) u i, (β' : ℝ), true)).1.fn =
      envFn ν (0, escPoint n (escJ n) u i, (β' : ℝ), true) :=
    (envPath_len (δ := (0, escPoint n (escJ n) u i, (β' : ℝ), true)) (hν _)).2
  have hfn' : (envPath ν (0, escPoint n (escJ n) u (i - 1 + 1), (β' : ℝ), true)).1.fn =
      envFn ν (0, escPoint n (escJ n) u i, (β' : ℝ), true) := by
    rw [Nat.sub_add_cancel hi1]; exact hfn
  have hPi : (escRP n β u 0).P (i - 1 + 1) = escPoint n (escJ n) u i := by
    simp [escRP, Nat.sub_add_cancel hi1]
  rw [hPi] at H2
  rw [hfn'] at H1 H2 H6
  have hIlam := escIstar_spec n (escJ n)
  have hpB_mem : escPoint n (escJ n) u i ∈ escBlock (escJ n) u := by
    refine escPoint_mem_block hj2' i ?_
    have : (i : ℝ) * escLambda n ≤ escIstar n (escJ n) * escLambda n := by gcongr
    have h2 : (16 : ℝ) * (escIstar n (escJ n) * escLambda n) ≤ 3 * 2 ^ escJ n := by
      exact_mod_cast hIlam
    have h3 : (0 : ℝ) < 2 ^ escJ n := by positivity
    nlinarith
  have hpB : ‖cycWalk (cycSlice 0 ν) 0 0 ξ.toReal - escPoint n (escJ n) u i‖ ≤ 2 ^ escJ n :=
    norm_sub_le_of_mem_block (escBlockMinus_subset_block hWξ') hpB_mem
  have hlogn : Real.log β ≤ (n : ℝ) ^ 40 := hlb
  have hinc := es5_inclusion_env (ν := ν) (hν 0) (n := n) (j := escJ n) hn hj1' hj2 hlogn
    (ξ := ξ.toReal) hξ0 (p := escPoint n (escJ n) u i) (β' := (β' : ℝ))
    (Bm := escBlockMinus (escJ n) u) hphase hcon'
    (by rw [← ht', ← copyEnv_eq_cycSlice]; exact hlt)
    (fun t ht ht' => H1 t ht.le ht')
    (fun t ht ht' hl => H2 t ht.le ht' hl)
    (fun t ht ht' => H6 t ht ht') hWξ' hpB
  obtain ⟨hA1, -, hEsc⟩ := hinc
  rw [← copyEnv_eq_cycSlice] at hA1
  intro s hs1 hs2
  have hs0 : 0 ≤ s := le_trans (by positivity) hs1
  have e1 : ENNReal.ofReal (ξ.toReal + s) ≤ cycTreg (copyEnv ν 0) := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (by rw [← ht'] at hA1; exact hA1)
    linarith
  have e0 : ENNReal.ofReal ξ.toReal ≤ cycTreg (copyEnv ν 0) :=
    le_trans (ENNReal.ofReal_le_ofReal (by linarith)) e1
  rw [escWalk_eq_first hν (by linarith) e1, escWalk_eq_first hν hξ0 e0]
  exact hEsc s hs1 hs2

end ElboimSly.Paper.Escape
