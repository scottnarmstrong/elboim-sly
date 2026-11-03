/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es53Core
public import ElboimSly.Paper.Escape.Es53Transfer
public import ElboimSly.Paper.Escape.Es53Meas
public import Mathlib

/-!
# On `𝒥`, the fresh walk agrees with `W_i` on `[0, 4^n]` and `𝒜_i` holds

ES22 Lemma 5.3, "On `𝒥`, `τ_i = 4^n` and `W_i = W'_i` on `[0,4^n]`".  The pathwise step:
if the cyclic walk `Ỹ` of a good fresh environment satisfies `𝒥` (with the set `A = {0} ∪ A'`) and the
coupling `(b)` of plan-level coupling after a stopping time holds, then `Ỹ = W_i` on `[0, 4^n]` and `τ_i = 4^n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n : ℕ} {u : Fin (k + 2) → ℤ} {b : ℕ}
  {hlog : 1 < Real.log β}

theorem envWalk_eq_fn {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν)
    (δ : CycData ℕ (k + 2)) : envWalk ν δ = (envPath ν δ).1.fn := by
  funext s
  unfold envWalk
  rw [ite_eq_left hν]
  exact (congrFun (envPath_len (hν δ.copy)).2 s).symm

theorem step_A (ν ν' : Measure (CycS ℕ (k + 2) β)) (hν : CycGood ν) (hν' : CycGood ν')
    {m : ℕ} (hm : m < escIstar n (escJ n))
    {m₁ : ℕ} (hm8 : 8 ≤ m₁) (hm1n : m₁ ≤ n) (hm1a : (m₁ : ℝ) ≤ Real.log (Real.log β))
    (hm1b : (4 : ℝ) ^ m₁ ≤ Real.log β) (hβ : Real.exp 2 ≤ Real.log β) (hn : 2 ≤ n)
    (hj1 : (n : ℝ) ^ 20 ≤ 2 ^ escJ n)
    (hIlam : 16 * (escIstar n (escJ n) * escLambda n) ≤ 3 * 2 ^ escJ n)
    (hjn : (escJ n : ℝ) * 4 ^ escJ n ≤ 4 ^ n)
    (δ : CycData ℕ (k + 2)) (hδ : δ = (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true))
    (hcouple : ∀ r : ℝ≥0,
      Disjoint (CycEntry.region β ((δ, (envPath ν' δ).cut (r : ℝ≥0∞)) : CycEntry ℕ (k + 2)))
        ((CycRec.trunc (((planA n β u b hlog).envFinal ν).cum m).toNNReal
          ((planA n β u b hlog).envFinal ν)).region β) →
      ∀ s : ℝ≥0, s ≤ r → envWalk ν' δ s = envWalk ν δ s)
    (hJ : EsJ n m₁ (escJ n) (escIstar n (escJ n)) u (m + 1)
      ({0} ∪ escVisNbr n u b hlog ν m) (fun q => envWalk ν' δ q)) :
    (escEntry n u b hlog ν m).len = (4 : ℝ≥0∞) ^ n := by
  set pT := envPath ν δ with hpT
  set pF := envPath ν' δ with hpF
  set A : Set (Fin (k + 2) → ℤ) := {0} ∪ escVisNbr n u b hlog ν m with hA
  have hyF : envWalk ν' δ = pF.1.fn := envWalk_eq_fn hν' δ
  have hyT : envWalk ν δ = pT.1.fn := envWalk_eq_fn hν δ
  rw [hyF] at hJ hcouple
  rw [hyT] at hcouple
  have hRC : IsRCPath pF.1.fn := fun t => pF.1.rc t
  have h4 : (0 : ℝ) ≤ 4 ^ n := by positivity
  have hCr := forall_of_not_exists_qSet hRC (bot_le : (0 : ℝ≥0) ≤ _)
    (P := fun v => v ∈ A) hJ.2.2.1
  have hdisj := disjoint_region ν hm δ pF (tn ((4 : ℝ) ^ n))
    (fun s hs hmem => hCr s bot_le hs (subset_union_right hmem))
  have hag := hcouple _ hdisj
  have hJT : EsJ n m₁ (escJ n) (escIstar n (escJ n)) u (m + 1) A pT.1.fn := by
    refine (EsJ_congr hjn (y := pF.1.fn) (y' := pT.1.fn) ?_).1 hJ
    intro q hq
    exact hag q (le_tn_of_coe_le h4 hq)
  subst hδ
  have hstop := core_stopLen ν hm hm8 hm1n hm1a hm1b hβ hn hj1 hIlam hjn
    (A := A) (by simp [hA]) (subset_union_right) hJT.1 hJT.2.1 hJT.2.2.1 hJT.2.2.2.1 hJT.2.2.2.2
  rw [escEntry_len]
  exact hstop

end ElboimSly.Paper.Escape
