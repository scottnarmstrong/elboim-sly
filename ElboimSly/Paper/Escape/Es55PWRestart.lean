/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es53Transfer
public import ElboimSly.Paper.Escape.EscapeTime
public import ElboimSly.Paper.Step.RegenMeas
public import ElboimSly.Foundations.Cyclic.CycClosing
public import Mathlib

/-!
# Step 1 of ES22 Lemma 5.5: restart at `ξ_B` and the closing time

ES22 Lemma 5.5, Step 1 ("restart at `ξ_B`"; "`t' < t_reg`").

* `pw_restart`: `W^{ν}_{0,0}(ξ + s) = W^{ν}_{v, ξ}(s)` for `v = W^ν_{0,0}(ξ)`, i.e. the walk
  `envWalk ν (0, v, ξ, +1)`;
* `pw_lt_cycTreg`: the closing time of a good slice exceeds `T` if no cyclic integer `≤ T` is a zero;
* `PWClose`: the output of the closing argument (the forward trajectory from `w` at a time just
  before `τ = ξ + t_*` reaches `p_i` at `t'` through a set `S ∌ 0`);
* `pw_conclude`: from the walk before `τ` (all its cyclic-integer values are nonzero and it sits at
  `w` just before `τ`) and `PWClose`, `t' < t_reg` and `W(t') = p_i`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Restart of the first-piece walk at the time `ξ ≥ 0`. -/
theorem pw_restart {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) {ξ : ℝ} (hξ : 0 ≤ ξ)
    {v : Fin (k + 2) → ℤ} (hv : ElboimSly.cycWalk (cycSlice 0 ν) 0 0 ξ = v) (s : ℝ≥0) :
    ElboimSly.cycWalk (cycSlice 0 ν) 0 0 (ξ + s) = envWalk ν ((0 : ℕ), v, ξ, true) s := by
  have hμ : Good (cycSlice 0 ν) := hν 0
  rw [envWalk_eq_cycWalk hν]
  simp only [envMeasure, CycData.sgn, CycData.phase, CycData.start, CycData.copy, CycData.fwd,
    ite_true, one_mul]
  rw [cycWalk_of_nonneg hμ v ξ (NNReal.coe_nonneg s), cycWalk_of_nonneg hμ 0 0 (by positivity)]
  rw [← hv, cycWalk_of_nonneg hμ 0 0 hξ]
  simp only [zero_add]
  exact fwdTraj_restart hμ 0 hξ (by linarith [NNReal.coe_nonneg s])

/-- The closing time exceeds `T` if no cyclic integer `≤ T` is a zero of the walk. -/
theorem pw_lt_cycTreg {μ : Measure (RingSpace (k + 2) β)} (_hμ : Good μ) {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ m : ℕ, 1 ≤ m → (m : ℝ) * β ≤ T → ElboimSly.cycWalk μ 0 0 ((m : ℝ) * β) ≠ 0) :
    ENNReal.ofReal T < ElboimSly.cycTreg μ := by
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨n, hn, h0, he⟩ := exists_cycTreg_eq (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  rw [he] at hle
  have hβ : 0 < β := Fact.out
  exact h n hn ((ENNReal.ofReal_le_ofReal_iff hT).1 hle) h0

/-- Before the closing time the regenerated walk is the first-piece walk. -/
theorem pw_escWalk_eq {ν : Measure (CycS ℕ (k + 2) β)} {t : ℝ} (ht : 0 ≤ t)
    (hlt : ENNReal.ofReal t < ElboimSly.cycTreg (copyEnv ν 0)) :
    escWalk ν t = ElboimSly.cycWalk (cycSlice 0 ν) 0 0 t := by
  have h := regenWalk_of_lt_treg (fun i => copyEnv ν i) (u := t.toNNReal)
    (by simpa [ENNReal.ofReal] using hlt)
  unfold escWalk
  rw [Real.coe_toNNReal _ ht] at h
  rw [h, copyEnv_eq_cycSlice]

/-- The output of the closing argument: the forward trajectory from `w`, started at a time `τ'`
just before `τ`, reaches `pi` at `tp` and stays in `S` on `[τ, tp)`. -/
def PWClose {μ : Measure (RingSpace (k + 2) β)} (hμ : Good μ) (S : Set (Fin (k + 2) → ℤ))
    (w pi : Fin (k + 2) → ℤ) (tp τ : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ τ' : ℝ, τ - ε < τ' → τ' < τ →
    fwdTraj hμ w τ' tp = pi ∧ ∀ x : ℝ, τ ≤ x → x < tp → fwdTraj hμ w τ' x ∈ S

/-- **Conclusion of Step 1.** -/
theorem pw_conclude {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) {ξ τ tp : ℝ}
    (hξ : 0 ≤ ξ) (hτtp : τ ≤ tp) {w pi : Fin (k + 2) → ℤ}
    {S : Set (Fin (k + 2) → ℤ)} (h0S : (0 : Fin (k + 2) → ℤ) ∉ S) (hpi : pi ∈ S)
    (hξt : ENNReal.ofReal ξ < ElboimSly.cycTreg (cycSlice 0 ν))
    (hnz : ∀ m : ℕ, 1 ≤ m → ξ < (m : ℝ) * β → (m : ℝ) * β < τ →
      ElboimSly.cycWalk (cycSlice 0 ν) 0 0 ((m : ℝ) * β) ≠ 0)
    (hlim : ∃ l : ℝ, 0 ≤ l ∧ l < τ - ξ ∧ ∀ s : ℝ, l < s → s < τ - ξ →
      ElboimSly.cycWalk (cycSlice 0 ν) 0 0 (ξ + s) = w)
    (hcl : PWClose (hν 0) S w pi tp τ) :
    ENNReal.ofReal tp < ElboimSly.cycTreg (copyEnv ν 0) ∧
      escWalk ν tp = pi := by
  have hμ : Good (cycSlice 0 ν) := hν 0
  have hβ : 0 < β := Fact.out
  obtain ⟨ε, hε, hc⟩ := hcl
  obtain ⟨l, hl0, hl, hlw⟩ := hlim
  set τ' : ℝ := max (τ - ε / 2) (ξ + (l + (τ - ξ)) / 2) with hτ'
  have hτ1 : τ - ε < τ' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hτ2 : τ' < τ := max_lt (by linarith) (by linarith)
  have hτ3 : ξ + l < τ' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hτ0 : 0 ≤ τ' := by linarith
  have hWτ : ElboimSly.cycWalk (cycSlice 0 ν) 0 0 τ' = w := by
    have := hlw (τ' - ξ) (by linarith) (by linarith)
    rwa [add_sub_cancel] at this
  have hrest : ∀ x : ℝ, τ' ≤ x → ElboimSly.cycWalk (cycSlice 0 ν) 0 0 x = fwdTraj hμ w τ' x := by
    intro x hx
    have h1 := fwdTraj_restart hμ 0 (a := 0) (c := τ') hτ0 (t := x) hx
    rw [cycWalk_of_nonneg hμ 0 0 (by linarith), zero_add]
    rw [cycWalk_of_nonneg hμ 0 0 hτ0, zero_add] at hWτ
    rw [hWτ] at h1
    exact h1
  obtain ⟨hend, hmid⟩ := hc τ' hτ1 hτ2
  have hWtp : ElboimSly.cycWalk (cycSlice 0 ν) 0 0 tp = pi := by
    rw [hrest tp (by linarith), hend]
  have hlt : ENNReal.ofReal tp < ElboimSly.cycTreg (cycSlice 0 ν) := by
    refine pw_lt_cycTreg hμ (by linarith) fun m hm1 hmT h0 => ?_
    by_cases hmξ : (m : ℝ) * β ≤ ξ
    · have := cycTreg_le hm1 h0
      exact absurd (lt_of_le_of_lt this (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hmξ) hξt))
        (lt_irrefl _)
    push Not at hmξ
    by_cases hmτ : (m : ℝ) * β < τ
    · exact hnz m hm1 hmξ hmτ h0
    push Not at hmτ
    rcases hmT.lt_or_eq with hlt' | heq
    · rw [hrest _ (by linarith)] at h0
      exact h0S (h0 ▸ hmid _ hmτ hlt')
    · rw [heq, hWtp] at h0
      exact h0S (h0 ▸ hpi)
  refine ⟨by rwa [copyEnv_eq_cycSlice], ?_⟩
  rw [pw_escWalk_eq (by linarith) (by rwa [copyEnv_eq_cycSlice]), hWtp]

end ElboimSly.Paper.Escape
