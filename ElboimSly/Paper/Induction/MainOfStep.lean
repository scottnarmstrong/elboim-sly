/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Induction.Base
public import ElboimSly.Paper.Step.StepFinal
public import Mathlib

/-!
# Theorem 3.2 from the induction base and the induction step (conditional form)

Induction step; ES22 Theorem 3.2; Bookkeeping of n_0; closing crefprop:ind-step.

* `ind_step_of`: induction step, which is the induction step word for word (`step_es7_of_inputs`).
* `ind_main_of_interface`: ES22 Theorem 3.2 by strong induction on `n ≥ n₀`, with
  `n₀ := max n₀^base (8d)` and `β₀ := max β₀^base β_step(n₀)`. Its conclusion is verbatim the frozen
  `ind_main`; the only hypotheses are `HeavyEscInterfaceAll` (§5 interface for
  Theorem 6.1, with `c₅` depending only on `d`) and `StepPp` (Lemma 7.8).
-/

@[expose] public section

namespace ElboimSly.Paper.Induction

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Step ElboimSly.Paper.Heavy

/-- Induction step, conditional on the named inputs. -/
theorem ind_step_of {d : ℕ} (hd5 : 5 ≤ d) (E : ℕ → HeavyEscConsts)
    (hI : HeavyEscInterfaceAll d E)
    {cPp : ℝ} {βPp : ℕ → ℝ} (hPp : StepPp d cPp βPp) :
    ∃ βstep : ℕ → ℝ, ∀ n₁ : ℕ, 8 * d ≤ n₁ → ∀ (β : ℝ) [Fact (0 < β)], βstep n₁ ≤ β →
      ∀ n : ℕ, 1 ≤ n → ∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 → β < indScale t₀ n →
        (∀ n' : ℕ, n₁ ≤ n' → n' < n → ∀ t' : ℝ, 1 < t' → t' ≤ 4 → IndHyp d β n' t') →
        IndHyp d β n t₀ :=
  step_es7_of_inputs hd5 E hI hPp

/-- ES22 Theorem 3.2, conditional on the named inputs (conclusion = frozen `ind_main`). -/
theorem ind_main_of_interface (d : ℕ) (hd : 5 ≤ d) (E : ℕ → HeavyEscConsts)
    (hI : HeavyEscInterfaceAll d E)
    {cPp : ℝ} {βPp : ℕ → ℝ} (hPp : StepPp d cPp βPp) :
    ∃ β₀ : ℝ, ∃ n₀ : ℕ, 10 ≤ n₀ ∧
      ∀ (β : ℝ) [Fact (0 < β)], β₀ ≤ β → ∀ n : ℕ, n₀ ≤ n → ∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 →
        IndHyp d β n t₀ := by
  obtain ⟨n₀b, β₀b, h10, hbase⟩ := ind_base d hd
  obtain ⟨βstep, hstep⟩ := ind_step_of hd E hI hPp
  refine ⟨max β₀b (βstep (max n₀b (8 * d))), max n₀b (8 * d), ?_, ?_⟩
  · exact h10.trans (le_max_left _ _)
  intro β _ hβ n hn t₀ ht1 ht4
  have hβb : β₀b ≤ β := (le_max_left _ _).trans hβ
  have hβs : βstep (max n₀b (8 * d)) ≤ β := (le_max_right _ _).trans hβ
  induction n using Nat.strong_induction_on generalizing t₀ with
  | _ n ih =>
    by_cases hle : indScale t₀ n ≤ β
    · exact hbase β hβb n ((le_max_left _ _).trans hn) t₀ ht1 ht4 hle
    · refine hstep _ (le_max_right _ _) β hβs n (by have := h10; have := le_max_left n₀b (8 * d); omega)
        t₀ ht1 ht4 (not_le.1 hle) ?_
      intro n' hn'1 hn'2 t' ht'1 ht'4
      exact ih n' hn'2 hn'1 t' ht'1 ht'4

end ElboimSly.Paper.Induction

end
